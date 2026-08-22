//! **Cultivation at the transport-atlas grain: the exposure's structured residual, and the delta
//! the declared return law derives from it.**
//!
//! Deed P3 of `blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md` §8.
//!
//! # Why this owner exists, stated as the absent relation rather than as a new faculty
//!
//! [`crate::holonic_training::TrainingEcology`] already owns cultivation, and owns it in the shape
//! this module must keep: `consequence_complex` → `derive_templates` → **`predict` before any
//! mutation** → a four-state [`ConsequenceRelation`] in which a contradicting later return is
//! `OpenResidual` rather than "incorrect", and a proposal that carries only the caused difference
//! and is refused intact if the body moved under it. Nothing here rivals that. What it cannot
//! carry is the **grain**: its consequence complex is built over the octets of one consequence and
//! `derive_templates` enumerates every complete route through that complex, which is exponential in
//! the extent — its own `maximum_templates_per_occurrence` exists to refuse before truncating.
//! `the_octet_route_population_is_exponential_so_the_atlas_grain_is_a_different_owner` measures it
//! rather than asserting it.
//!
//! So the absent relation is exactly one: **the structured residual of an exposure against a
//! standing transport atlas, and the delta the declared return law derives from that residual.**
//! Everything else is composed — [`ConsequenceRelation`] is imported, not restated; the transport
//! is [`ExactSuffixEcology::absorb_returning_lineage`]; the prediction is the rest's own declared
//! walk, future and depth laws.
//!
//! # The return law
//!
//! ```text
//!  1. PREDICT, mutating nothing. Carry the material through the standing atlas under the rest's
//!     own WALK law. At each position record the class stood in, the whole continuation family that
//!     class offers, how far up the suffix ladder the carried germ is first offered (the DEPTH
//!     law), and the four-state relation between the offered family and what the material carried.
//!     That plural record is the STRUCTURED RESIDUAL.
//!
//!  2. DEPOSIT. The material is absorbed, and the transport returns its forward lineage: per
//!     position, the class stood in, the class landed in, and every class founded, transition
//!     added and link rebased, in the order deposited.
//!
//!  3. DERIVE.
//!       structural face — every founded class, founded transition and rebased link is licensed by
//!                         a named position of the residual, and carries it as its cause;
//!       standings face  — LINEAR, and this is where the metric is read. The R1 ladder face is
//!                             y_p = sum over the suffix ladder of the class occurrence p landed in
//!                                   of that class's standing,
//!                         so the exact differential of the R1 faces with respect to the standings
//!                         is the 0/1 deposit incidence A, and the cultivation return is the
//!                         covector
//!                             dq = G_X^-1 A^T G_Y r
//!                         through the DECLARED metrics. The committed standing of every class is
//!                         its carried part plus that image, and nothing else:
//!                             standing(s) = carried(s) + (G_X^-1 A^T G_Y r)_s
//!                             carried(s)  = standing_before(s)          a class that stood
//!                                         = standing_before(origin)     a split, which inherits
//!                                         = 0                           a class the material carried
//!
//!  4. COMMIT. The delta is applied to the predecessor container by replay. The committed container
//!     must equal the container the transport itself emits, octet for octet.
//! ```
//!
//! **The metric is read and not decorated.** `G_Y` is a declared receiver metric over the residual
//! species — a rational weight per [`ConsequenceRelation`] — and `G_X` a declared class-side metric.
//! At the identity declaration the image is the atlas's own occurrence fold, which is the control.
//! At any other declaration the committed increments move, and where the image leaves the integer
//! carrier the law refuses by name rather than rounding.
//!
//! **No factorized overlay is used.** A counting atlas has no dense transport to factor: its
//! transport is a sparse partial function and its standings are occurrence counts. No rank is
//! declared, chosen or truncated anywhere in this module, so no `RankDerivationReceipt` is owed.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::athena::{emit_integers, IntegerDtype, IntegerTensor, TreeChart};
use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;

use crate::causal_language::{fiber_bytes, CausalLanguageError};
use crate::holonic_training::ConsequenceRelation;
use crate::resonance_ecology::ResonanceGerm;
use crate::suffix_ecology::{AbsorbLineage, ExactSuffixEcology, ExtendEvent};

/// The schema the P0 rest declares and this cultivation preserves.
pub const REST_SCHEMA: &str = "holonic-engine.athena-native-rest.v1";

/// The container region carrying [`AthenaRest::extent`]. Optional, and absent from P0's rest.
pub const EXTENT_REGION: &str = "athena.class.extent";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CultivationRefusal {
    /// A rest the reader cannot resolve as the declared container.
    Container(String),
    /// The declared metric returned a deposit outside the integer carrier the rest holds.
    NonIntegralDeposit { class: u32, image: String },
    /// The declared metric returned a negative deposit; a standing is an occupancy.
    NegativeDeposit { class: u32, image: String },
    /// A declared metric that is not invertible over the exact rationals.
    SingularMetric(String),
    /// A delta row naming a class or germ the body it is applied to does not carry.
    Unlicensed(String),
    /// The material could not be read as germs.
    Material(String),
}

impl core::fmt::Display for CultivationRefusal {
    fn fmt(&self, form: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Container(why) => write!(form, "container: {why}"),
            Self::NonIntegralDeposit { class, image } => write!(
                form,
                "the declared metric returns {image} at class {class}, which the integer carrier \
                 does not hold — the law refuses rather than rounding"
            ),
            Self::NegativeDeposit { class, image } => write!(
                form,
                "the declared metric returns {image} at class {class}; a standing is an occupancy \
                 and cannot be negative"
            ),
            Self::SingularMetric(why) => write!(form, "the declared metric is singular: {why}"),
            Self::Unlicensed(why) => write!(form, "unlicensed delta row: {why}"),
            Self::Material(why) => write!(form, "material: {why}"),
        }
    }
}

impl From<CausalLanguageError> for CultivationRefusal {
    fn from(error: CausalLanguageError) -> Self {
        Self::Material(format!("{error:?}"))
    }
}

// -------------------------------------------------------------------------------------------
// the rest, as this owner holds it
// -------------------------------------------------------------------------------------------

/// **The native rest's own arrays.** The P0 container's exact populations, nothing added.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AthenaRest {
    pub indptr: Vec<u64>,
    pub germ: Vec<u64>,
    pub target: Vec<u64>,
    pub standing: Vec<u64>,
    pub suffix: Vec<u64>,
    /// **The longest substring each class represents** — the transport's own `class_extent`.
    ///
    /// **Empty means the container does not carry it**, which is the P0 rest's state: P0 emitted
    /// the transport, the standings, the suffix links and the vocabulary, and every one of the
    /// three declared laws reads only those, so a rest without this array *conducts* perfectly.
    /// It cannot be **deposited into** from itself: [`crate::suffix_ecology::ExactSuffixEcology`]
    /// finds the class the concatenation ends in as the unique class of greatest extent, decides a
    /// split by comparing extents, and orders the occurrence fold by extent, so an extent that is
    /// absent or guessed is three wrong answers rather than one. Measured on the committed P0 rest
    /// 2026-08-20: 23 of its 59,698 classes are unreachable from the root over the germ transport
    /// alone — the classes whose longest string crosses a path boundary — so the array is not
    /// derivable from what P0 carried and is carried here instead.
    ///
    /// Emitting it is opt-in ([`crate::phoenix_rest::seal`]), so every standing container's octets
    /// are unmoved.
    pub extent: Vec<u64>,
    pub vocabulary: Vec<String>,
    pub height: u32,
    pub metadata: BTreeMap<String, String>,
}

impl AthenaRest {
    pub fn classes(&self) -> usize {
        self.standing.len()
    }

    pub fn transitions(&self) -> usize {
        self.germ.len()
    }

    /// The transport row of one class: `(germ index, class reached)`, sorted by germ index because
    /// the card searches it that way.
    pub fn row(&self, class: u32) -> &[u64] {
        let at = class as usize;
        &self.germ[self.indptr[at] as usize..self.indptr[at + 1] as usize]
    }

    fn row_span(&self, class: u32) -> (usize, usize) {
        let at = class as usize;
        (self.indptr[at] as usize, self.indptr[at + 1] as usize)
    }

    /// The class this class reaches on this germ index, or `None` where it offers none.
    pub fn reaches(&self, class: u32, germ: u64) -> Option<u32> {
        let (start, end) = self.row_span(class);
        self.germ[start..end]
            .binary_search(&germ)
            .ok()
            .map(|at| self.target[start + at] as u32)
    }

    /// The whole continuation family this class offers, by germ index.
    pub fn offered(&self, class: u32) -> &[u64] {
        self.row(class)
    }

    /// The suffix ladder of a class, finest first, ending at the root. The material's own scale
    /// ladder, read off the rest's `athena.class.suffix`.
    pub fn ladder(&self, class: u32) -> Vec<u32> {
        let mut ladder = vec![class];
        let mut at = class;
        while at != 0 {
            let parent = self.suffix[at as usize] as u32;
            if parent == at {
                break;
            }
            at = parent;
            ladder.push(at);
        }
        ladder
    }

    /// Read the rest from an emitted container.
    pub fn read_container(octets: &[u8]) -> Result<Self, CultivationRefusal> {
        let refuse = |why: &str| CultivationRefusal::Container(why.to_owned());
        if octets.len() < 8 {
            return Err(refuse("shorter than its own header length"));
        }
        let header_len = u64::from_le_bytes(octets[..8].try_into().unwrap()) as usize;
        let header = core::str::from_utf8(
            octets
                .get(8..8 + header_len)
                .ok_or_else(|| refuse("the header runs past the container"))?,
        )
        .map_err(|_| refuse("the header is not UTF-8"))?;
        let payload = &octets[8 + header_len..];
        let metadata = read_metadata(header)?;
        let region =
            |name: &str| -> Result<(usize, usize), CultivationRefusal> {
                let key = format!("\"{name}\":");
                let at = header
                    .find(&key)
                    .ok_or_else(|| CultivationRefusal::Container(format!("no {name}")))?;
                let rest = &header[at + key.len()..];
                let marker = "\"data_offsets\":[";
                let start = rest.find(marker).ok_or_else(|| {
                    CultivationRefusal::Container(format!("{name} has no offsets"))
                })? + marker.len();
                let end = rest[start..].find(']').ok_or_else(|| {
                    CultivationRefusal::Container(format!("{name} offsets unclosed"))
                })? + start;
                let mut parts = rest[start..end].split(',');
                let read = |part: Option<&str>| -> Result<usize, CultivationRefusal> {
                    part.and_then(|value| value.trim().parse::<usize>().ok())
                        .ok_or_else(|| CultivationRefusal::Container(format!("{name} offset")))
                };
                Ok((read(parts.next())?, read(parts.next())?))
            };
        let words = |name: &str| -> Result<Vec<u64>, CultivationRefusal> {
            let (start, end) = region(name)?;
            let slice = payload
                .get(start..end)
                .ok_or_else(|| CultivationRefusal::Container(format!("{name} past the payload")))?;
            Ok(slice
                .chunks_exact(4)
                .map(|word| u64::from(u32::from_le_bytes([word[0], word[1], word[2], word[3]])))
                .collect())
        };
        let half_words = |name: &str| -> Result<Vec<u64>, CultivationRefusal> {
            let (start, end) = region(name)?;
            let slice = payload
                .get(start..end)
                .ok_or_else(|| CultivationRefusal::Container(format!("{name} past the payload")))?;
            Ok(slice
                .chunks_exact(2)
                .map(|word| u64::from(u16::from_le_bytes([word[0], word[1]])))
                .collect())
        };
        let octets_of_vocabulary = half_words("athena.vocabulary.octets")?;
        let offsets = words("athena.vocabulary.offsets")?;
        let mut vocabulary = Vec::with_capacity(offsets.len().saturating_sub(1));
        for pair in offsets.windows(2) {
            let bytes: Vec<u8> = octets_of_vocabulary[pair[0] as usize..pair[1] as usize]
                .iter()
                .map(|word| *word as u8)
                .collect();
            vocabulary.push(
                String::from_utf8(bytes).map_err(|_| refuse("a vocabulary germ is not UTF-8"))?,
            );
        }
        let architecture = words("athena.architecture")?;
        // The extent region is optional and its absence is a fact about the container rather than
        // a fault: P0 emitted no extents and this reader must still mount P0's rest.
        let extent = if header.contains(&format!("\"{EXTENT_REGION}\":")) {
            words(EXTENT_REGION)?
        } else {
            Vec::new()
        };
        Ok(Self {
            indptr: words("athena.transport.indptr")?,
            germ: words("athena.transport.germ")?,
            target: words("athena.transport.target")?,
            standing: words("athena.class.standing")?,
            suffix: words("athena.class.suffix")?,
            extent,
            vocabulary,
            height: u32::try_from(architecture[0]).map_err(|_| refuse("architecture height"))?,
            metadata,
        })
    }

    /// Emit the container. **The same writer the P0 rest builder uses**, and the driver checks that
    /// it reproduces the committed P0 artifact octet for octet before anything is cultivated.
    pub fn write_container(&self) -> Result<Vec<u8>, CultivationRefusal> {
        let mut vocabulary_octets: Vec<u64> = Vec::new();
        let mut vocabulary_offsets: Vec<u64> = vec![0];
        for token in &self.vocabulary {
            vocabulary_octets.extend(token.as_bytes().iter().map(|octet| u64::from(*octet)));
            vocabulary_offsets.push(vocabulary_octets.len() as u64);
        }
        let emit = |name: &str,
                    values: &[u64],
                    dtype: IntegerDtype|
         -> Result<IntegerTensor, CultivationRefusal> {
            emit_integers(name, values, 1, dtype)
                .map_err(|error| CultivationRefusal::Container(format!("{name}: {error:?}")))
        };
        let mut tensors = vec![
            emit("athena.transport.indptr", &self.indptr, IntegerDtype::U32)?,
            emit("athena.transport.germ", &self.germ, IntegerDtype::U32)?,
            emit("athena.transport.target", &self.target, IntegerDtype::U32)?,
            emit("athena.class.standing", &self.standing, IntegerDtype::U32)?,
            emit("athena.class.suffix", &self.suffix, IntegerDtype::U32)?,
        ];
        // Written only where it is carried, so a container that never had it is octet-unmoved.
        if !self.extent.is_empty() {
            tensors.push(emit(EXTENT_REGION, &self.extent, IntegerDtype::U32)?);
        }
        tensors.extend([
            emit(
                "athena.vocabulary.octets",
                &vocabulary_octets,
                IntegerDtype::U16,
            )?,
            emit(
                "athena.vocabulary.offsets",
                &vocabulary_offsets,
                IntegerDtype::U32,
            )?,
            emit(
                "athena.architecture",
                &[
                    u64::from(self.height),
                    self.classes() as u64,
                    self.germ.len() as u64,
                    self.vocabulary.len() as u64,
                ],
                IntegerDtype::U32,
            )?,
        ]);
        Ok(write_container(&tensors, &self.metadata))
    }
}

fn read_metadata(header: &str) -> Result<BTreeMap<String, String>, CultivationRefusal> {
    let marker = "{\"__metadata__\":{";
    let Some(start) = header.find(marker) else {
        return Ok(BTreeMap::new());
    };
    let mut at = start + marker.len();
    let bytes: Vec<char> = header.chars().collect();
    let mut metadata = BTreeMap::new();
    let mut field = String::new();
    let mut key: Option<String> = None;
    let mut inside = false;
    let mut escaped = false;
    while at < bytes.len() {
        let character = bytes[at];
        at += 1;
        if inside {
            if escaped {
                field.push(match character {
                    'n' => '\n',
                    other => other,
                });
                escaped = false;
            } else if character == '\\' {
                escaped = true;
            } else if character == '"' {
                inside = false;
                match key.take() {
                    None => key = Some(core::mem::take(&mut field)),
                    Some(name) => {
                        metadata.insert(name, core::mem::take(&mut field));
                    }
                }
            } else {
                field.push(character);
            }
        } else if character == '"' {
            inside = true;
        } else if character == '}' {
            break;
        }
    }
    Ok(metadata)
}

/// The safetensors header with a `__metadata__` object: a length, a JSON map and a flat payload.
fn write_container(tensors: &[IntegerTensor], metadata: &BTreeMap<String, String>) -> Vec<u8> {
    let escape = |text: &str| {
        text.replace('\\', "\\\\")
            .replace('"', "\\\"")
            .replace('\n', "\\n")
    };
    let mut header = String::from("{\"__metadata__\":{");
    for (at, (key, value)) in metadata.iter().enumerate() {
        if at > 0 {
            header.push(',');
        }
        header.push_str(&format!("\"{}\":\"{}\"", escape(key), escape(value)));
    }
    header.push('}');
    let mut offset = 0usize;
    for tensor in tensors {
        let end = offset + tensor.octets.len();
        header.push_str(&format!(
            ",\"{}\":{{\"dtype\":\"{}\",\"shape\":[{},{}],\"data_offsets\":[{offset},{end}]}}",
            tensor.name,
            tensor.dtype.name(),
            tensor.rows,
            tensor.width
        ));
        offset = end;
    }
    header.push('}');
    while header.len() % 8 != 0 {
        header.push(' ');
    }
    let mut octets = Vec::with_capacity(8 + header.len() + offset);
    octets.extend_from_slice(&(header.len() as u64).to_le_bytes());
    octets.extend_from_slice(header.as_bytes());
    for tensor in tensors {
        octets.extend_from_slice(&tensor.octets);
    }
    octets
}

/// Emit a standing atlas as the native rest's arrays, canonically.
pub fn emit_rest(
    atlas: &ExactSuffixEcology,
    metadata: BTreeMap<String, String>,
) -> Result<AthenaRest, CultivationRefusal> {
    let classes = atlas.state_count();
    let chart = TreeChart::label(classes, |state| atlas.suffix_link(state))
        .map_err(|error| CultivationRefusal::Container(format!("{error:?}")))?;
    let mut ordered: Vec<String> = Vec::new();
    let mut index_of: BTreeMap<String, u64> = BTreeMap::new();
    {
        let mut seen: BTreeSet<String> = BTreeSet::new();
        for state in 0..classes as u32 {
            for (germ, _) in atlas.outgoing(state) {
                seen.insert(fiber_bytes(germ.identity())?);
            }
        }
        for (at, token) in seen.into_iter().enumerate() {
            index_of.insert(token.clone(), at as u64);
            ordered.push(token);
        }
    }
    let mut indptr: Vec<u64> = vec![0];
    let mut germ: Vec<u64> = Vec::new();
    let mut target: Vec<u64> = Vec::new();
    let mut standing: Vec<u64> = Vec::with_capacity(classes);
    let mut suffix: Vec<u64> = Vec::with_capacity(classes);
    for state in 0..classes as u32 {
        let mut rows: Vec<(u64, u64)> = Vec::new();
        for (carried, reaches) in atlas.outgoing(state) {
            let token = fiber_bytes(carried.identity())?;
            rows.push((
                index_of.get(&token).copied().unwrap_or(u64::from(u32::MAX)),
                u64::from(reaches),
            ));
        }
        rows.sort();
        for (index, reaches) in rows {
            germ.push(index);
            target.push(reaches);
        }
        indptr.push(germ.len() as u64);
        standing.push(atlas.standing_at(state).unwrap_or(0));
        suffix.push(u64::from(atlas.suffix_link(state).unwrap_or(0)));
    }
    Ok(AthenaRest {
        indptr,
        germ,
        target,
        standing,
        suffix,
        // The emission is P0's face exactly. `phoenix_rest::seal` attaches the extents.
        extent: Vec::new(),
        vocabulary: ordered,
        height: chart.height,
        metadata,
    })
}

// -------------------------------------------------------------------------------------------
// 1. the structured residual — the prediction, mutating nothing
// -------------------------------------------------------------------------------------------

/// What one position of the exposure returned against what the standing rest predicted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PositionResidual {
    pub at: usize,
    /// The class the walk stood in before the material carried this germ.
    pub stood_in: u32,
    /// The germ the material carried, by its surface.
    pub carried: String,
    /// The germ's index in the standing rest's vocabulary, `None` where the rest has never seen it.
    pub carried_index: Option<u64>,
    /// How many distinct germs that class offers — the junction's breadth, `0` at a terminus.
    pub offered_breadth: usize,
    /// How far up the suffix ladder the carried germ is first offered — the rest's own DEPTH law.
    /// `None` when no class on the whole ladder offers it, which is the strongest surprise the
    /// material can return.
    pub first_offering_depth: Option<usize>,
    /// The four-state relation between what the class offered and what the material carried.
    pub relation: ConsequenceRelation,
}

/// **The exposure's structured residual: plural, and never one number.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExposureResidual {
    pub material: String,
    pub positions: Vec<PositionResidual>,
    /// Germ surfaces the standing rest's vocabulary does not carry, in canonical order.
    pub novel_germs: BTreeSet<String>,
    /// `(class, germ surface)` — a class the walk stood in that offers no such germ. These are the
    /// refusals the founding law reads.
    pub refusals: BTreeSet<(u32, String)>,
    /// `(class, germ surface)` pairs where no class on the whole ladder offers the germ.
    pub unreached: BTreeSet<(u32, String)>,
}

impl ExposureResidual {
    /// The relation census, by species. Plural by construction.
    pub fn census(&self) -> BTreeMap<&'static str, usize> {
        let mut census = BTreeMap::new();
        for position in &self.positions {
            *census.entry(relation_name(position.relation)).or_insert(0) += 1;
        }
        census
    }

    /// The depth census — how far up the ladder each position's germ was first offered.
    pub fn depth_census(&self) -> BTreeMap<Option<usize>, usize> {
        let mut census = BTreeMap::new();
        for position in &self.positions {
            *census.entry(position.first_offering_depth).or_insert(0) += 1;
        }
        census
    }

    /// True when the material founded no transport the rest did not already carry.
    pub fn structurally_empty(&self) -> bool {
        self.novel_germs.is_empty() && self.refusals.is_empty()
    }
}

pub const fn relation_name(relation: ConsequenceRelation) -> &'static str {
    match relation {
        ConsequenceRelation::None => "None",
        ConsequenceRelation::Ride => "Ride",
        ConsequenceRelation::OpenIncluded => "OpenIncluded",
        ConsequenceRelation::OpenResidual => "OpenResidual",
    }
}

/// **PREDICT, mutating nothing.**
///
/// Carries the material through the standing rest under the rest's own declared walk law and
/// returns the plural difference between what each class offered and what the material carried.
/// This reads the container and touches no atlas; the still control is that a body is octet-equal
/// before and after.
pub fn read_residual(rest: &AthenaRest, material: &str, path: &[String]) -> ExposureResidual {
    let index_of: BTreeMap<&str, u64> = rest
        .vocabulary
        .iter()
        .enumerate()
        .map(|(at, surface)| (surface.as_str(), at as u64))
        .collect();
    let mut positions = Vec::with_capacity(path.len());
    let mut novel_germs = BTreeSet::new();
    let mut refusals = BTreeSet::new();
    let mut unreached = BTreeSet::new();
    let mut standing_class: u32 = 0;
    for (at, carried) in path.iter().enumerate() {
        let carried_index = index_of.get(carried.as_str()).copied();
        let offered = rest.offered(standing_class);
        let offered_breadth = offered.len();
        let ladder = rest.ladder(standing_class);
        let first_offering_depth = carried_index.and_then(|germ| {
            ladder
                .iter()
                .position(|class| rest.reaches(*class, germ).is_some())
        });
        let offers_here = carried_index
            .map(|germ| rest.reaches(standing_class, germ).is_some())
            .unwrap_or(false);
        let relation = if offered_breadth == 0 {
            ConsequenceRelation::None
        } else if offers_here && offered_breadth == 1 {
            ConsequenceRelation::Ride
        } else if offers_here {
            ConsequenceRelation::OpenIncluded
        } else {
            ConsequenceRelation::OpenResidual
        };
        if carried_index.is_none() {
            novel_germs.insert(carried.clone());
        }
        if !offers_here {
            refusals.insert((standing_class, carried.clone()));
        }
        if first_offering_depth.is_none() {
            unreached.insert((standing_class, carried.clone()));
        }
        positions.push(PositionResidual {
            at,
            stood_in: standing_class,
            carried: carried.clone(),
            carried_index,
            offered_breadth,
            first_offering_depth,
            relation,
        });
        // the walk law: fall along the suffix link and retry; an unseen germ returns to the root
        standing_class = match carried_index {
            None => 0,
            Some(germ) => {
                let mut reached = None;
                for class in &ladder {
                    if let Some(target) = rest.reaches(*class, germ) {
                        reached = Some(target);
                        break;
                    }
                }
                reached.unwrap_or(0)
            }
        };
    }
    ExposureResidual {
        material: material.to_owned(),
        positions,
        novel_germs,
        refusals,
        unreached,
    }
}

// -------------------------------------------------------------------------------------------
// 2. the declared metric, and the covector the R1 face returns through
// -------------------------------------------------------------------------------------------

/// **The declared receiver metric on the R1 ladder face and the declared class-side metric.**
///
/// `G_Y` is diagonal over the residual species: a rational weight per [`ConsequenceRelation`], so
/// the receiver declares what one occurrence of each species of returned difference weighs. `G_X`
/// is a rational scalar on the class side — the whole class-side metric is `g_x * I`, which is the
/// declaration a counting atlas can carry without founding a per-class magnitude nothing measured.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MetricDeclaration {
    pub name: String,
    pub none: BigRational,
    pub ride: BigRational,
    pub open_included: BigRational,
    pub open_residual: BigRational,
    pub class_side: BigRational,
}

fn rational(numerator: i64, denominator: i64) -> BigRational {
    BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
}

impl MetricDeclaration {
    /// **The declared identity.** One unit of returned difference per occurrence, of every species,
    /// with no class-side rebase. This is the metric the sealed successor rest is cultivated under
    /// and it is a declaration, not an absence.
    pub fn identity() -> Self {
        Self {
            name: "identity: G_Y = I over the four residual species, G_X = I".to_owned(),
            none: rational(1, 1),
            ride: rational(1, 1),
            open_included: rational(1, 1),
            open_residual: rational(1, 1),
            class_side: rational(1, 1),
        }
    }

    pub fn weight(&self, relation: ConsequenceRelation) -> &BigRational {
        match relation {
            ConsequenceRelation::None => &self.none,
            ConsequenceRelation::Ride => &self.ride,
            ConsequenceRelation::OpenIncluded => &self.open_included,
            ConsequenceRelation::OpenResidual => &self.open_residual,
        }
    }

    /// The diagonal of `G_Y` over the exposure, in position order.
    pub fn codomain_diagonal(&self, residual: &ExposureResidual) -> Vec<BigRational> {
        residual
            .positions
            .iter()
            .map(|position| self.weight(position.relation).clone())
            .collect()
    }
}

/// **The exposure's deposit incidence — the exact differential of the R1 ladder face with respect
/// to the standings.**
///
/// `A[p][s] = 1` exactly when class `s` lies on the suffix ladder of the class occurrence `p`
/// landed in. `y = A q` is then the standing the walk reads along its own depth ladder, which is
/// the face the rest's future and depth laws climb.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DepositIncidence {
    /// Per material position, the ladder of the class it landed in, finest first.
    pub ladders: Vec<Vec<u32>>,
    pub classes: usize,
}

impl DepositIncidence {
    /// Read the incidence off the body the deposit founded.
    pub fn of(atlas: &ExactSuffixEcology, lineage: &AbsorbLineage) -> Self {
        let classes = atlas.state_count();
        let ladders = lineage
            .landed
            .iter()
            .map(|landed| {
                let mut ladder = vec![*landed];
                let mut at = *landed;
                while at != 0 {
                    match atlas.suffix_link(at) {
                        Some(parent) if parent != at => {
                            at = parent;
                            ladder.push(at);
                        }
                        _ => break,
                    }
                }
                ladder
            })
            .collect();
        Self { ladders, classes }
    }

    /// The dense window of `A` over the first `positions` positions and the classes they touch.
    /// Small by construction; this is what the exact matrix carrier is handed.
    pub fn window(&self, positions: usize) -> (Vec<u32>, Vec<Vec<BigRational>>) {
        let taken = positions.min(self.ladders.len());
        let mut columns: BTreeSet<u32> = BTreeSet::new();
        for ladder in &self.ladders[..taken] {
            columns.extend(ladder.iter().copied());
        }
        let columns: Vec<u32> = columns.into_iter().collect();
        let rows = self.ladders[..taken]
            .iter()
            .map(|ladder| {
                let held: BTreeSet<u32> = ladder.iter().copied().collect();
                columns
                    .iter()
                    .map(|class| {
                        if held.contains(class) {
                            rational(1, 1)
                        } else {
                            rational(0, 1)
                        }
                    })
                    .collect()
            })
            .collect();
        (columns, rows)
    }

    /// **The cultivation return: `dq = G_X^-1 A^T G_Y r`, computed exactly and sparsely.**
    ///
    /// `r` is the exposure's residual covector on the R1 face — one entry per position, the unit of
    /// returned difference that occurrence carried. The image is the covector on the class side,
    /// which is the deposit.
    pub fn adjoint_image(
        &self,
        residual: &ExposureResidual,
        metric: &MetricDeclaration,
        covector: &[BigRational],
    ) -> Result<BTreeMap<u32, BigRational>, CultivationRefusal> {
        if metric.class_side == rational(0, 1) {
            return Err(CultivationRefusal::SingularMetric(
                "the class-side metric is zero and has no inverse".to_owned(),
            ));
        }
        let inverse = rational(1, 1) / metric.class_side.clone();
        let mut image: BTreeMap<u32, BigRational> = BTreeMap::new();
        for (at, ladder) in self.ladders.iter().enumerate() {
            let weight = metric.weight(residual.positions[at].relation) * &covector[at];
            if weight == rational(0, 1) {
                continue;
            }
            let carried = &inverse * &weight;
            for class in ladder {
                image
                    .entry(*class)
                    .and_modify(|held| *held += &carried)
                    .or_insert_with(|| carried.clone());
            }
        }
        Ok(image)
    }
}

/// The residual covector on the R1 face: one unit of returned difference per occurrence. Its
/// species is carried by the residual and weighed by the declared metric, which is where a
/// receiver's declaration enters and the only place it does.
pub fn unit_covector(residual: &ExposureResidual) -> Vec<BigRational> {
    residual.positions.iter().map(|_| rational(1, 1)).collect()
}

// -------------------------------------------------------------------------------------------
// 3. the delta the law derives
// -------------------------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FoundedSpecies {
    /// The class the material's own occurrence carried.
    Carried,
    /// A split of a class that stood, which inherits its transport row, its link and its occupancy.
    Split { from: u32 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoundedClass {
    pub class: u32,
    pub species: FoundedSpecies,
    /// The material position that founded it — the row's cause.
    pub caused_by: usize,
    /// The germ that position carried.
    pub germ: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoundedTransition {
    pub class: u32,
    pub germ: String,
    pub target: u32,
    pub caused_by: usize,
    /// True when the class stood in the predecessor: this is a founding **inside** the standing
    /// body, licensed by that class's refusal of that germ.
    pub on_standing_class: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RebasedTransition {
    pub class: u32,
    pub germ: String,
    pub before: u32,
    pub after: u32,
    pub caused_by: usize,
    pub on_standing_class: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RebasedSuffix {
    pub class: u32,
    pub before: Option<u32>,
    pub after: u32,
    pub caused_by: usize,
    pub on_standing_class: bool,
}

/// **The owned delta: what the exposure deposited, every row carrying its cause.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CultivationDelta {
    pub material: String,
    pub classes_before: usize,
    pub classes_after: usize,
    pub germs_founded: Vec<String>,
    pub classes_founded: Vec<FoundedClass>,
    pub transitions_founded: Vec<FoundedTransition>,
    pub transitions_rebased: Vec<RebasedTransition>,
    pub suffix_rebased: Vec<RebasedSuffix>,
    /// The committed standing of every class, derived by the adjoint law:
    /// `standing(s) = carried(s) + (G_X^-1 A^T G_Y r)_s`.
    pub standing: Vec<u64>,
    /// The adjoint image alone, sparse and by class — the increment the exposure deposited.
    pub standing_increments: BTreeMap<u32, u64>,
    pub metric: String,
    /// The ordered replay this delta commits by. One entry per material position plus the
    /// separator; the order is the chronology and reordering it founds a different body.
    pub replay: Vec<(Option<String>, Vec<ExtendEvent>)>,
}

impl CultivationDelta {
    pub fn transitions_founded_on_standing(&self) -> usize {
        self.transitions_founded
            .iter()
            .filter(|row| row.on_standing_class)
            .count()
    }

    pub fn classes_split(&self) -> usize {
        self.classes_founded
            .iter()
            .filter(|row| matches!(row.species, FoundedSpecies::Split { .. }))
            .count()
    }
}

/// **DERIVE the delta from the residual and the deposit's forward lineage.**
///
/// The structural face is licensed row by row: every founded class, transition and rebased link
/// names the material position that caused it. The standings face is derived by the declared
/// return law and by nothing else — no standing anywhere in this function is read from the body the
/// deposit founded.
#[allow(clippy::too_many_arguments)]
pub fn derive(
    predecessor: &AthenaRest,
    residual: &ExposureResidual,
    lineage: &AbsorbLineage,
    incidence: &DepositIncidence,
    metric: &MetricDeclaration,
    covector: &[BigRational],
    path: &[String],
) -> Result<CultivationDelta, CultivationRefusal> {
    let classes_before = lineage.classes_before;
    let classes_after = incidence.classes;
    let standing_class = |class: u32| (class as usize) < classes_before;

    let mut classes_founded = Vec::new();
    let mut transitions_founded = Vec::new();
    let mut transitions_rebased = Vec::new();
    let mut suffix_rebased = Vec::new();
    let mut replay: Vec<(Option<String>, Vec<ExtendEvent>)> = Vec::new();
    let mut split_origin: BTreeMap<u32, u32> = BTreeMap::new();

    let groups = lineage
        .per_position
        .iter()
        .enumerate()
        .map(|(at, record)| (Some(path[at].clone()), at, record))
        .chain(core::iter::once((None, path.len(), &lineage.boundary)));
    for (germ, at, record) in groups {
        replay.push((germ.clone(), record.events.clone()));
        for event in &record.events {
            match event {
                ExtendEvent::Founded { class, split_from } => {
                    let species = match split_from {
                        None => FoundedSpecies::Carried,
                        Some(origin) => {
                            split_origin.insert(*class as u32, *origin as u32);
                            FoundedSpecies::Split {
                                from: *origin as u32,
                            }
                        }
                    };
                    classes_founded.push(FoundedClass {
                        class: *class as u32,
                        species,
                        caused_by: at,
                        germ: germ.clone().unwrap_or_else(|| "<separator>".to_owned()),
                    });
                }
                ExtendEvent::TransitionAdded { class, target } => {
                    if let Some(germ) = germ.clone() {
                        transitions_founded.push(FoundedTransition {
                            class: *class as u32,
                            germ,
                            target: *target as u32,
                            caused_by: at,
                            on_standing_class: standing_class(*class as u32),
                        });
                    }
                }
                ExtendEvent::TransitionRebased {
                    class,
                    before,
                    after,
                } => {
                    if let Some(germ) = germ.clone() {
                        transitions_rebased.push(RebasedTransition {
                            class: *class as u32,
                            germ,
                            before: *before as u32,
                            after: *after as u32,
                            caused_by: at,
                            on_standing_class: standing_class(*class as u32),
                        });
                    }
                }
                ExtendEvent::SuffixRebased {
                    class,
                    before,
                    after,
                } => suffix_rebased.push(RebasedSuffix {
                    class: *class as u32,
                    before: before.map(|held| held as u32),
                    after: *after as u32,
                    caused_by: at,
                    on_standing_class: standing_class(*class as u32),
                }),
            }
        }
    }

    // ---- the standings face: the covector returned through the declared metric ----
    let image = incidence.adjoint_image(residual, metric, covector)?;
    let mut standing_increments = BTreeMap::new();
    let mut standing = vec![0u64; classes_after];
    for class in 0..classes_after as u32 {
        let carried = if standing_class(class) {
            predecessor.standing[class as usize]
        } else {
            match split_origin.get(&class) {
                // A split inherits the occupancy of the class it divides. Its own subtree is that
                // class's subtree, so the carried part is exactly that class's standing before.
                Some(origin) if standing_class(*origin) => predecessor.standing[*origin as usize],
                Some(origin) => {
                    carried_of_split(*origin, &split_origin, predecessor, classes_before)
                }
                None => 0,
            }
        };
        let deposited = match image.get(&class) {
            None => 0u64,
            Some(exact) => {
                if exact.denom() != &BigInt::from(1) {
                    return Err(CultivationRefusal::NonIntegralDeposit {
                        class,
                        image: exact.to_string(),
                    });
                }
                if exact.numer() < &BigInt::from(0) {
                    return Err(CultivationRefusal::NegativeDeposit {
                        class,
                        image: exact.to_string(),
                    });
                }
                let magnitude: BigUint = exact.numer().magnitude().clone();
                u64::try_from(magnitude).map_err(|_| CultivationRefusal::NonIntegralDeposit {
                    class,
                    image: exact.to_string(),
                })?
            }
        };
        if deposited != 0 {
            standing_increments.insert(class, deposited);
        }
        standing[class as usize] = carried + deposited;
    }

    let mut germs_founded: Vec<String> = residual.novel_germs.iter().cloned().collect();
    germs_founded.sort();
    Ok(CultivationDelta {
        material: residual.material.clone(),
        classes_before,
        classes_after,
        germs_founded,
        classes_founded,
        transitions_founded,
        transitions_rebased,
        suffix_rebased,
        standing,
        standing_increments,
        metric: metric.name.clone(),
        replay,
    })
}

/// A split of a split inherits through its own origin.
///
/// **This terminates structurally and carries no authored bound.** A split is founded at the index
/// one past the body's extent and divides a class that already stood, so `origin < class` strictly;
/// the walk is therefore strictly decreasing and reaches an index below `classes_before` or a class
/// with no origin. The strict decrease is asserted rather than assumed.
fn carried_of_split(
    origin: u32,
    split_origin: &BTreeMap<u32, u32>,
    predecessor: &AthenaRest,
    classes_before: usize,
) -> u64 {
    let mut at = origin;
    while (at as usize) >= classes_before {
        match split_origin.get(&at) {
            Some(next) if *next < at => at = *next,
            // Either the class has no origin, or the lineage is not strictly decreasing, which
            // would mean the deposit's own record is malformed. Neither inherits an occupancy.
            _ => return 0,
        }
    }
    predecessor.standing[at as usize]
}

// -------------------------------------------------------------------------------------------
// 4. commit — the delta applied to the predecessor by replay
// -------------------------------------------------------------------------------------------

/// **COMMIT the derived delta onto a standing rest.**
///
/// The transport rows are replayed from the predecessor's own rows; no row is copied out of the
/// body the deposit founded. The standings are the delta's derived standings and nothing else.
pub fn commit(
    predecessor: &AthenaRest,
    delta: &CultivationDelta,
) -> Result<AthenaRest, CultivationRefusal> {
    if predecessor.classes() != delta.classes_before {
        return Err(CultivationRefusal::Unlicensed(format!(
            "the delta was derived against {} classes and is offered {}",
            delta.classes_before,
            predecessor.classes()
        )));
    }
    // ---- the vocabulary: the standing surfaces plus the founded ones, canonically ----
    let mut surfaces: BTreeSet<String> = predecessor.vocabulary.iter().cloned().collect();
    for germ in &delta.germs_founded {
        surfaces.insert(germ.clone());
    }
    let vocabulary: Vec<String> = surfaces.into_iter().collect();
    let index_of: BTreeMap<&str, u64> = vocabulary
        .iter()
        .enumerate()
        .map(|(at, surface)| (surface.as_str(), at as u64))
        .collect();
    let remap: Vec<u64> = predecessor
        .vocabulary
        .iter()
        .map(|surface| index_of[surface.as_str()])
        .collect();

    // ---- the transport rows, replayed from the predecessor's own ----
    let mut rows: Vec<BTreeMap<u64, u64>> = Vec::with_capacity(delta.classes_after);
    for class in 0..predecessor.classes() as u32 {
        let (start, end) = predecessor.row_span(class);
        rows.push(
            (start..end)
                .map(|at| (remap[predecessor.germ[at] as usize], predecessor.target[at]))
                .collect(),
        );
    }
    rows.resize(delta.classes_after, BTreeMap::new());
    let mut suffix: Vec<u64> = predecessor.suffix.clone();
    suffix.resize(delta.classes_after, 0);
    for (germ, events) in &delta.replay {
        let germ_index = germ.as_deref().map(|surface| {
            *index_of
                .get(surface)
                .expect("a delta's germ is in the committed vocabulary")
        });
        for event in events {
            match event {
                ExtendEvent::Founded { class, split_from } => {
                    let class = *class;
                    if class >= rows.len() {
                        return Err(CultivationRefusal::Unlicensed(format!(
                            "class {class} is past the delta's own class population"
                        )));
                    }
                    match split_from {
                        // A split inherits the transport row and the link of the class it divides,
                        // AS THEY STAND AT THIS INSTANT. That is why the replay is ordered.
                        Some(origin) => {
                            rows[class] = rows[*origin].clone();
                            suffix[class] = suffix[*origin];
                        }
                        None => {
                            rows[class] = BTreeMap::new();
                            suffix[class] = 0;
                        }
                    }
                }
                ExtendEvent::TransitionAdded { class, target } => {
                    if let Some(germ_index) = germ_index {
                        rows[*class].insert(germ_index, *target as u64);
                    }
                }
                ExtendEvent::TransitionRebased { class, after, .. } => {
                    if let Some(germ_index) = germ_index {
                        rows[*class].insert(germ_index, *after as u64);
                    }
                }
                ExtendEvent::SuffixRebased { class, after, .. } => {
                    suffix[*class] = *after as u64;
                }
            }
        }
    }

    let mut indptr: Vec<u64> = vec![0];
    let mut germ: Vec<u64> = Vec::new();
    let mut target: Vec<u64> = Vec::new();
    for row in &rows {
        for (index, reaches) in row {
            germ.push(*index);
            target.push(*reaches);
        }
        indptr.push(germ.len() as u64);
    }
    let chart = TreeChart::label(delta.classes_after, |class| {
        if class == 0 {
            None
        } else {
            Some(suffix[class as usize] as u32)
        }
    })
    .map_err(|error| CultivationRefusal::Container(format!("{error:?}")))?;
    Ok(AthenaRest {
        indptr,
        germ,
        target,
        standing: delta.standing.clone(),
        suffix,
        // A commit derives the germ side by replay. A class extent is not among the rows the delta
        // carries — `ExtendEvent` records what was founded, not how long it is — so the successor's
        // extents come from the transport that deposited, and `phoenix_rest::cultivate` attaches
        // them there and says so.
        extent: Vec::new(),
        vocabulary,
        height: chart.height,
        metadata: predecessor.metadata.clone(),
    })
}

/// The metadata key a sealed successor carries so that a withdrawal can restore the predecessor's
/// own material declaration rather than guessing it.
pub const PREDECESSOR_MATERIAL_KEY: &str = "cultivation.predecessor.material";

/// **WITHDRAW the delta — the targeted ablation.**
///
/// The founded classes leave, the founded transitions leave, the rebased links return to what they
/// were, the founded germs leave the vocabulary and every standing returns to its carried part.
/// **The declared cultivation lineage is struck too**: a body that no longer carries the deposit
/// must not go on declaring it, and the predecessor's own material declaration is restored from
/// [`PREDECESSOR_MATERIAL_KEY`], which the seal carries for exactly this.
///
/// This is a deletion inside the standing body, not a rebuild from a smaller corpus.
pub fn withdraw(
    successor: &AthenaRest,
    delta: &CultivationDelta,
) -> Result<AthenaRest, CultivationRefusal> {
    if successor.classes() != delta.classes_after {
        return Err(CultivationRefusal::Unlicensed(format!(
            "the delta founded {} classes and is offered {}",
            delta.classes_after,
            successor.classes()
        )));
    }
    let index_of: BTreeMap<&str, u64> = successor
        .vocabulary
        .iter()
        .enumerate()
        .map(|(at, surface)| (surface.as_str(), at as u64))
        .collect();
    let founded: BTreeSet<&str> = delta.germs_founded.iter().map(String::as_str).collect();
    let vocabulary: Vec<String> = successor
        .vocabulary
        .iter()
        .filter(|surface| !founded.contains(surface.as_str()))
        .cloned()
        .collect();
    let back: BTreeMap<&str, u64> = vocabulary
        .iter()
        .enumerate()
        .map(|(at, surface)| (surface.as_str(), at as u64))
        .collect();

    let mut rows: Vec<BTreeMap<u64, u64>> = (0..delta.classes_before as u32)
        .map(|class| {
            let (start, end) = successor.row_span(class);
            (start..end)
                .map(|at| (successor.germ[at], successor.target[at]))
                .collect()
        })
        .collect();
    let mut suffix: Vec<u64> = successor.suffix[..delta.classes_before].to_vec();
    // undo in reverse chronology
    for row in delta.suffix_rebased.iter().rev() {
        if row.on_standing_class {
            suffix[row.class as usize] = row.before.unwrap_or(0) as u64;
        }
    }
    for row in delta.transitions_rebased.iter().rev() {
        if row.on_standing_class {
            rows[row.class as usize].insert(index_of[row.germ.as_str()], u64::from(row.before));
        }
    }
    for row in delta.transitions_founded.iter().rev() {
        if row.on_standing_class {
            rows[row.class as usize].remove(&index_of[row.germ.as_str()]);
        }
    }
    let mut indptr: Vec<u64> = vec![0];
    let mut germ: Vec<u64> = Vec::new();
    let mut target: Vec<u64> = Vec::new();
    for row in &rows {
        for (index, reaches) in row {
            let surface = successor.vocabulary[*index as usize].as_str();
            let Some(back) = back.get(surface) else {
                return Err(CultivationRefusal::Unlicensed(format!(
                    "withdrawing germ {surface:?} would orphan a transition that stood"
                )));
            };
            germ.push(*back);
            target.push(*reaches);
        }
        indptr.push(germ.len() as u64);
    }
    let standing: Vec<u64> = (0..delta.classes_before as u32)
        .map(|class| {
            successor.standing[class as usize]
                - delta.standing_increments.get(&class).copied().unwrap_or(0)
        })
        .collect();
    let chart = TreeChart::label(delta.classes_before, |class| {
        if class == 0 {
            None
        } else {
            Some(suffix[class as usize] as u32)
        }
    })
    .map_err(|error| CultivationRefusal::Container(format!("{error:?}")))?;
    let mut metadata = successor.metadata.clone();
    if let Some(material) = metadata.remove(PREDECESSOR_MATERIAL_KEY) {
        metadata.insert("material".to_owned(), material);
    }
    metadata.retain(|key, _| !key.starts_with("cultivation."));
    Ok(AthenaRest {
        indptr,
        germ,
        target,
        standing,
        suffix,
        // A withdrawal cannot restore an extent it never carried; the ablated body is the P0 face.
        extent: Vec::new(),
        vocabulary,
        height: chart.height,
        metadata,
    })
}

// -------------------------------------------------------------------------------------------
// 5. conduct — the rest's own three laws, exactly, on this surface
// -------------------------------------------------------------------------------------------

/// One prompt's plural section: every germ the landed class's ladder offers, with the standing of
/// the class it reaches and how far up the ladder it was found. Never one winner.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConductedSection {
    pub prompt: String,
    pub class: u32,
    pub standing: u64,
    pub trace: Vec<String>,
    /// `(germ surface, standing, depth)`, canonically ordered by surface.
    pub offered: Vec<(String, u64, usize)>,
}

impl ConductedSection {
    /// A canonical octet face, so bit-equality between two conducts is a comparison of bytes.
    pub fn face(&self) -> Vec<u8> {
        let mut face = Vec::new();
        face.extend_from_slice(self.prompt.as_bytes());
        face.push(0);
        face.extend_from_slice(&self.class.to_le_bytes());
        face.extend_from_slice(&self.standing.to_le_bytes());
        for step in &self.trace {
            face.extend_from_slice(step.as_bytes());
            face.push(0x1f);
        }
        face.push(0);
        for (surface, standing, depth) in &self.offered {
            face.extend_from_slice(surface.as_bytes());
            face.push(0x1f);
            face.extend_from_slice(&standing.to_le_bytes());
            face.extend_from_slice(&(*depth as u64).to_le_bytes());
        }
        face
    }

    /// The support alone — which germs at which depth, with every standing dropped. This is the
    /// face that survives a corpus-wide occupancy move, and P0 measured that it is the only one
    /// that does.
    pub fn support(&self) -> Vec<u8> {
        let mut face = Vec::new();
        for (surface, _, depth) in &self.offered {
            face.extend_from_slice(surface.as_bytes());
            face.push(0x1f);
            face.extend_from_slice(&(*depth as u64).to_le_bytes());
        }
        face
    }

    /// The support at depth zero — what the full context alone licenses.
    pub fn depth_zero_support(&self) -> Vec<u8> {
        let mut face = Vec::new();
        for (surface, _, depth) in &self.offered {
            if *depth == 0 {
                face.extend_from_slice(surface.as_bytes());
                face.push(0x1f);
            }
        }
        face
    }
}

/// **Conduct one prompt from the rest alone**, under the container's own declared walk, future and
/// depth laws. Exact and integral throughout.
pub fn conduct(rest: &AthenaRest, prompt: &str, tokens: &[String]) -> ConductedSection {
    let index_of: BTreeMap<&str, u64> = rest
        .vocabulary
        .iter()
        .enumerate()
        .map(|(at, surface)| (surface.as_str(), at as u64))
        .collect();
    let mut class: u32 = 0;
    let mut trace = Vec::new();
    for token in tokens {
        match index_of.get(token.as_str()) {
            None => {
                trace.push(format!("{token}=UNSEEN->root"));
                class = 0;
            }
            Some(germ) => {
                let ladder = rest.ladder(class);
                let mut reached = None;
                for (depth, held) in ladder.iter().enumerate() {
                    if let Some(target) = rest.reaches(*held, *germ) {
                        reached = Some((target, depth));
                        break;
                    }
                }
                match reached {
                    Some((target, 0)) => {
                        trace.push(token.clone());
                        class = target;
                    }
                    Some((target, _)) => {
                        trace.push(format!("{token}*ARC"));
                        class = target;
                    }
                    None => {
                        trace.push(format!("{token}=UNREACHED->root"));
                        class = 0;
                    }
                }
            }
        }
    }
    // the future and depth laws, over the whole vocabulary
    let ladder = rest.ladder(class);
    let mut held: BTreeMap<u64, (u64, usize)> = BTreeMap::new();
    for (depth, at) in ladder.iter().enumerate() {
        let (start, end) = rest.row_span(*at);
        for slot in start..end {
            held.entry(rest.germ[slot])
                .or_insert((rest.standing[rest.target[slot] as usize], depth));
        }
    }
    ConductedSection {
        prompt: prompt.to_owned(),
        class,
        standing: rest.standing[class as usize],
        trace,
        offered: held
            .into_iter()
            .map(|(germ, (standing, depth))| {
                (rest.vocabulary[germ as usize].clone(), standing, depth)
            })
            .collect(),
    }
}

/// Read the germ surfaces of one material under a declared lexical reading.
pub fn surfaces_of(path: &[ResonanceGerm]) -> Result<Vec<String>, CultivationRefusal> {
    path.iter()
        .map(|germ| fiber_bytes(germ.identity()).map_err(CultivationRefusal::from))
        .collect()
}

// -------------------------------------------------------------------------------------------
// 6. interventions on a standing rest — the native arm's matched siblings
// -------------------------------------------------------------------------------------------

/// **An intervention enacted on a COPY of a standing rest, so the sibling is matched.**
///
/// # The composition attempt, stated before the owner
///
/// Three interventions on a native rest already stand and are composed rather than restated:
/// [`withdraw`] is the delta ablation (a deletion inside the standing body), the cultivation itself
/// is the pre-versus-post intervention, and clearing [`AthenaRest::extent`] before
/// [`AthenaRest::write_container`] is the region withdrawal whose refusal
/// [`crate::phoenix_rest::mount_atlas`] already names. On the resident side,
/// `holonic_engine::resident_law`'s `WithdrawRows` and `PermuteColumns` are Station D's two
/// intervention laws — but they act on a dense device section of BF16 words addressed by row and
/// column, and this arm's material is a **sparse integer transport addressed by (class, germ)**.
/// Neither law can name a germ family or a suffix-height band, and the sparse row is not a column
/// span, so the genuinely absent relation is exactly this: **an intervention on the native sparse
/// transport that leaves the container conductible and its arithmetic exact.**
///
/// Every variant is the *caller's* declaration, exactly as Station D typed its siblings: none of
/// them is a law the rest declares, and an intervened rest carries
/// [`INTERVENTION_KEY`] in its metadata so a later reader cannot mistake a sibling for a body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RestIntervention {
    /// Withdraw every transition carrying one germ index — the family withdrawal. The germ stays in
    /// the vocabulary (so the walk can still *ask* for it), and every class that offered it now
    /// refuses it, which is the difference between withdrawing a family and shrinking a codec.
    WithdrawGermFamily { germ: u64 },
    /// Withdraw every transition whose **target** class sits at a suffix-ladder height inside the
    /// closed band — the scale intervention. The rest's own depth law is the only ladder here.
    WithdrawHeightBand { low: u32, high: u32 },
    /// Transpose two germ labels throughout the transport — the adjacency permutation. The
    /// transition population, every row's length and the whole target multiset are unmoved; only
    /// which germ reaches which continuation moves.
    TransposeGermLabels { left: u64, right: u64 },
}

/// The metadata key an intervened copy carries. A sibling that did not say so would be a body.
pub const INTERVENTION_KEY: &str = "intervention.declared";

/// What one intervention did, plurally. Counts are here because a matched sibling must be shown to
/// be matched, and the populations are the evidence for it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterventionReceipt {
    pub declaration: String,
    pub transitions_before: usize,
    pub transitions_after: usize,
    /// The transitions the intervention removed, by `(class, germ index, target)` — the artifact,
    /// bounded for exhibition by the caller and complete here.
    pub withdrawn: Vec<(u32, u64, u32)>,
    /// The transitions whose germ label moved, by `(class, germ before, germ after)`.
    pub relabelled: Vec<(u32, u64, u64)>,
    /// Classes whose transport row changed at all.
    pub classes_touched: BTreeSet<u32>,
    /// True when the transition population, every row length and the target multiset are unmoved —
    /// which is what makes a permutation sibling matched rather than smaller.
    pub population_preserved: bool,
}

/// Every class's suffix-ladder height, read off `athena.class.suffix` and nothing else.
///
/// The height of a class is the number of suffix links between it and the root of its link tree —
/// the same ladder [`AthenaRest::ladder`] climbs, and the only depth receiver this arm has. A class
/// the links cannot resolve within the population (which would be a link cycle, and the committed
/// rests carry none) is left at [`u32::MAX`] rather than given a number nothing measured.
pub fn class_heights(rest: &AthenaRest) -> Vec<u32> {
    let classes = rest.classes();
    let mut height = vec![u32::MAX; classes];
    for class in 0..classes as u32 {
        if height[class as usize] != u32::MAX {
            continue;
        }
        let mut climb: Vec<u32> = Vec::new();
        let mut at = class;
        loop {
            if height[at as usize] != u32::MAX {
                break;
            }
            let parent = rest.suffix[at as usize] as u32;
            if parent == at {
                height[at as usize] = 0;
                break;
            }
            climb.push(at);
            at = parent;
            if climb.len() > classes {
                // The links did not resolve. Nothing here invents a height for them.
                climb.clear();
                break;
            }
        }
        if climb.is_empty() {
            continue;
        }
        let mut base = height[at as usize];
        if base == u32::MAX {
            continue;
        }
        for held in climb.iter().rev() {
            base += 1;
            height[*held as usize] = base;
        }
    }
    height
}

/// **Enact one intervention on a copy.** The rest handed in is never touched.
pub fn intervene(
    rest: &AthenaRest,
    intervention: &RestIntervention,
) -> Result<(AthenaRest, InterventionReceipt), CultivationRefusal> {
    let refuse = |why: String| CultivationRefusal::Container(why);
    let vocabulary = rest.vocabulary.len() as u64;
    let declaration = match intervention {
        RestIntervention::WithdrawGermFamily { germ } => {
            if *germ >= vocabulary {
                return Err(refuse(format!(
                    "germ {germ} is outside the vocabulary of {vocabulary}"
                )));
            }
            format!(
                "withdraw the germ family {germ} ({:?}) from every transport row",
                rest.vocabulary[*germ as usize]
            )
        }
        RestIntervention::WithdrawHeightBand { low, high } => {
            if low > high {
                return Err(refuse(format!(
                    "the band {low}..{high} is empty by its own order"
                )));
            }
            format!("withdraw every transition whose target sits at suffix height {low}..={high}")
        }
        RestIntervention::TransposeGermLabels { left, right } => {
            if *left >= vocabulary || *right >= vocabulary {
                return Err(refuse(format!(
                    "the transposition ({left},{right}) leaves the vocabulary of {vocabulary}"
                )));
            }
            if left == right {
                return Err(refuse(
                    "a transposition of a germ with itself moves nothing and is not a sibling"
                        .to_owned(),
                ));
            }
            format!(
                "transpose the germ labels {left} ({:?}) and {right} ({:?}) throughout the transport",
                rest.vocabulary[*left as usize], rest.vocabulary[*right as usize]
            )
        }
    };

    let heights = match intervention {
        RestIntervention::WithdrawHeightBand { .. } => class_heights(rest),
        _ => Vec::new(),
    };

    let mut indptr: Vec<u64> = Vec::with_capacity(rest.indptr.len());
    let mut germ: Vec<u64> = Vec::with_capacity(rest.germ.len());
    let mut target: Vec<u64> = Vec::with_capacity(rest.target.len());
    let mut withdrawn: Vec<(u32, u64, u32)> = Vec::new();
    let mut relabelled: Vec<(u32, u64, u64)> = Vec::new();
    let mut classes_touched: BTreeSet<u32> = BTreeSet::new();
    let mut rows_preserved = true;
    indptr.push(0);
    for class in 0..rest.classes() as u32 {
        let start = rest.indptr[class as usize] as usize;
        let end = rest.indptr[class as usize + 1] as usize;
        let mut row: Vec<(u64, u64)> = Vec::with_capacity(end - start);
        for slot in start..end {
            let held = rest.germ[slot];
            let reaches = rest.target[slot];
            match intervention {
                RestIntervention::WithdrawGermFamily { germ: family } => {
                    if held == *family {
                        withdrawn.push((class, held, reaches as u32));
                        classes_touched.insert(class);
                        continue;
                    }
                    row.push((held, reaches));
                }
                RestIntervention::WithdrawHeightBand { low, high } => {
                    let at = heights[reaches as usize];
                    if at >= *low && at <= *high {
                        withdrawn.push((class, held, reaches as u32));
                        classes_touched.insert(class);
                        continue;
                    }
                    row.push((held, reaches));
                }
                RestIntervention::TransposeGermLabels { left, right } => {
                    let moved = if held == *left {
                        *right
                    } else if held == *right {
                        *left
                    } else {
                        held
                    };
                    if moved != held {
                        relabelled.push((class, held, moved));
                        classes_touched.insert(class);
                    }
                    row.push((moved, reaches));
                }
            }
        }
        // The card searches a row 32-ary by germ index, so a row that is not ascending is a row the
        // rest's own walk law cannot read. Sorting here is the sibling meeting the standing law.
        row.sort_by_key(|(held, _)| *held);
        if row.len() != end - start {
            rows_preserved = false;
        }
        for (held, reaches) in row {
            germ.push(held);
            target.push(reaches);
        }
        indptr.push(germ.len() as u64);
    }

    let population_preserved = rows_preserved && {
        let mut before: Vec<u64> = rest.target.clone();
        let mut after: Vec<u64> = target.clone();
        before.sort_unstable();
        after.sort_unstable();
        before == after
    };

    let mut metadata = rest.metadata.clone();
    metadata.insert(INTERVENTION_KEY.to_owned(), declaration.clone());
    let sibling = AthenaRest {
        indptr,
        germ,
        target,
        standing: rest.standing.clone(),
        suffix: rest.suffix.clone(),
        extent: rest.extent.clone(),
        vocabulary: rest.vocabulary.clone(),
        height: rest.height,
        metadata,
    };
    let receipt = InterventionReceipt {
        declaration,
        transitions_before: rest.transitions(),
        transitions_after: sibling.transitions(),
        withdrawn,
        relabelled,
        classes_touched,
        population_preserved,
    };
    Ok((sibling, receipt))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::causal_language::{lexical_tokens, token_germs_public};
    use crate::holonic_training::{consequence_complex, derive_templates, FaceAddress, SourceFace};

    fn atlas_of(texts: &[&str]) -> (ExactSuffixEcology, Vec<Vec<String>>) {
        let mut paths = Vec::new();
        let mut surfaces = Vec::new();
        for text in texts {
            let tokens = lexical_tokens(text);
            let path = token_germs_public(&tokens).expect("germs");
            surfaces.push(surfaces_of(&path).expect("surfaces"));
            paths.push(path);
        }
        (
            ExactSuffixEcology::condition(&paths).expect("conditioned"),
            surfaces,
        )
    }

    fn declarations() -> BTreeMap<String, String> {
        let mut metadata = BTreeMap::new();
        metadata.insert("schema".to_owned(), REST_SCHEMA.to_owned());
        metadata
    }

    // ---------------------------------------------------------------------------------------
    // the interventions on a standing rest — the native arm's matched siblings
    // ---------------------------------------------------------------------------------------

    fn intervention_fixture() -> AthenaRest {
        let (atlas, _) = atlas_of(&[
            "a chart is a receiver and the transport is a jacobian",
            "the receiver declares the grain it reads at",
            "a chart forgets a winding and the receiver keeps the turn",
        ]);
        emit_rest(&atlas, declarations()).expect("emitted")
    }

    fn germ_index(rest: &AthenaRest, surface: &str) -> u64 {
        rest.vocabulary
            .iter()
            .position(|held| held == surface)
            .expect("the surface is in the vocabulary") as u64
    }

    /// The height of a class is the length of its own ladder, and the two readings are one reading.
    #[test]
    fn the_class_heights_are_exactly_the_ladders_the_rest_climbs() {
        let rest = intervention_fixture();
        let heights = class_heights(&rest);
        assert_eq!(heights.len(), rest.classes());
        for class in 0..rest.classes() as u32 {
            assert_eq!(
                heights[class as usize],
                rest.ladder(class).len() as u32 - 1,
                "class {class}"
            );
        }
        assert_eq!(heights[0], 0, "the root sits at height zero");
    }

    /// The family leaves the transport and nothing else does; the vocabulary is unmoved, so the
    /// walk can still ask for the germ and every class now refuses it.
    #[test]
    fn the_germ_family_withdrawal_removes_that_family_and_only_that_family() {
        let rest = intervention_fixture();
        let germ = germ_index(&rest, "receiver");
        let carried = (0..rest.classes() as u32)
            .filter(|class| rest.reaches(*class, germ).is_some())
            .count();
        assert!(
            carried > 0,
            "the fixture must carry the family being withdrawn"
        );

        let (sibling, receipt) =
            intervene(&rest, &RestIntervention::WithdrawGermFamily { germ }).expect("intervened");
        assert_eq!(receipt.withdrawn.len(), carried);
        assert_eq!(
            receipt.transitions_after + carried,
            receipt.transitions_before
        );
        assert!(
            !receipt.population_preserved,
            "a withdrawal is not a permutation"
        );
        assert_eq!(
            sibling.vocabulary, rest.vocabulary,
            "the codec does not shrink"
        );
        for class in 0..rest.classes() as u32 {
            assert!(
                sibling.reaches(class, germ).is_none(),
                "class {class} still offers it"
            );
            for held in rest.offered(class) {
                if *held != germ {
                    assert_eq!(
                        sibling.reaches(class, *held),
                        rest.reaches(class, *held),
                        "class {class} germ {held} moved and should not have"
                    );
                }
            }
        }
        assert!(sibling
            .metadata
            .get(INTERVENTION_KEY)
            .expect("the sibling declares itself")
            .contains("withdraw the germ family"));
    }

    /// The band is read off the target's own height, so a transition survives exactly when its
    /// target sits outside the band.
    #[test]
    fn the_height_band_withdrawal_removes_exactly_the_transitions_into_that_band() {
        let rest = intervention_fixture();
        let heights = class_heights(&rest);
        let (sibling, receipt) = intervene(
            &rest,
            &RestIntervention::WithdrawHeightBand { low: 2, high: 2 },
        )
        .expect("intervened");
        assert!(
            !receipt.withdrawn.is_empty(),
            "the fixture must carry transitions into height 2"
        );
        for (_, _, target) in &receipt.withdrawn {
            assert_eq!(heights[*target as usize], 2);
        }
        for class in 0..rest.classes() as u32 {
            for held in sibling.offered(class) {
                let target = sibling
                    .reaches(class, *held)
                    .expect("a row it just offered");
                assert_ne!(heights[target as usize], 2, "a banded target survived");
            }
        }
        assert_eq!(
            receipt.transitions_after + receipt.withdrawn.len(),
            receipt.transitions_before
        );
    }

    /// A transposition is matched: the transition population, every row length and the whole target
    /// multiset are unmoved, and only which germ reaches which continuation moves.
    #[test]
    fn the_germ_transposition_preserves_the_population_and_moves_the_adjacency() {
        let rest = intervention_fixture();
        let left = germ_index(&rest, "receiver");
        let right = germ_index(&rest, "chart");
        let (sibling, receipt) = intervene(
            &rest,
            &RestIntervention::TransposeGermLabels { left, right },
        )
        .expect("intervened");
        assert!(receipt.population_preserved);
        assert_eq!(receipt.transitions_before, receipt.transitions_after);
        assert!(receipt.withdrawn.is_empty());
        assert!(!receipt.relabelled.is_empty());
        assert_eq!(sibling.indptr, rest.indptr, "no row changed length");
        for class in 0..rest.classes() as u32 {
            assert_eq!(sibling.reaches(class, left), rest.reaches(class, right));
            assert_eq!(sibling.reaches(class, right), rest.reaches(class, left));
        }
        // Every row is ascending by germ index, which is the standing walk law's own requirement.
        for class in 0..sibling.classes() as u32 {
            let row = sibling.offered(class);
            assert!(
                row.windows(2).all(|pair| pair[0] < pair[1]),
                "class {class} is unsorted"
            );
        }
        // An involution: transposing twice returns the transport itself.
        let (back, _) = intervene(
            &sibling,
            &RestIntervention::TransposeGermLabels { left, right },
        )
        .expect("intervened");
        assert_eq!(back.germ, rest.germ);
        assert_eq!(back.target, rest.target);
        assert_eq!(back.indptr, rest.indptr);
    }

    /// The refusals are typed, and each names what it refused.
    #[test]
    fn an_intervention_outside_the_material_refuses_by_name() {
        let rest = intervention_fixture();
        let vocabulary = rest.vocabulary.len() as u64;
        assert!(intervene(
            &rest,
            &RestIntervention::WithdrawGermFamily { germ: vocabulary }
        )
        .is_err());
        assert!(intervene(
            &rest,
            &RestIntervention::TransposeGermLabels { left: 0, right: 0 }
        )
        .is_err());
        assert!(intervene(
            &rest,
            &RestIntervention::WithdrawHeightBand { low: 3, high: 1 }
        )
        .is_err());
    }

    /// **The withdrawal is visible at the conduct face, and unrelated conduct is bit-identical.**
    #[test]
    fn a_withdrawn_family_moves_the_conduct_that_reaches_it_and_leaves_the_rest_bit_identical() {
        let rest = intervention_fixture();
        let germ = germ_index(&rest, "grain");
        let (sibling, _) =
            intervene(&rest, &RestIntervention::WithdrawGermFamily { germ }).expect("intervened");
        let probe = "the receiver declares the";
        let tokens = lexical_tokens(probe);
        let base = conduct(&rest, probe, &tokens);
        let moved = conduct(&sibling, probe, &tokens);
        assert_ne!(
            base.face(),
            moved.face(),
            "the family was on this probe's ladder"
        );
        assert!(
            base.offered
                .iter()
                .any(|(surface, _, _)| surface == "grain"),
            "the base must offer the family being withdrawn"
        );
        assert!(
            !moved
                .offered
                .iter()
                .any(|(surface, _, _)| surface == "grain"),
            "no class offers a withdrawn family"
        );
    }

    /// **The whole law, end to end, on material small enough to read by hand.**
    ///
    /// The delta the return law derives, committed onto the predecessor container, is the container
    /// the transport itself emits — octet for octet.
    #[test]
    fn the_committed_delta_is_the_derived_one_and_reproduces_the_transport_octet_for_octet() {
        let (mut atlas, _) = atlas_of(&[
            "a chart is a receiver and the transport is a jacobian",
            "the receiver declares the grain it reads at",
        ]);
        let predecessor = emit_rest(&atlas, declarations()).expect("emitted");

        let tokens = lexical_tokens("a chart forgets a winding and the receiver keeps the turn");
        let path = token_germs_public(&tokens).expect("germs");
        let surfaces = surfaces_of(&path).expect("surfaces");

        let residual = read_residual(&predecessor, "development", &surfaces);
        let lineage = atlas.absorb_returning_lineage(&path).expect("absorbed");
        let incidence = DepositIncidence::of(&atlas, &lineage);
        let metric = MetricDeclaration::identity();
        let covector = unit_covector(&residual);
        let delta = derive(
            &predecessor,
            &residual,
            &lineage,
            &incidence,
            &metric,
            &covector,
            &surfaces,
        )
        .expect("derived");

        let committed = commit(&predecessor, &delta).expect("committed");
        let transported = emit_rest(&atlas, declarations()).expect("emitted");
        assert_eq!(
            committed.standing, transported.standing,
            "the adjoint image must BE the transport's own occupancy, not a number beside it"
        );
        assert_eq!(committed, transported, "the committed delta is the deposit");
        assert_eq!(
            committed.write_container().expect("container"),
            transported.write_container().expect("container"),
            "octet for octet"
        );
    }

    /// The delta withdraws in place and the predecessor returns, octet for octet.
    #[test]
    fn withdrawing_the_delta_returns_the_predecessor_octet_for_octet() {
        let (mut atlas, _) = atlas_of(&[
            "a chart is a receiver and the transport is a jacobian",
            "the receiver declares the grain it reads at",
        ]);
        let predecessor = emit_rest(&atlas, declarations()).expect("emitted");
        let tokens = lexical_tokens("a chart forgets a winding and the receiver keeps the turn");
        let path = token_germs_public(&tokens).expect("germs");
        let surfaces = surfaces_of(&path).expect("surfaces");
        let residual = read_residual(&predecessor, "development", &surfaces);
        let lineage = atlas.absorb_returning_lineage(&path).expect("absorbed");
        let incidence = DepositIncidence::of(&atlas, &lineage);
        let metric = MetricDeclaration::identity();
        let delta = derive(
            &predecessor,
            &residual,
            &lineage,
            &incidence,
            &metric,
            &unit_covector(&residual),
            &surfaces,
        )
        .expect("derived");
        let successor = commit(&predecessor, &delta).expect("committed");
        let ablated = withdraw(&successor, &delta).expect("withdrawn");
        assert_eq!(
            ablated.write_container().expect("container"),
            predecessor.write_container().expect("container"),
            "the targeted ablation restores the predecessor exactly"
        );
    }

    /// **The metric is read.** A declared receiver metric that weighs one residual species
    /// differently commits different increments; a metric the law never read could not.
    #[test]
    fn the_declared_metric_is_load_bearing_and_moves_the_committed_increments() {
        let (mut atlas, _) = atlas_of(&["a chart is a receiver and the transport is a jacobian"]);
        let predecessor = emit_rest(&atlas, declarations()).expect("emitted");
        let tokens = lexical_tokens("a chart forgets a winding");
        let path = token_germs_public(&tokens).expect("germs");
        let surfaces = surfaces_of(&path).expect("surfaces");
        let residual = read_residual(&predecessor, "development", &surfaces);
        let lineage = atlas.absorb_returning_lineage(&path).expect("absorbed");
        let incidence = DepositIncidence::of(&atlas, &lineage);
        let covector = unit_covector(&residual);

        let identity = MetricDeclaration::identity();
        let under_identity = derive(
            &predecessor,
            &residual,
            &lineage,
            &incidence,
            &identity,
            &covector,
            &surfaces,
        )
        .expect("derived");

        let mut perturbed = MetricDeclaration::identity();
        perturbed.name = "a receiver that weighs a refused continuation three".to_owned();
        perturbed.open_residual = rational(3, 1);
        let under_perturbed = derive(
            &predecessor,
            &residual,
            &lineage,
            &incidence,
            &perturbed,
            &covector,
            &surfaces,
        )
        .expect("derived");

        assert_ne!(
            under_identity.standing_increments, under_perturbed.standing_increments,
            "a metric the law never reads cannot move the deposit"
        );
        let moved = under_identity
            .standing_increments
            .iter()
            .filter(|(class, held)| under_perturbed.standing_increments.get(class) != Some(*held))
            .count();
        assert!(moved > 0, "the perturbation must move named classes");
    }

    /// A declared metric whose image leaves the integer carrier refuses by name.
    #[test]
    fn a_metric_that_leaves_the_integer_carrier_refuses_rather_than_rounding() {
        let (mut atlas, _) = atlas_of(&["a chart is a receiver"]);
        let predecessor = emit_rest(&atlas, declarations()).expect("emitted");
        let tokens = lexical_tokens("a chart forgets a winding");
        let path = token_germs_public(&tokens).expect("germs");
        let surfaces = surfaces_of(&path).expect("surfaces");
        let residual = read_residual(&predecessor, "development", &surfaces);
        let lineage = atlas.absorb_returning_lineage(&path).expect("absorbed");
        let incidence = DepositIncidence::of(&atlas, &lineage);
        let mut half = MetricDeclaration::identity();
        half.name = "a receiver that halves every returned difference".to_owned();
        half.open_residual = rational(1, 2);
        half.ride = rational(1, 2);
        half.open_included = rational(1, 2);
        half.none = rational(1, 2);
        let refusal = derive(
            &predecessor,
            &residual,
            &lineage,
            &incidence,
            &half,
            &unit_covector(&residual),
            &surfaces,
        );
        assert!(
            matches!(refusal, Err(CultivationRefusal::NonIntegralDeposit { .. })),
            "got {refusal:?}"
        );
    }

    /// **The residual is a reading and mutates nothing** — the still control's mechanism.
    #[test]
    fn reading_a_residual_leaves_the_rest_octet_identical() {
        let (atlas, _) = atlas_of(&["a chart is a receiver and the transport is a jacobian"]);
        let rest = emit_rest(&atlas, declarations()).expect("emitted");
        let before = rest.write_container().expect("container");
        let tokens = lexical_tokens("an unrelated hardware audit measures a card");
        let path = token_germs_public(&tokens).expect("germs");
        let surfaces = surfaces_of(&path).expect("surfaces");
        let residual = read_residual(&rest, "subject-disjoint", &surfaces);
        assert!(!residual.positions.is_empty());
        assert_eq!(before, rest.write_container().expect("container"));
    }

    /// **Re-exposing material the rest already carries founds no transport.** The occupancy still
    /// moves, and that is the law's own face rather than an exception to it.
    #[test]
    fn re_exposing_standing_material_is_structurally_empty_and_moves_only_the_occupancy() {
        let text = "a chart is a receiver and the transport is a jacobian";
        let (mut atlas, _) = atlas_of(&[text]);
        let predecessor = emit_rest(&atlas, declarations()).expect("emitted");
        let tokens = lexical_tokens(text);
        let path = token_germs_public(&tokens).expect("germs");
        let surfaces = surfaces_of(&path).expect("surfaces");
        let residual = read_residual(&predecessor, "no-op", &surfaces);
        assert!(
            residual.structurally_empty(),
            "a verbatim re-exposure founds no germ and refuses nowhere: {:?} {:?}",
            residual.novel_germs,
            residual.refusals
        );
        let lineage = atlas.absorb_returning_lineage(&path).expect("absorbed");
        let incidence = DepositIncidence::of(&atlas, &lineage);
        let delta = derive(
            &predecessor,
            &residual,
            &lineage,
            &incidence,
            &MetricDeclaration::identity(),
            &unit_covector(&residual),
            &surfaces,
        )
        .expect("derived");
        // **The founding law is `found where the class did not offer`, and a class does not offer in
        // exactly two ways — it offers a family without this germ (`OpenResidual`) or it offers
        // nothing at all (`None`). A verbatim re-exposure produces none of the first: every
        // founding it makes is at a TERMINUS, and every terminus here is a class whose longest
        // string ends in the previous path's separator. That is the chronology's own seam, caused
        // by the separator rather than by the material, and it is reported rather than hidden.
        let inside: Vec<&FoundedTransition> = delta
            .transitions_founded
            .iter()
            .filter(|row| row.on_standing_class && !predecessor.offered(row.class).is_empty())
            .collect();
        assert!(
            inside.is_empty(),
            "a verbatim re-exposure founds nothing inside the material's own transport: {inside:?}"
        );
        let seam = delta.transitions_founded_on_standing();
        assert!(
            seam > 0,
            "the separator's seam is real and must be visible rather than assumed away"
        );
        assert!(delta.germs_founded.is_empty());
        assert!(
            !delta.standing_increments.is_empty(),
            "the occupancy moves: the material occurred again"
        );
        let committed = commit(&predecessor, &delta).expect("committed");
        assert_eq!(
            committed.write_container().expect("container"),
            emit_rest(&atlas, declarations())
                .expect("emitted")
                .write_container()
                .expect("container")
        );
    }

    /// **Every founded transition inside the standing body is licensed by a refusal the residual
    /// recorded.** This is the derivation's own falsifier: a founding with no refusal behind it
    /// would be a delta the residual did not cause.
    #[test]
    fn every_founding_inside_the_standing_body_names_a_refusal_the_residual_recorded() {
        let (mut atlas, _) = atlas_of(&["a chart is a receiver and the transport is a jacobian"]);
        let predecessor = emit_rest(&atlas, declarations()).expect("emitted");
        let tokens = lexical_tokens("a chart forgets a winding and the receiver keeps the turn");
        let path = token_germs_public(&tokens).expect("germs");
        let surfaces = surfaces_of(&path).expect("surfaces");
        let residual = read_residual(&predecessor, "development", &surfaces);
        let lineage = atlas.absorb_returning_lineage(&path).expect("absorbed");
        let incidence = DepositIncidence::of(&atlas, &lineage);
        let delta = derive(
            &predecessor,
            &residual,
            &lineage,
            &incidence,
            &MetricDeclaration::identity(),
            &unit_covector(&residual),
            &surfaces,
        )
        .expect("derived");
        for row in delta
            .transitions_founded
            .iter()
            .filter(|row| row.on_standing_class)
        {
            assert!(
                predecessor
                    .vocabulary
                    .iter()
                    .position(|surface| *surface == row.germ)
                    .and_then(|germ| predecessor.reaches(row.class, germ as u64))
                    .is_none(),
                "class {} already offered {:?}; it cannot be founded",
                row.class,
                row.germ
            );
        }
    }

    /// **The grain, measured rather than asserted.** The standing transduction owner's route
    /// population over one octet consequence is exponential in its extent, which is why the atlas
    /// grain is a different owner rather than a rival to it.
    #[test]
    fn the_octet_route_population_is_exponential_so_the_atlas_grain_is_a_different_owner() {
        let faces = vec![SourceFace::new(FaceAddress::new("germ", 0), b"a".to_vec())];
        let mut population = Vec::new();
        for extent in 1..=12usize {
            let consequence = vec![b'a'; extent];
            let complex = consequence_complex(&faces, &consequence).expect("complex");
            population.push(
                derive_templates(&complex, 1 << 20)
                    .expect("templates")
                    .len(),
            );
        }
        assert_eq!(
            population,
            (1..=12).map(|extent| 1usize << extent).collect::<Vec<_>>(),
            "the route population doubles with every octet: {population:?}"
        );
    }
}
