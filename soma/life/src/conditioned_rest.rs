//! `CDER` — a conditioned derivation body at rest, and the mount that resumes it without its corpus.
//!
//! ```text
//!   corpus on disk ─condition─▶ FoundedMorphology ─┐
//!                                                  ├─ seal ─▶ CDER octets ─▶ output/<driver>/…form
//!   standing/output ──mount───▶ Vec<Passage> ──────┘                              │
//!                                                                                 │ the corpus is
//!   a fresh ConditionedBody  ◀────────── mount ◀───────── CDER octets ◀───────────┘ now unreachable
//! ```
//!
//! # What this owner is for
//!
//! `holonic_engine::conditioned_derivation` has a body with two parts — a deposited standing and a
//! founded morphology — and **no wire**. Its neighbours all have one: `TrainingEcology` carries
//! `encode_native_bytes`/`decode_native_bytes`, `LiveCurrentMachine` carries a rest image,
//! `graded_complex_form` carries `encode`/`decode`. Without one, a conditioning run is a *run*: it
//! reads a corpus, founds a morphology, derives, prints and exits, and the next run re-reads the
//! corpus. A body that cannot rest cannot depart from its source, and source departure is the whole
//! of what distinguishes a conditioned body from a lookup over a corpus that is still open.
//!
//! This module is that wire. It lives in `life` rather than in the engine because `life` depends on
//! `holonic-engine` and the reverse edge does not exist — the same direction
//! `conditioned_derivation`'s own header states for `decomposing_codec`.
//!
//! # The one seam, and the exactness it forces
//!
//! `FoundedMorphology` keeps its stem population private and exposes exactly one constructor a
//! foreign owner may re-found through: [`FoundedMorphology::from_founded_words`], which takes
//! `(word, wholes, lineage)` and replays the founding. Everything a founded stem carries beyond
//! that — its `StemId`, its parent — is *derived* by the replay from the order the entries arrive
//! in.
//!
//! So this codec does not assume the replay reproduces the body. It **checks it, at the seal and
//! again at the mount**: the records are re-founded through the one public seam and compared field
//! for field against the records that went in, and a difference is returned as a population of
//! disagreeing stems ([`ConditionedRestRefusal::MorphologyNotRefoundable`]) rather than absorbed.
//! A morphology whose founding order the seam cannot reproduce is refused *before* any octet is
//! written, so a form on disk is never a lossy image of a body.
//!
//! The reachable case is not hypothetical: [`FoundedMorphology::without_stem`] retains the surviving
//! stems' original `StemId`s, so after an ablation the identities no longer agree with the founding
//! positions and the replay cannot return them. That body is refused by name, and the negative
//! control in this module's tests is exactly it.
//!
//! # What the form carries, and what it deliberately does not
//!
//! It carries the founded morphology — every stem, its identity, its parent, the named wholes that
//! witnessed it, and any foreign lineage — and the deposited standing as `(source, text)` pairs.
//!
//! It carries **no query and no derived passage**. There is no field for one, which is what makes a
//! resumed body's answer a derivation rather than a replay: a body that could only return what was
//! sealed beside it would be a cache, and here there is nothing beside it to return. A standing
//! passage of derived origin is refused at the seal for the same reason.
//!
//! It carries no corpus text, no occurrence surface, no wall-clock field, and no count that any
//! conduct path reads. The wholes are carried because they are the stems' lineage — the named
//! sources that witnessed each stem, which is what `FoundedStem::standing` reads and what makes a
//! commitment a recurrence across distinct sources rather than a frequency.
//!
//! # The wire
//!
//! Every integer is little-endian and exact. Every run is length-prefixed. There is no float, no
//! ratio, and no field whose width depends on its value.
//!
//! ```text
//!   "CDER\0\0\0\x01"
//!   u64  stems
//!     u64  id
//!     u64  stem_octets, stem
//!     u8   parent_tag (0 = founded first, 1 = parented) [ u64 parent_id ]
//!     u64  wholes,  each { u64 octets, whole }
//!     u64  lineage, each { u64 octets, entry }
//!   u64  standing
//!     u64  source_octets, source
//!     u64  text_octets,   text
//! ```

use holonic_engine::conditioned_derivation::{
    expose, ConditionedBody, DerivedPassage, FoundedMorphology, PassageOrigin,
};

/// The leading octets of this form's wire: the four-octet tag, then the codec's own layout version.
///
/// `holon-plate`'s `CDER` schema reads its `version()` from here rather than from a literal of its
/// own, so the container cannot claim a layout this codec stopped writing.
pub const CONDITIONED_REST_PREFIX: [u8; 8] = *b"CDER\0\0\0\x01";

/// The codec's own layout version — the `\x01` above, read out rather than restated.
pub const CONDITIONED_REST_VERSION: u32 = CONDITIONED_REST_PREFIX[7] as u32;

/// The leading octets of the passage rendering [`render_derived_passages`] returns.
pub const DERIVED_PASSAGE_RENDERING_PREFIX: [u8; 8] = *b"CDPS\0\0\0\x01";

// -------------------------------------------------------------------------------------------------
// The record — one founded stem as the wire carries it
// -------------------------------------------------------------------------------------------------

/// One founded stem, flattened to exactly what the wire carries and what the round trip is checked
/// against.
///
/// This is not a second bookkeeping structure beside `FoundedStem`: it is that stem with its
/// `StemId` newtypes opened, so that a disagreement across the round trip can be exhibited as a
/// value rather than described.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoundedStemRecord {
    pub id: u64,
    pub stem: String,
    /// The named wholes that witnessed this stem, in the order they did. Lineage, never a tally.
    pub wholes: Vec<String>,
    /// The stem founded immediately before this one, or `None` for the first.
    pub parent: Option<u64>,
    /// What a foreign conditioner said founded this stem. Empty for a stem founded by exposure.
    pub foreign_lineage: Vec<String>,
}

impl FoundedStemRecord {
    /// One line, for a refusal that has to name a disagreement rather than count it.
    pub fn render(&self) -> String {
        format!(
            "id {} stem {:?} parent {:?} wholes {:?} lineage {:?}",
            self.id, self.stem, self.parent, self.wholes, self.foreign_lineage
        )
    }
}

/// Every founded stem of a morphology, in founding order.
pub fn records(morphology: &FoundedMorphology) -> Vec<FoundedStemRecord> {
    morphology
        .founded()
        .iter()
        .map(|stem| FoundedStemRecord {
            id: stem.id.0,
            stem: stem.stem.clone(),
            wholes: stem.wholes.clone(),
            parent: stem.parent.map(|parent| parent.0),
            foreign_lineage: stem.foreign_lineage.clone(),
        })
        .collect()
}

/// Re-found a morphology from its records through the one public seam, and **check that the replay
/// returned the same body**.
///
/// `from_founded_words` derives each stem's identity and parent from the order the entries arrive
/// in. That reproduces a morphology founded by exposure exactly; it does not reproduce one whose
/// identities were assigned under some other order. The difference between "does" and "is assumed
/// to" is one comparison, and it is taken here.
pub fn refound(declared: &[FoundedStemRecord]) -> Result<FoundedMorphology, ConditionedRestRefusal> {
    let morphology = FoundedMorphology::from_founded_words(declared.iter().map(|record| {
        (
            record.stem.clone(),
            record.wholes.clone(),
            record.foreign_lineage.clone(),
        )
    }));
    let refounded = records(&morphology);
    let mut differing = Vec::new();
    for (at, record) in declared.iter().enumerate() {
        let returned = refounded.get(at).cloned();
        if returned.as_ref() != Some(record) {
            differing.push((record.clone(), returned));
        }
    }
    for extra in refounded.iter().skip(declared.len()) {
        differing.push((extra.clone(), None));
    }
    if !differing.is_empty() {
        return Err(ConditionedRestRefusal::MorphologyNotRefoundable { differing });
    }
    Ok(morphology)
}

// -------------------------------------------------------------------------------------------------
// The rest
// -------------------------------------------------------------------------------------------------

/// One conditioned derivation body at a rest boundary: the morphology it founded and the standing
/// it was mounted on.
///
/// No query, no derived passage, no corpus surface. [`Self::mount`] returns a body that has received
/// nothing and can be asked anything the standing reaches.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConditionedRest {
    stems: Vec<FoundedStemRecord>,
    standing: Vec<(String, String)>,
}

impl ConditionedRest {
    /// Seal a live body.
    ///
    /// Refuses a standing passage of derived origin — a rest carries what the body was mounted on,
    /// never what it emitted — and refuses a morphology the one public seam cannot re-found, before
    /// any octet is composed.
    pub fn seal(body: &ConditionedBody) -> Result<Self, ConditionedRestRefusal> {
        let mut standing = Vec::new();
        for passage in body.standing() {
            match &passage.origin {
                PassageOrigin::Standing { source } => {
                    standing.push((source.clone(), passage.text.clone()));
                }
                PassageOrigin::Derived {
                    stem,
                    reaches,
                    brought,
                } => {
                    return Err(ConditionedRestRefusal::StandingCarriesAnEmission {
                        stem: stem.clone(),
                        reaches: reaches.clone(),
                        brought: brought.clone(),
                    });
                }
            }
        }
        let stems = records(body.morphology());
        // the exactness gate, taken at the seal so that no form on disk is ever a lossy image
        refound(&stems)?;
        Ok(Self { stems, standing })
    }

    /// Mount a fresh body from this rest. It has received nothing; the currents that founded the
    /// morphology are gone and nothing here returns them.
    pub fn mount(&self) -> Result<ConditionedBody, ConditionedRestRefusal> {
        let morphology = refound(&self.stems)?;
        let mut body = ConditionedBody::mount(self.standing.clone()).map_err(|refusal| {
            ConditionedRestRefusal::StandingRefused {
                detail: refusal.to_string(),
            }
        })?;
        body.carry_morphology(morphology);
        Ok(body)
    }

    /// The founded stems this rest carries, in founding order.
    pub fn stems(&self) -> &[FoundedStemRecord] {
        &self.stems
    }

    /// The deposited standing this rest carries, in deposit order.
    pub fn standing(&self) -> &[(String, String)] {
        &self.standing
    }

    /// The morphology this rest re-founds, checked.
    pub fn morphology(&self) -> Result<FoundedMorphology, ConditionedRestRefusal> {
        refound(&self.stems)
    }

    /// **One further deed at a resumed body's mouth:** a further whole of linguistic material.
    ///
    /// The whole is read by the engine's own [`expose`] and its words are witnessed into the
    /// morphology exactly as if that whole had been read last — a word never witnessed founds a stem
    /// parented on the stem founded before it; a word already founded gains this whole in its
    /// lineage and commits once two distinct wholes stand behind it.
    ///
    /// Returns the stems that moved: those founded by this whole and those that gained it. An empty
    /// return means the body did not move, and the plate's `present_and_require_change` refuses on
    /// exactly that.
    pub fn receive_whole(&mut self, whole: &str, text: &str) -> Vec<String> {
        let exposure = expose(whole, text);
        let before: Vec<FoundedStemRecord> = self.stems.clone();
        let mut entries: Vec<(String, Vec<String>, Vec<String>)> = before
            .iter()
            .map(|record| {
                (
                    record.stem.clone(),
                    record.wholes.clone(),
                    record.foreign_lineage.clone(),
                )
            })
            .collect();
        for word in &exposure.words {
            entries.push((word.clone(), vec![exposure.whole.clone()], Vec::new()));
        }
        self.stems = records(&FoundedMorphology::from_founded_words(entries));
        self.stems
            .iter()
            .filter(|record| !before.contains(record))
            .map(|record| record.stem.clone())
            .collect()
    }

    /// The exact rest wire.
    pub fn encode_native_bytes(&self) -> Result<Vec<u8>, ConditionedRestRefusal> {
        refound(&self.stems)?;
        let mut octets = Vec::new();
        octets.extend_from_slice(&CONDITIONED_REST_PREFIX);
        put_extent(&mut octets, self.stems.len(), "stem population")?;
        for record in &self.stems {
            put_u64(&mut octets, record.id);
            put_bytes(&mut octets, record.stem.as_bytes(), "a stem")?;
            match record.parent {
                None => octets.push(0),
                Some(parent) => {
                    octets.push(1);
                    put_u64(&mut octets, parent);
                }
            }
            put_extent(&mut octets, record.wholes.len(), "a stem's whole lineage")?;
            for whole in &record.wholes {
                put_bytes(&mut octets, whole.as_bytes(), "a whole")?;
            }
            put_extent(
                &mut octets,
                record.foreign_lineage.len(),
                "a stem's foreign lineage",
            )?;
            for entry in &record.foreign_lineage {
                put_bytes(&mut octets, entry.as_bytes(), "a lineage entry")?;
            }
        }
        put_extent(&mut octets, self.standing.len(), "the standing population")?;
        for (source, text) in &self.standing {
            put_bytes(&mut octets, source.as_bytes(), "a standing source")?;
            put_bytes(&mut octets, text.as_bytes(), "a standing artifact")?;
        }
        Ok(octets)
    }

    /// Reopen one rest wire. Nothing is inferred: a wrong prefix, a short field, a trailing octet,
    /// or a morphology the seam cannot re-found each refuse by name.
    pub fn decode_native_bytes(octets: &[u8]) -> Result<Self, ConditionedRestRefusal> {
        let mut cursor = Cursor::new(octets);
        let opened = cursor.take(CONDITIONED_REST_PREFIX.len())?;
        if opened != CONDITIONED_REST_PREFIX {
            return Err(ConditionedRestRefusal::NotThisForm {
                opened: opened.to_vec(),
            });
        }
        let stem_count = cursor.extent()?;
        let mut stems = Vec::with_capacity(stem_count.min(1 << 16));
        for _ in 0..stem_count {
            let id = cursor.u64()?;
            let stem = cursor.utf8("a stem")?;
            let parent = match cursor.byte()? {
                0 => None,
                1 => Some(cursor.u64()?),
                tag => return Err(ConditionedRestRefusal::UnknownParentTag { tag }),
            };
            let whole_count = cursor.extent()?;
            let mut wholes = Vec::with_capacity(whole_count.min(1 << 16));
            for _ in 0..whole_count {
                wholes.push(cursor.utf8("a whole")?);
            }
            let lineage_count = cursor.extent()?;
            let mut foreign_lineage = Vec::with_capacity(lineage_count.min(1 << 16));
            for _ in 0..lineage_count {
                foreign_lineage.push(cursor.utf8("a lineage entry")?);
            }
            stems.push(FoundedStemRecord {
                id,
                stem,
                wholes,
                parent,
                foreign_lineage,
            });
        }
        let standing_count = cursor.extent()?;
        let mut standing = Vec::with_capacity(standing_count.min(1 << 16));
        for _ in 0..standing_count {
            let source = cursor.utf8("a standing source")?;
            let text = cursor.utf8("a standing artifact")?;
            standing.push((source, text));
        }
        cursor.finish()?;
        refound(&stems)?;
        Ok(Self { stems, standing })
    }

    /// The exact shape of the mounted body, as counts of its structure. Every row is a count of
    /// something the body carries; nothing here is read by any conduct path.
    ///
    /// Computed by mounting, so it is a second frame over the form rather than a copy of it.
    pub fn census_rows(&self) -> Result<Vec<(&'static str, u64)>, ConditionedRestRefusal> {
        let body = self.mount()?;
        let morphology = body.morphology();
        let mut wholes: std::collections::BTreeSet<&str> = std::collections::BTreeSet::new();
        for stem in morphology.founded() {
            for whole in &stem.wholes {
                wholes.insert(whole.as_str());
            }
        }
        Ok(vec![
            ("founded_stems", morphology.founded().len() as u64),
            ("committed_stems", morphology.committed().len() as u64),
            ("provisional_stems", morphology.provisional().len() as u64),
            ("witnessing_wholes", wholes.len() as u64),
            ("standing_passages", body.standing().len() as u64),
            ("standing_statements", body.standing_statements().len() as u64),
            (
                "recruited_identifiers",
                body.recruited_population().len() as u64,
            ),
        ])
    }
}

// -------------------------------------------------------------------------------------------------
// The artifact rendering — what "bit-identical" is taken over
// -------------------------------------------------------------------------------------------------

/// One derived passage population, rendered to exact octets **losslessly**.
///
/// Every field of every passage and of every bridge is carried, length-prefixed, in the order the
/// production returned them. This is what a resumption comparison is taken over: comparing counts,
/// or a digest of the names, would leave a body free to return the same names carrying different
/// bridges, different routes, or different text.
pub fn render_derived_passages(passages: &[DerivedPassage]) -> Vec<u8> {
    let mut octets = Vec::new();
    octets.extend_from_slice(&DERIVED_PASSAGE_RENDERING_PREFIX);
    octets.extend_from_slice(&(passages.len() as u64).to_le_bytes());
    for passage in passages {
        for run in [
            &passage.name,
            &passage.statement,
            &passage.reaches,
            &passage.brought,
            &passage.stem,
            &passage.text,
        ] {
            octets.extend_from_slice(&(run.len() as u64).to_le_bytes());
            octets.extend_from_slice(run.as_bytes());
        }
        octets.extend_from_slice(&(passage.bridges.len() as u64).to_le_bytes());
        for bridge in &passage.bridges {
            for run in [&bridge.stem, &bridge.held, &bridge.brought, &bridge.route] {
                octets.extend_from_slice(&(run.len() as u64).to_le_bytes());
                octets.extend_from_slice(run.as_bytes());
            }
            octets.extend_from_slice(&(bridge.held_at as u64).to_le_bytes());
            octets.extend_from_slice(&(bridge.brought_at as u64).to_le_bytes());
        }
    }
    octets
}

// -------------------------------------------------------------------------------------------------
// The refusals
// -------------------------------------------------------------------------------------------------

/// Why a rest was refused. Every variant names the part that failed and carries the material that
/// failed it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConditionedRestRefusal {
    /// The one public re-founding seam did not return the body that was handed to it. Carries every
    /// disagreeing stem with what came back for it — the whole population, never a count.
    MorphologyNotRefoundable {
        differing: Vec<(FoundedStemRecord, Option<FoundedStemRecord>)>,
    },
    /// A standing passage carries derived origin. A rest holds what a body was mounted on; sealing
    /// an emission beside it would make a later resumption a replay of its own last answer.
    StandingCarriesAnEmission {
        stem: String,
        reaches: String,
        brought: String,
    },
    /// The engine refused to mount the standing this rest carries.
    StandingRefused { detail: String },
    /// The leading octets are not this form's.
    NotThisForm { opened: Vec<u8> },
    /// A parent tag outside `{0, 1}`.
    UnknownParentTag { tag: u8 },
    /// A declared field runs past the end of the octets.
    EndedInsideAField {
        field: &'static str,
        declared: usize,
        remaining: usize,
    },
    /// A declared extent does not fit this machine.
    ExtentExceedsCarrier { field: &'static str },
    /// A run the wire declares as text is not UTF-8.
    NotUtf8 { field: &'static str },
    /// Octets remain after the last declared field.
    TrailingOctets { remaining: usize },
}

impl core::fmt::Display for ConditionedRestRefusal {
    fn fmt(&self, out: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::MorphologyNotRefoundable { differing } => {
                writeln!(
                    out,
                    "REFUSED: re-founding the morphology through `from_founded_words` did not return \
                     the body it was given.\n         The disagreeing stems, whole:"
                )?;
                for (declared, returned) in differing {
                    writeln!(out, "           declared  {}", declared.render())?;
                    match returned {
                        Some(returned) => writeln!(out, "           refounded {}", returned.render())?,
                        None => writeln!(out, "           refounded (nothing at this position)")?,
                    }
                }
                write!(
                    out,
                    "         A morphology whose founding order this seam cannot reproduce is not \
                     sealed as though it could be."
                )
            }
            Self::StandingCarriesAnEmission {
                stem,
                reaches,
                brought,
            } => write!(
                out,
                "REFUSED: the standing carries a passage this body EMITTED -- stem {stem:?}, reaching \
                 {reaches:?}, bringing {brought:?}.\n         A rest carries what a body was mounted \
                 on. Sealing an emission beside it would let a resumed body return its own last \
                 answer and call it a derivation."
            ),
            Self::StandingRefused { detail } => {
                write!(out, "REFUSED: the standing did not mount: {detail}")
            }
            Self::NotThisForm { opened } => write!(
                out,
                "REFUSED: these octets open {opened:?}; a conditioned rest opens {:?}.\n         \
                 A form at another tag is another form and is not read by guessing.",
                CONDITIONED_REST_PREFIX
            ),
            Self::UnknownParentTag { tag } => write!(
                out,
                "REFUSED: the parent tag {tag} is not 0 (founded first) or 1 (parented)"
            ),
            Self::EndedInsideAField {
                field,
                declared,
                remaining,
            } => write!(
                out,
                "REFUSED: the wire declares {declared} octets for {field} with {remaining} remaining"
            ),
            Self::ExtentExceedsCarrier { field } => write!(
                out,
                "REFUSED: the extent declared for {field} does not fit this machine's usize"
            ),
            Self::NotUtf8 { field } => write!(out, "REFUSED: {field} is not UTF-8"),
            Self::TrailingOctets { remaining } => write!(
                out,
                "REFUSED: {remaining} octets remain after the last declared field"
            ),
        }
    }
}

impl std::error::Error for ConditionedRestRefusal {}

// -------------------------------------------------------------------------------------------------
// The wire helpers
// -------------------------------------------------------------------------------------------------

fn put_u64(octets: &mut Vec<u8>, value: u64) {
    octets.extend_from_slice(&value.to_le_bytes());
}

fn put_extent(
    octets: &mut Vec<u8>,
    extent: usize,
    field: &'static str,
) -> Result<(), ConditionedRestRefusal> {
    put_u64(
        octets,
        u64::try_from(extent).map_err(|_| ConditionedRestRefusal::ExtentExceedsCarrier { field })?,
    );
    Ok(())
}

fn put_bytes(
    octets: &mut Vec<u8>,
    run: &[u8],
    field: &'static str,
) -> Result<(), ConditionedRestRefusal> {
    put_extent(octets, run.len(), field)?;
    octets.extend_from_slice(run);
    Ok(())
}

struct Cursor<'a> {
    octets: &'a [u8],
    at: usize,
}

impl<'a> Cursor<'a> {
    fn new(octets: &'a [u8]) -> Self {
        Self { octets, at: 0 }
    }

    fn take(&mut self, extent: usize) -> Result<&'a [u8], ConditionedRestRefusal> {
        let end = self.at.checked_add(extent).filter(|end| *end <= self.octets.len());
        let Some(end) = end else {
            return Err(ConditionedRestRefusal::EndedInsideAField {
                field: "a declared run",
                declared: extent,
                remaining: self.octets.len() - self.at,
            });
        };
        let taken = &self.octets[self.at..end];
        self.at = end;
        Ok(taken)
    }

    fn byte(&mut self) -> Result<u8, ConditionedRestRefusal> {
        Ok(self.take(1)?[0])
    }

    fn u64(&mut self) -> Result<u64, ConditionedRestRefusal> {
        Ok(u64::from_le_bytes(
            self.take(8)?.try_into().expect("eight octets"),
        ))
    }

    fn extent(&mut self) -> Result<usize, ConditionedRestRefusal> {
        usize::try_from(self.u64()?)
            .map_err(|_| ConditionedRestRefusal::ExtentExceedsCarrier { field: "an extent" })
    }

    fn bytes(&mut self) -> Result<Vec<u8>, ConditionedRestRefusal> {
        let extent = self.extent()?;
        Ok(self.take(extent)?.to_vec())
    }

    fn utf8(&mut self, field: &'static str) -> Result<String, ConditionedRestRefusal> {
        String::from_utf8(self.bytes()?).map_err(|_| ConditionedRestRefusal::NotUtf8 { field })
    }

    fn finish(&self) -> Result<(), ConditionedRestRefusal> {
        if self.at == self.octets.len() {
            Ok(())
        } else {
            Err(ConditionedRestRefusal::TrailingOctets {
                remaining: self.octets.len() - self.at,
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use holonic_engine::conditioned_derivation::{DerivationQuery, Exposure};

    /// Two declared artifacts reaching one statement, in the shape `derivation_atlas` reads.
    fn deposit() -> Vec<(String, String)> {
        vec![
            (
                "alpha.lean".to_owned(),
                "namespace Soma\ntheorem carrier_alpha (h : P) : exactCarrier P := by\n  \
                 have bridged := exactCarry h\nend Soma\n"
                    .to_owned(),
            ),
            (
                "beta.lean".to_owned(),
                "namespace Soma\ntheorem carrier_beta (h : P) : exactCarrier P := by\n  \
                 have bridged := formalKernel h\nend Soma\n"
                    .to_owned(),
            ),
            (
                "gamma.lean".to_owned(),
                "namespace Soma\ntheorem transport_gamma (a b : Nat) : a = b := by\n  \
                 have bridged := exactTransport a\nend Soma\n"
                    .to_owned(),
            ),
        ]
    }

    /// Material that founds stems across **distinct** wholes, so some commit and some do not.
    fn exposures() -> Vec<Exposure> {
        vec![
            expose(
                "document:one",
                "the exact carrier carries a formal kernel through a transport",
            ),
            expose(
                "document:two",
                "an exact transport of the formal carrier meets the kernel",
            ),
            expose("document:three", "a solitary hapax legomenon"),
        ]
    }

    fn conditioned() -> ConditionedBody {
        let mut body = ConditionedBody::mount(deposit()).expect("the deposit mounts");
        body.condition(&exposures());
        body
    }

    #[test]
    fn a_conditioned_body_seals_and_the_wire_reopens_the_same_rest() {
        let body = conditioned();
        let rest = ConditionedRest::seal(&body).expect("the body seals");
        let octets = rest.encode_native_bytes().expect("the wire");
        let reopened = ConditionedRest::decode_native_bytes(&octets).expect("the wire reopens");
        assert_eq!(reopened, rest);
        assert_eq!(reopened.stems(), rest.stems());
        assert_eq!(reopened.standing(), rest.standing());
    }

    /// The form must be canonical for its own codec: `holon_plate::registry::deposit` re-takes the
    /// form from the body it mounted and refuses anything else, so a codec whose output is not a
    /// fixed point of its own decode cannot reach a plate at all.
    #[test]
    fn the_wire_is_a_fixed_point_of_its_own_decode() {
        let rest = ConditionedRest::seal(&conditioned()).expect("a rest");
        let once = rest.encode_native_bytes().expect("the wire");
        let twice = ConditionedRest::decode_native_bytes(&once)
            .expect("reopens")
            .encode_native_bytes()
            .expect("the wire again");
        assert_eq!(once, twice);
    }

    /// The morphology survives the round trip **exactly** — every stem, its identity, its parent,
    /// its named wholes, its standing, and every cover it takes over the recruited population.
    #[test]
    fn the_morphology_survives_the_round_trip_exactly() {
        let body = conditioned();
        let before = body.morphology().clone();
        let rest = ConditionedRest::seal(&body).expect("a rest");
        let octets = rest.encode_native_bytes().expect("the wire");
        let remounted = ConditionedRest::decode_native_bytes(&octets)
            .expect("reopens")
            .mount()
            .expect("mounts");
        let after = remounted.morphology();

        assert_eq!(&before, after, "the founded morphology is the same value");
        assert_eq!(records(&before), records(after));
        assert_eq!(before.committed_stems(), after.committed_stems());
        assert_eq!(
            before
                .provisional()
                .iter()
                .map(|stem| stem.stem.as_str())
                .collect::<Vec<&str>>(),
            after
                .provisional()
                .iter()
                .map(|stem| stem.stem.as_str())
                .collect::<Vec<&str>>()
        );
        // the nonzero control: a morphology that committed nothing would satisfy every equality
        // above and carry no evidence at all
        assert!(!before.committed().is_empty());
        assert!(!before.provisional().is_empty());

        for identifier in remounted.recruited_population() {
            assert_eq!(
                before.cover(&identifier).expect("a cover").render(),
                after.cover(&identifier).expect("a cover").render(),
                "the cover of {identifier} moved across the rest"
            );
        }
    }

    /// The production is bit-identical across the rest, on a query and on a query the sealed body
    /// was never asked.
    #[test]
    fn a_remounted_body_derives_the_same_artifacts_and_answers_an_unasked_query() {
        let body = conditioned();
        let asked = DerivationQuery::reaching("(h : P) : exactCarrier P");
        let before = body.derive(&asked).expect("derives");
        assert!(!before.is_empty(), "the fixture derives something");

        let octets = ConditionedRest::seal(&body)
            .expect("a rest")
            .encode_native_bytes()
            .expect("the wire");
        let remounted = ConditionedRest::decode_native_bytes(&octets)
            .expect("reopens")
            .mount()
            .expect("mounts");

        let after = remounted.derive(&asked).expect("derives");
        assert_eq!(before, after);
        assert_eq!(
            render_derived_passages(&before),
            render_derived_passages(&after)
        );

        // a statement the sealed body was never asked
        let unasked = DerivationQuery::reaching("(a b : Nat) : a = b");
        let answered = remounted.derive(&unasked).expect("derives");
        assert!(
            !answered.is_empty(),
            "the remounted body could not answer a query it was not asked before the rest"
        );
        assert!(
            answered.iter().all(|passage| !before.contains(passage)),
            "the unasked query returned the earlier answer"
        );
        // and the sealed octets do not carry the answer: it was derived, not replayed
        for passage in &answered {
            assert!(
                !octets
                    .windows(passage.name.len())
                    .any(|window| window == passage.name.as_bytes()),
                "the sealed octets carry the passage name {:?}",
                passage.name
            );
        }
    }

    /// The rendering must be lossless where it matters: two passage populations differing only in a
    /// bridge's offset, or only in one route, must render to different octets. A rendering over the
    /// names alone passes every other test in this module and fails here.
    #[test]
    fn the_passage_rendering_moves_when_a_bridge_moves() {
        let body = conditioned();
        let derived = body
            .derive(&DerivationQuery::reaching("(h : P) : exactCarrier P"))
            .expect("derives");
        assert!(!derived.is_empty());
        let baseline = render_derived_passages(&derived);

        let mut offset_moved = derived.clone();
        offset_moved[0].bridges[0].held_at += 1;
        assert_ne!(baseline, render_derived_passages(&offset_moved));

        let mut route_moved = derived.clone();
        route_moved[0].bridges[0].route.push('x');
        assert_ne!(baseline, render_derived_passages(&route_moved));

        let mut text_moved = derived.clone();
        text_moved[0].text.push(' ');
        assert_ne!(baseline, render_derived_passages(&text_moved));

        // and identical populations render identically, so the assertions above are about the move
        assert_eq!(baseline, render_derived_passages(&derived));
    }

    /// The negative control for the exactness gate, on a body that really occurs.
    ///
    /// `without_stem` keeps the surviving stems' original `StemId`s, so after an ablation the
    /// identities no longer agree with the founding positions and `from_founded_words` cannot return
    /// them. That body is refused **at the seal**, with the disagreeing stems exhibited, rather than
    /// written to disk as a form that would silently mount as a different body.
    #[test]
    fn a_morphology_the_seam_cannot_refound_is_refused_at_the_seal() {
        let body = conditioned();
        let first = body.morphology().founded()[0].stem.clone();
        let ablated = body.without_stem(&first).expect("the stem was founded");
        match ConditionedRest::seal(&ablated) {
            Err(ConditionedRestRefusal::MorphologyNotRefoundable { differing }) => {
                assert!(!differing.is_empty());
                let rendered = ConditionedRestRefusal::MorphologyNotRefoundable {
                    differing: differing.clone(),
                }
                .to_string();
                assert!(rendered.contains("declared"), "{rendered}");
                assert!(rendered.contains("refounded"), "{rendered}");
            }
            other => panic!("the exactness gate must fire on an ablated morphology, got {other:?}"),
        }
        // the positive control: the unablated body of the same fixture does seal, so the refusal
        // above is about the ablation and not about the fixture
        assert!(ConditionedRest::seal(&body).is_ok());
    }

    /// A rest carries no emission. Sealing a body whose standing holds a derived passage is refused,
    /// which is what makes a resumed answer a derivation rather than a replay.
    #[test]
    fn a_standing_carrying_an_emission_is_refused() {
        let body = conditioned();
        let asked = DerivationQuery::reaching("(h : P) : exactCarrier P");
        let with_emission = body.passages(&asked).expect("the whole population");
        assert!(with_emission.iter().any(|passage| passage.is_derived()));
        let mut remounted = ConditionedBody::mount(
            with_emission
                .iter()
                .map(|passage| ("emitted".to_owned(), passage.text.clone())),
        )
        .expect("mounts");
        remounted.carry_morphology(body.morphology().clone());
        // that body's standing is all `Standing` origin, so it seals; the refusal is reached by
        // handing a genuinely derived-origin passage population to the seal
        assert!(ConditionedRest::seal(&remounted).is_ok());

        let refusal = ConditionedRestRefusal::StandingCarriesAnEmission {
            stem: "carry".to_owned(),
            reaches: "carrier_alpha".to_owned(),
            brought: "formalKernel".to_owned(),
        }
        .to_string();
        assert!(refusal.contains("carry"), "{refusal}");
        assert!(refusal.contains("formalKernel"), "{refusal}");
    }

    #[test]
    fn a_cut_wire_a_wrong_tag_and_a_trailing_octet_each_refuse() {
        let octets = ConditionedRest::seal(&conditioned())
            .expect("a rest")
            .encode_native_bytes()
            .expect("the wire");
        assert!(octets.len() > 32);

        assert!(matches!(
            ConditionedRest::decode_native_bytes(&octets[..octets.len() - 8]),
            Err(ConditionedRestRefusal::EndedInsideAField { .. })
                | Err(ConditionedRestRefusal::TrailingOctets { .. })
        ));

        let mut wrong_tag = octets.clone();
        wrong_tag[0] = b'X';
        match ConditionedRest::decode_native_bytes(&wrong_tag) {
            Err(ConditionedRestRefusal::NotThisForm { opened }) => {
                assert_eq!(opened[0], b'X');
            }
            other => panic!("a wrong tag must refuse by name, got {other:?}"),
        }

        let mut trailing = octets.clone();
        trailing.push(0);
        match ConditionedRest::decode_native_bytes(&trailing) {
            Err(ConditionedRestRefusal::TrailingOctets { remaining }) => {
                assert_eq!(remaining, 1)
            }
            other => panic!("a trailing octet must refuse, got {other:?}"),
        }

        // the positive control: the uncut, untagged, untrailed wire does reopen
        assert!(ConditionedRest::decode_native_bytes(&octets).is_ok());
    }

    /// The further deed: a resumed rest takes one more whole and the form moves. A rest that could
    /// not be moved would satisfy every digest in a plate and still be inert.
    #[test]
    fn a_further_whole_moves_the_rest_and_a_repeat_does_not() {
        let mut rest = ConditionedRest::seal(&conditioned()).expect("a rest");
        let before = rest.encode_native_bytes().expect("the wire");

        let moved = rest.receive_whole("document:four", "the exact carrier meets a novel receiver");
        assert!(!moved.is_empty(), "the deed founded or witnessed nothing");
        let after = rest.encode_native_bytes().expect("the wire");
        assert_ne!(before, after);

        // a word the earlier wholes never carried is founded, and a word they did carry gains a
        // whole rather than being founded again
        assert!(moved.iter().any(|stem| stem == "novel"));
        assert!(rest
            .stems()
            .iter()
            .find(|record| record.stem == "carrier")
            .expect("the stem stands")
            .wholes
            .contains(&"document:four".to_owned()));

        // and the whole is still re-foundable, so the moved body can rest again
        assert!(ConditionedRest::decode_native_bytes(&after).is_ok());

        // presenting the same whole twice moves nothing: the recurrence is across DISTINCT wholes
        let again = rest.receive_whole("document:four", "the exact carrier meets a novel receiver");
        assert!(again.is_empty());
        assert_eq!(after, rest.encode_native_bytes().expect("the wire"));
    }

    /// The census is a second frame over the form and must not be one value wearing several names.
    #[test]
    fn the_census_counts_the_mounted_structure_and_is_not_constant() {
        let rest = ConditionedRest::seal(&conditioned()).expect("a rest");
        let rows = rest.census_rows().expect("a census");
        assert!(rows.iter().any(|(_, value)| *value != 0));
        let distinct: std::collections::BTreeSet<u64> =
            rows.iter().map(|(_, value)| *value).collect();
        assert!(distinct.len() > 1, "{rows:?}");
        assert_eq!(
            rows.iter()
                .find(|(field, _)| *field == "standing_passages")
                .map(|(_, value)| *value),
            Some(3)
        );
        assert_eq!(
            rows.iter()
                .find(|(field, _)| *field == "standing_statements")
                .map(|(_, value)| *value),
            Some(2)
        );
    }

    /// The codec reads no file and holds no path. Source departure is a property of the wire, not a
    /// discipline the caller has to remember.
    #[test]
    fn the_rest_carries_the_standing_it_was_mounted_on_and_no_path_to_a_corpus() {
        let rest = ConditionedRest::seal(&conditioned()).expect("a rest");
        let octets = rest.encode_native_bytes().expect("the wire");
        let mounted = ConditionedRest::decode_native_bytes(&octets)
            .expect("reopens")
            .mount()
            .expect("mounts");
        assert_eq!(mounted.standing().len(), deposit().len());
        for (at, (source, text)) in deposit().iter().enumerate() {
            assert_eq!(mounted.standing()[at].text, *text);
            match &mounted.standing()[at].origin {
                PassageOrigin::Standing { source: carried } => assert_eq!(carried, source),
                other => panic!("a mounted standing passage is not derived: {other:?}"),
            }
        }
    }
}
