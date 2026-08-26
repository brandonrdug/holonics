//! **The rest is mounted alone: conducted, deposited into, and re-sealed, with no corpus and no
//! source anywhere in the path.**
//!
//! Deed P4 of `blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md` §8.
//!
//! # Why this owner exists, stated as the absent edge rather than as a new faculty
//!
//! [`crate::atlas_cultivation`] owns the whole cultivation law — residual, deposit, derive, commit,
//! withdraw — and [`crate::suffix_ecology`] owns the transport. Nothing here rivals either. What
//! was absent is one **edge**: the P3 driver obtains its predecessor atlas by rebuilding it from
//! the eight canon documents, so the law stood on a body the corpus had to be present to make. A
//! frozen runtime may not do that, and the falsifier matrix names it — *source-detached rest
//! retains source/corpus lookup*.
//!
//! So this module is exactly the composition an application needs and nothing more:
//!
//! ```text
//!   octets -> AthenaRest            atlas_cultivation::AthenaRest::read_container   (stood already)
//!   AthenaRest -> ExactSuffixEcology  suffix_ecology::mount_emitted                 (the new edge)
//!   prompt -> plural section        atlas_cultivation::conduct                      (stood already)
//!   material -> successor           atlas_cultivation::{read_residual, derive, commit}
//! ```
//!
//! # The split between this and the application
//!
//! Everything above is library because it is a law and not a reading. The `eros phoenix` station
//! holds the argument parsing, the printing, the hashes it prints, and the audit it prints — a
//! station drives standing organs and carries no reading of its own.
//!
//! # What the rest has to carry, and the one thing P0's did not
//!
//! Conduct reads the transport, the standings, the suffix links and the vocabulary, and the P0 rest
//! carries all four — so `infer` mounts P0's own committed artifact directly. A **deposit** also
//! reads the class extents, which P0 did not emit and which are not derivable from what it did
//! (see [`crate::suffix_ecology::ExactSuffixEcology::mount_emitted`]). [`seal`] emits them;
//! [`mount_atlas`] refuses a rest without them **by name**, rather than guessing three answers.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use num_rational::BigRational;

use crate::atlas_cultivation::{
    commit, derive, emit_rest, read_residual, unit_covector, AthenaRest, CultivationDelta,
    CultivationRefusal, DepositIncidence, ExposureResidual, MetricDeclaration, EXTENT_REGION,
};
use crate::causal_language::{lexical_tokens, token_germs_public};
use crate::resonance_ecology::ResonanceGerm;
use crate::suffix_ecology::ExactSuffixEcology;

// -------------------------------------------------------------------------------------------
// refusals — every one of them names the rest it is about
// -------------------------------------------------------------------------------------------

/// **What the frozen runtime refuses, and what it names when it does.**
///
/// A refusal that says only *failed* is a refusal a caller cannot act on, and the deed's third
/// control asks for exactly the opposite: a missing rest must produce a typed refusal naming the
/// rest, a non-zero exit, and no plausible output.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PhoenixRefusal {
    /// The rest is not on the disk at the path the caller named.
    NoRest { rest: String, why: String },
    /// The octets at that path are not the declared container.
    NotAContainer { rest: String, why: String },
    /// The container carries no class extents, so it conducts and cannot be deposited into.
    NoExtents { rest: String, classes: usize },
    /// The mounted arrays do not satisfy the transport's own invariants.
    Unmountable { rest: String, why: String },
    /// The material could not be read.
    Material { path: String, why: String },
    /// The cultivation law refused, and carries its own reason.
    Cultivation(CultivationRefusal),
}

impl core::fmt::Display for PhoenixRefusal {
    fn fmt(&self, form: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::NoRest { rest, why } => write!(
                form,
                "the rest {rest} is not there ({why}) — this runtime mounts a rest and has no \
                 second place to look, so there is nothing to conduct"
            ),
            Self::NotAContainer { rest, why } => {
                write!(form, "the rest {rest} is not the declared container: {why}")
            }
            Self::NoExtents { rest, classes } => write!(
                form,
                "the rest {rest} carries {classes} classes and no {EXTENT_REGION} region, so it \
                 CONDUCTS and cannot be deposited into: the class the concatenation ends in, the \
                 split test and the occurrence fold all read a class extent, and an extent that is \
                 absent is not one wrong answer but three. Seal a rest that carries it."
            ),
            Self::Unmountable { rest, why } => write!(
                form,
                "the rest {rest} does not satisfy the transport's own invariants: {why}"
            ),
            Self::Material { path, why } => write!(form, "the material {path}: {why}"),
            Self::Cultivation(refusal) => write!(form, "{refusal}"),
        }
    }
}

impl From<CultivationRefusal> for PhoenixRefusal {
    fn from(refusal: CultivationRefusal) -> Self {
        Self::Cultivation(refusal)
    }
}

// -------------------------------------------------------------------------------------------
// the seal
// -------------------------------------------------------------------------------------------

/// Every class's own extent, read off the transport that holds it.
pub fn extents_of(atlas: &ExactSuffixEcology) -> Vec<u64> {
    (0..atlas.state_count() as u32)
        .map(|state| atlas.class_extent(state).unwrap_or(0) as u64)
        .collect()
}

/// **SEAL a standing atlas as a rest a later process can both conduct and deposit into.**
///
/// This is [`emit_rest`] plus the extents, and it is deliberately not `emit_rest` itself: every
/// container that stands was written by that emission and its octets do not move.
pub fn seal(
    atlas: &ExactSuffixEcology,
    metadata: BTreeMap<String, String>,
) -> Result<AthenaRest, CultivationRefusal> {
    let mut rest = emit_rest(atlas, metadata)?;
    rest.extent = extents_of(atlas);
    Ok(rest)
}

// -------------------------------------------------------------------------------------------
// the mount
// -------------------------------------------------------------------------------------------

/// Read one rest from one path. **The only file this runtime opens on the way to conducting.**
pub fn read_rest(path: &Path) -> Result<(Vec<u8>, AthenaRest), PhoenixRefusal> {
    let rest = path.display().to_string();
    let octets = std::fs::read(path).map_err(|error| PhoenixRefusal::NoRest {
        rest: rest.clone(),
        why: error.to_string(),
    })?;
    let mounted =
        AthenaRest::read_container(&octets).map_err(|error| PhoenixRefusal::NotAContainer {
            rest: rest.clone(),
            why: error.to_string(),
        })?;
    Ok((octets, mounted))
}

/// **MOUNT the transport from the rest alone.** Refuses a rest that carries no extents, by name.
pub fn mount_atlas(rest: &AthenaRest, named: &str) -> Result<ExactSuffixEcology, PhoenixRefusal> {
    if rest.extent.len() != rest.classes() {
        return Err(PhoenixRefusal::NoExtents {
            rest: named.to_owned(),
            classes: rest.classes(),
        });
    }
    let mut rows: Vec<Vec<(ResonanceGerm, u32)>> = Vec::with_capacity(rest.classes());
    let germs = germ_population(&rest.vocabulary).map_err(|why| PhoenixRefusal::Unmountable {
        rest: named.to_owned(),
        why,
    })?;
    for class in 0..rest.classes() as u32 {
        let (start, end) = (
            rest.indptr[class as usize] as usize,
            rest.indptr[class as usize + 1] as usize,
        );
        let mut row = Vec::with_capacity(end - start);
        for slot in start..end {
            let germ =
                germs
                    .get(rest.germ[slot] as usize)
                    .ok_or_else(|| PhoenixRefusal::Unmountable {
                        rest: named.to_owned(),
                        why: format!(
                            "transport slot {slot} names germ {} and the vocabulary holds {}",
                            rest.germ[slot],
                            germs.len()
                        ),
                    })?;
            row.push((germ.clone(), rest.target[slot] as u32));
        }
        rows.push(row);
    }
    ExactSuffixEcology::mount_emitted(&rest.extent, &rest.suffix, &rest.standing, &rows).map_err(
        |error| PhoenixRefusal::Unmountable {
            rest: named.to_owned(),
            why: format!("{error:?}"),
        },
    )
}

/// The vocabulary's germs, in vocabulary order. A germ is determined by its surface, so this is the
/// exact inverse of the emission's `fiber_bytes(germ.identity())`.
fn germ_population(vocabulary: &[String]) -> Result<Vec<ResonanceGerm>, String> {
    token_germs_public(vocabulary).map_err(|error| format!("{error:?}"))
}

// -------------------------------------------------------------------------------------------
// the deposit
// -------------------------------------------------------------------------------------------

/// One cultivation performed from the rest alone.
pub struct Cultivated {
    pub residual: ExposureResidual,
    pub delta: CultivationDelta,
    /// The successor: the committed germ side, with the transport's extents attached.
    pub successor: AthenaRest,
    /// **The P3 identity, re-taken here**: the committed container against the container the
    /// transport itself emits, octet for octet. The comparison is over the **germ side** — the
    /// extents are the transport's on both sides and so are not a falsifier, and this says so.
    pub germ_side_identical: bool,
    pub germs: usize,
}

/// **CULTIVATE from the rest alone: residual → deposit → derive → commit.**
///
/// The predecessor atlas is *mounted from the rest*, not rebuilt from a corpus. That is the whole
/// difference between this and the P3 driver, and it is the difference the deed is about.
pub fn cultivate(
    rest: &AthenaRest,
    named: &str,
    label: &str,
    material: &str,
    metric: &MetricDeclaration,
) -> Result<Cultivated, PhoenixRefusal> {
    let tokens = lexical_tokens(material);
    let germs = token_germs_public(&tokens).map_err(|error| PhoenixRefusal::Material {
        path: label.to_owned(),
        why: format!("{error:?}"),
    })?;
    if germs.is_empty() {
        return Err(PhoenixRefusal::Material {
            path: label.to_owned(),
            why: "the material founds no germ, so there is nothing to deposit".to_owned(),
        });
    }
    let surfaces = crate::atlas_cultivation::surfaces_of(&germs)?;

    // 1 — PREDICT, mutating nothing. The rest alone answers this.
    let residual = read_residual(rest, label, &surfaces);
    // 2 — DEPOSIT into the atlas mounted from the rest, returning the forward lineage.
    let mut atlas = mount_atlas(rest, named)?;
    let lineage =
        atlas
            .absorb_returning_lineage(&germs)
            .map_err(|error| PhoenixRefusal::Unmountable {
                rest: named.to_owned(),
                why: format!("the deposit refused: {error:?}"),
            })?;
    let incidence = DepositIncidence::of(&atlas, &lineage);
    // 3 — DERIVE, under the declared metric and the unit covector.
    let covector: Vec<BigRational> = unit_covector(&residual);
    let delta = derive(
        rest, &residual, &lineage, &incidence, metric, &covector, &surfaces,
    )?;
    // 4 — COMMIT by replay onto the predecessor, then check it against the transport's own body.
    let committed = commit(rest, &delta)?;
    let transported = emit_rest(&atlas, rest.metadata.clone())?;
    let germ_side_identical = committed.write_container()? == transported.write_container()?;
    let mut successor = committed;
    successor.extent = extents_of(&atlas);
    Ok(Cultivated {
        residual,
        delta,
        successor,
        germ_side_identical,
        germs: germs.len(),
    })
}

// -------------------------------------------------------------------------------------------
// the audit, the manifest, and the bar
// -------------------------------------------------------------------------------------------

/// **Every file this process has open, by the target it resolves to.**
///
/// A claim that a runtime is source-detached is a claim about what it opened, and this is the
/// process asking the question of itself rather than an outside observer asserting it.
pub fn open_descriptors() -> Vec<String> {
    let mut audit: Vec<String> = Vec::new();
    if let Ok(entries) = std::fs::read_dir("/proc/self/fd") {
        for entry in entries.flatten() {
            if let Ok(target) = std::fs::read_link(entry.path()) {
                audit.push(target.to_string_lossy().into_owned());
            }
        }
    }
    audit.sort();
    audit.dedup();
    audit
}

/// **The descriptor targets a frozen runtime may not hold**, and what an audit found of them.
///
/// The named classes are the ones the deed is about: the declared corpus, the research record, a
/// foreign source model in any of its carriers, another driver's material, and the card. The card
/// is in this list for the honest reason rather than the impressive one — this station conducts
/// CPU-exact, so the correct claim is that it never opens the device at all, not that a hidden
/// device produced a typed refusal.
pub const FORBIDDEN_DESCRIPTORS: &[&str] = &[
    "/canon/",
    "/research/",
    "/blueprint/",
    "/examples/",
    "gemma",
    ".gguf",
    "/dev/nvidia",
    "/dev/dri",
];

/// Which of [`FORBIDDEN_DESCRIPTORS`] an audit actually found. Empty is the whole claim.
pub fn forbidden_open(audit: &[String]) -> Vec<String> {
    audit
        .iter()
        .filter(|target| {
            let lowered = target.to_ascii_lowercase();
            FORBIDDEN_DESCRIPTORS
                .iter()
                .any(|needle| lowered.contains(needle))
        })
        .cloned()
        .collect()
}

/// One region of the container, as its own header declares it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Region {
    pub name: String,
    pub dtype: String,
    pub start: usize,
    pub end: usize,
}

impl Region {
    pub fn octets(&self) -> usize {
        self.end.saturating_sub(self.start)
    }
}

/// **The realization manifest: what is actually in the container.** Read out of the header the
/// container carries, not out of a table beside it.
pub fn regions(octets: &[u8]) -> Vec<Region> {
    let Some(header) = header_of(octets) else {
        return Vec::new();
    };
    let mut found = Vec::new();
    let mut rest = header;
    while let Some(at) = rest.find("\"dtype\":\"") {
        // the name is the quoted key immediately before this object
        let before = &rest[..at];
        let Some(open) = before.rfind(":{") else {
            break;
        };
        let head = &before[..open];
        let Some(name_end) = head.rfind('"') else {
            break;
        };
        let Some(name_start) = head[..name_end].rfind('"') else {
            break;
        };
        let name = head[name_start + 1..name_end].to_owned();
        let after = &rest[at + "\"dtype\":\"".len()..];
        let Some(dtype_end) = after.find('"') else {
            break;
        };
        let dtype = after[..dtype_end].to_owned();
        let (start, end) = match after.find("\"data_offsets\":[") {
            Some(marker) => {
                let tail = &after[marker + "\"data_offsets\":[".len()..];
                match tail.find(']') {
                    Some(close) => {
                        let mut parts = tail[..close].split(',');
                        let read = |part: Option<&str>| {
                            part.and_then(|value| value.trim().parse::<usize>().ok())
                                .unwrap_or(0)
                        };
                        (read(parts.next()), read(parts.next()))
                    }
                    None => (0, 0),
                }
            }
            None => (0, 0),
        };
        found.push(Region {
            name,
            dtype,
            start,
            end,
        });
        rest = after;
    }
    found
}

fn header_of(octets: &[u8]) -> Option<&str> {
    if octets.len() < 8 {
        return None;
    }
    let length = u64::from_le_bytes(octets[..8].try_into().ok()?) as usize;
    core::str::from_utf8(octets.get(8..8 + length)?).ok()
}

/// **A loss detector over a frozen rest, and nothing else.**
///
/// The archive's lesson is that a deposit's identity is its path plus its lineage, never a
/// checksum — a hash is a compression with no decoder, so making one an identity imports a deletion
/// at the addressing layer. The two uses it leaves standing are **detecting loss** and **declaring
/// an apparatus frame**, and this is the first: a frozen inference must leave the rest unmoved, and
/// this is how a reader sees at a glance that it did. Nothing addresses a rest by it, and the
/// controls compare the octets themselves rather than this.
pub fn loss_digest(octets: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    let mut rendered = String::with_capacity(64);
    for octet in Sha256::digest(octets) {
        rendered.push_str(&format!("{octet:02x}"));
    }
    rendered
}

/// The statement of the law a cultivated rest carries, so a later reader binds against the rest's
/// own declaration rather than against an implementation it does not have.
pub const CULTIVATION_LAW: &str = "cultivation: predict the continuation family the standing rest \
     offers at every position of the material and record the four-state relation between it and \
     what the material carried (the structured residual); deposit the material; derive the \
     structural rows from the residual's refusals with the position that caused each, and the \
     standings from the exact receiver differential of the R1 ladder face returned through the \
     declared metrics, standing(s) = carried(s) + (G_X^-1 A^T G_Y r)_s; commit by replaying the \
     derived rows onto the predecessor";

/// **The successor's declared cultivation lineage**, which is the metadata a later process reads to
/// know what this body is a successor OF and by what law.
///
/// The predecessor's own material declaration is carried under
/// [`crate::atlas_cultivation::PREDECESSOR_MATERIAL_KEY`] so that a withdrawal can restore it, and
/// the `material` key is extended rather than replaced: the successor's material is the
/// predecessor's plus this exposure, which is a lineage and not a corpus.
pub fn lineage_metadata(
    predecessor: &AthenaRest,
    predecessor_named: &str,
    material_named: &str,
    grown: &Cultivated,
    metric: &MetricDeclaration,
) -> BTreeMap<String, String> {
    let mut metadata = predecessor.metadata.clone();
    let declared = predecessor
        .metadata
        .get("material")
        .cloned()
        .unwrap_or_default();
    metadata.insert(
        crate::atlas_cultivation::PREDECESSOR_MATERIAL_KEY.to_owned(),
        declared.clone(),
    );
    metadata.insert("cultivation.law".to_owned(), CULTIVATION_LAW.to_owned());
    metadata.insert("cultivation.metric".to_owned(), metric.name.clone());
    metadata.insert(
        "cultivation.predecessor".to_owned(),
        format!(
            "{predecessor_named} · {} classes · {} transitions · {} vocabulary",
            predecessor.classes(),
            predecessor.transitions(),
            predecessor.vocabulary.len()
        ),
    );
    metadata.insert(
        "cultivation.material".to_owned(),
        format!(
            "{material_named} ({} germ occurrences, exposed once, lexical aperture: inherited)",
            grown.germs
        ),
    );
    metadata.insert(
        "cultivation.delta".to_owned(),
        format!(
            "germs +{} · classes +{} of which {} are splits · transitions founded {} of which {} \
             inside the standing body · links rebased {} of which {} on standing classes · \
             standings moved at {} classes",
            grown.delta.germs_founded.len(),
            grown.delta.classes_after - grown.delta.classes_before,
            grown.delta.classes_split(),
            grown.delta.transitions_founded.len(),
            grown.delta.transitions_founded_on_standing(),
            grown.delta.suffix_rebased.len(),
            grown
                .delta
                .suffix_rebased
                .iter()
                .filter(|row| row.on_standing_class)
                .count(),
            grown.delta.standing_increments.len()
        ),
    );
    let mut declared_material: Vec<String> = declared
        .split_whitespace()
        .map(str::to_owned)
        .collect::<Vec<_>>();
    declared_material.push(format!("{material_named}@{}", declared_material.len() + 1));
    metadata.insert("material".to_owned(), declared_material.join(" "));
    metadata
}

/// One row of the content bar: what the rest is required NOT to carry, and what was measured.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BarRow {
    pub claim: &'static str,
    pub held: bool,
    pub evidence: String,
}

/// **THE CONTENT BAR, MEASURED.** Every row is a count taken on the container's own octets.
///
/// The honest note the fourth row carries: the vocabulary **is** material-derived surface strings —
/// that is what a germ is — so the bar is not *no string from the material*. It is that the
/// **corpus** is absent: the documents' text is not reconstructible from the container, and what is
/// there is the germ population, one occurrence of each surface, with the chronology living in the
/// transport rather than in any retained text.
pub fn content_bar(octets: &[u8], rest: &AthenaRest) -> Vec<BarRow> {
    let regions = regions(octets);
    let float_dtypes: Vec<&Region> = regions
        .iter()
        .filter(|region| {
            let dtype = region.dtype.to_ascii_uppercase();
            dtype.starts_with('F') || dtype.starts_with("BF")
        })
        .collect();
    let foreign_regions: Vec<&Region> = regions
        .iter()
        .filter(|region| !region.name.starts_with("athena."))
        .collect();
    let metadata_text = rest
        .metadata
        .iter()
        .map(|(key, value)| format!("{key}={value}"))
        .collect::<Vec<_>>()
        .join("\n");
    let routing = [
        "gemma",
        "phoenix",
        "q_proj",
        "k_proj",
        "v_proj",
        "o_proj",
        "gate_proj",
        "up_proj",
        "down_proj",
        "self_attn",
        "mlp.",
    ];
    let routing_hits: Vec<&str> = routing
        .iter()
        .copied()
        .filter(|needle| {
            metadata_text.to_ascii_lowercase().contains(needle)
                || regions
                    .iter()
                    .any(|region| region.name.to_ascii_lowercase().contains(needle))
        })
        .collect();
    let program = ["portedprogram", "opcode", "ordinal", "expected", "prompt"];
    let program_hits: Vec<&str> = program
        .iter()
        .copied()
        .filter(|needle| {
            rest.metadata
                .keys()
                .any(|key| key.to_ascii_lowercase().contains(needle))
                || regions
                    .iter()
                    .any(|region| region.name.to_ascii_lowercase().contains(needle))
        })
        .collect();
    let multi_germ: Vec<&String> = rest
        .vocabulary
        .iter()
        .filter(|surface| surface.contains(' ') || surface.contains('\n'))
        .collect();
    let vocabulary_octets: usize = rest.vocabulary.iter().map(|surface| surface.len()).sum();
    let unique: BTreeSet<&String> = rest.vocabulary.iter().collect();
    let declared_material = rest
        .metadata
        .get("material")
        .cloned()
        .unwrap_or_else(|| "(none declared)".to_owned());

    vec![
        BarRow {
            claim: "no source tensor payload",
            held: float_dtypes.is_empty() && foreign_regions.is_empty(),
            evidence: format!(
                "{} regions, every name under `athena.`, every dtype an integer carrier ({}); \
                 float/bfloat regions {}",
                regions.len(),
                regions
                    .iter()
                    .map(|region| region.dtype.as_str())
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect::<Vec<_>>()
                    .join("/"),
                float_dtypes.len()
            ),
        },
        BarRow {
            claim: "no PortedProgram, no operation ordinals, no expected output table, no \
                    hard-coded input rows",
            held: program_hits.is_empty(),
            evidence: format!(
                "region names and metadata keys searched for {program:?} — {} hit(s); the metadata \
                 keys are {:?}",
                program_hits.len(),
                rest.metadata.keys().collect::<Vec<_>>()
            ),
        },
        BarRow {
            claim: "no source-routing names",
            held: routing_hits.is_empty(),
            evidence: format!(
                "region names and metadata values searched for {routing:?} — {} hit(s)",
                routing_hits.len()
            ),
        },
        BarRow {
            claim: "no development corpus — the documents' TEXT is absent",
            held: multi_germ.is_empty(),
            evidence: format!(
                "the container holds {} classes, {} transitions and {} vocabulary germs in {} \
                 octets of surface; {} germ(s) carry a space or newline, so no germ is a phrase and \
                 none is a line of a document. {} of the germs are distinct. The declared material \
                 is a LIST OF PATHS in the metadata ({} octets), which is a lineage and not the \
                 text. HONESTLY: the vocabulary IS material-derived surface strings — that is what \
                 a germ is — and the bar is that the CORPUS is absent, which it is: one occurrence \
                 of each surface, with every chronology in the transport.",
                rest.classes(),
                rest.transitions(),
                rest.vocabulary.len(),
                vocabulary_octets,
                multi_germ.len(),
                unique.len(),
                declared_material.len()
            ),
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atlas_cultivation::{conduct, surfaces_of, REST_SCHEMA};

    fn atlas_of(texts: &[&str]) -> ExactSuffixEcology {
        let paths: Vec<Vec<ResonanceGerm>> = texts
            .iter()
            .map(|text| token_germs_public(&lexical_tokens(text)).expect("germs"))
            .collect();
        ExactSuffixEcology::condition(&paths).expect("conditioned")
    }

    fn declarations() -> BTreeMap<String, String> {
        let mut metadata = BTreeMap::new();
        metadata.insert("schema".to_owned(), REST_SCHEMA.to_owned());
        metadata.insert(
            "material".to_owned(),
            "a-chart@1 a-receiver@2 a-transport@3".to_owned(),
        );
        metadata
    }

    const MATERIAL: &[&str] = &[
        "a chart is a receiver and the transport is a jacobian",
        "the receiver declares the grain it reads at and the chart follows",
        "a transport carries a construction and returns a residual to the receiver",
    ];

    /// **The container's return edge is exact**: mount what was emitted, emit it again, and the
    /// octets do not move.
    #[test]
    fn the_rest_mounts_the_transport_it_was_emitted_from_and_re_emits_it_octet_for_octet() {
        let atlas = atlas_of(MATERIAL);
        let sealed = seal(&atlas, declarations()).expect("sealed");
        let mounted = mount_atlas(&sealed, "test").expect("mounted");
        let again = seal(&mounted, declarations()).expect("re-sealed");
        assert_eq!(
            sealed.write_container().unwrap(),
            again.write_container().unwrap()
        );
        assert_eq!(mounted.state_count(), atlas.state_count());
        for class in 0..atlas.state_count() as u32 {
            assert_eq!(mounted.class_extent(class), atlas.class_extent(class));
            assert_eq!(mounted.standing_at(class), atlas.standing_at(class));
            assert_eq!(mounted.suffix_link(class), atlas.suffix_link(class));
        }
    }

    /// **The falsifier that decides the whole deed**: a deposit into the atlas mounted from the
    /// rest is the deposit into the atlas the corpus built. If the mount were lossy in any way the
    /// deposit reads, these two containers would differ.
    #[test]
    fn a_deposit_into_the_mounted_atlas_is_the_deposit_into_the_atlas_the_corpus_built() {
        let corpus_built = atlas_of(MATERIAL);
        let sealed = seal(&corpus_built, declarations()).expect("sealed");
        let mounted = mount_atlas(&sealed, "test").expect("mounted");

        let exposure = "a jacobian is a chart transition and the residual is a receiver face";
        let germs = token_germs_public(&lexical_tokens(exposure)).expect("germs");

        let mut from_corpus = corpus_built;
        let corpus_lineage = from_corpus
            .absorb_returning_lineage(&germs)
            .expect("absorbed");
        let mut from_rest = mounted;
        let rest_lineage = from_rest
            .absorb_returning_lineage(&germs)
            .expect("absorbed");

        assert_eq!(corpus_lineage.stood_in, rest_lineage.stood_in);
        assert_eq!(corpus_lineage.landed, rest_lineage.landed);
        assert_eq!(corpus_lineage.per_position, rest_lineage.per_position);
        assert_eq!(
            emit_rest(&from_corpus, declarations())
                .unwrap()
                .write_container()
                .unwrap(),
            emit_rest(&from_rest, declarations())
                .unwrap()
                .write_container()
                .unwrap()
        );
    }

    /// The whole application-side cultivation, from the rest alone, against the same law driven by
    /// the corpus-built body: the successors agree octet for octet on the germ side.
    #[test]
    fn cultivating_from_the_rest_alone_returns_the_successor_the_corpus_built_body_returns() {
        let atlas = atlas_of(MATERIAL);
        let sealed = seal(&atlas, declarations()).expect("sealed");
        let exposure = "a jacobian is a chart transition and the residual is a receiver face";
        let grown = cultivate(
            &sealed,
            "test",
            "exposure",
            exposure,
            &MetricDeclaration::identity(),
        )
        .expect("cultivated");
        assert!(grown.germ_side_identical);
        assert!(grown.delta.classes_after > grown.delta.classes_before);

        // the same law, driven the P3 way
        let mut corpus_built = atlas_of(MATERIAL);
        let germs = token_germs_public(&lexical_tokens(exposure)).expect("germs");
        let surfaces = surfaces_of(&germs).expect("surfaces");
        let residual = read_residual(&sealed, "exposure", &surfaces);
        let lineage = corpus_built
            .absorb_returning_lineage(&germs)
            .expect("absorbed");
        let incidence = DepositIncidence::of(&corpus_built, &lineage);
        let delta = derive(
            &sealed,
            &residual,
            &lineage,
            &incidence,
            &MetricDeclaration::identity(),
            &unit_covector(&residual),
            &surfaces,
        )
        .expect("derived");
        assert_eq!(delta, grown.delta);
    }

    /// A rest without its extents conducts and refuses a deposit **by name**.
    #[test]
    fn a_rest_without_extents_conducts_and_refuses_the_deposit_naming_itself() {
        let atlas = atlas_of(MATERIAL);
        let p0_shaped = emit_rest(&atlas, declarations()).expect("emitted");
        assert!(p0_shaped.extent.is_empty());
        let section = conduct(&p0_shaped, "the receiver", &lexical_tokens("the receiver"));
        assert!(!section.offered.is_empty());
        let refusal = mount_atlas(&p0_shaped, "output/x/rest.safetensors").unwrap_err();
        assert!(matches!(refusal, PhoenixRefusal::NoExtents { .. }));
        let said = refusal.to_string();
        assert!(said.contains("output/x/rest.safetensors"));
        assert!(said.contains(EXTENT_REGION));
    }

    /// The optional region is optional in both directions, so nothing that stands moves.
    #[test]
    fn a_rest_that_carries_no_extents_writes_the_octets_it_always_wrote() {
        let atlas = atlas_of(MATERIAL);
        let p0_shaped = emit_rest(&atlas, declarations()).expect("emitted");
        let octets = p0_shaped.write_container().expect("written");
        let header = header_of(&octets).expect("header");
        assert!(!header.contains(EXTENT_REGION));
        let read_back = AthenaRest::read_container(&octets).expect("read");
        assert_eq!(read_back, p0_shaped);
        assert_eq!(read_back.write_container().unwrap(), octets);

        let sealed = seal(&atlas, declarations()).expect("sealed");
        let sealed_octets = sealed.write_container().expect("written");
        assert!(header_of(&sealed_octets).unwrap().contains(EXTENT_REGION));
        assert_eq!(
            AthenaRest::read_container(&sealed_octets).expect("read"),
            sealed
        );
    }

    /// The manifest reads the container's own header, and the bar is measured on the octets.
    #[test]
    fn the_manifest_and_the_bar_are_read_off_the_container() {
        let atlas = atlas_of(MATERIAL);
        let sealed = seal(&atlas, declarations()).expect("sealed");
        let octets = sealed.write_container().expect("written");
        let regions = regions(&octets);
        assert_eq!(regions.len(), 9);
        assert!(regions
            .iter()
            .all(|region| region.name.starts_with("athena.")));
        assert!(regions.iter().any(|region| region.name == EXTENT_REGION));
        assert_eq!(
            regions.last().unwrap().end,
            octets.len() - 8 - header_of(&octets).unwrap().len()
        );
        for row in content_bar(&octets, &sealed) {
            assert!(row.held, "{}: {}", row.claim, row.evidence);
        }
    }
}
