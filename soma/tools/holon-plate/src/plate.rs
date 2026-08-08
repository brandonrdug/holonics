//! The `.holon` container: head, census, form, seal.
//!
//! This module knows nothing about bodies. It seals octets and it opens octets, and its whole
//! contribution is that the two ways a plate can be wrong are **separable and named**.
//!
//! See the crate doc for the exact layout table and the two-species argument.

use std::fmt;

use soma_standing_deposit::sha256::{hex, Sha256};

use crate::census::{Census, CensusRefusal};

/// The magic the old laboratory plate carried, kept deliberately. A reader that recognises the
/// historical plate must be able to tell at octet zero that this is the same mouth, and a reader
/// that opens a historical plate must fail on the *version*, which is a precise refusal, rather
/// than on the magic, which is a vague one.
pub const PLATE_MAGIC: [u8; 4] = *b"HLON";

/// The container layout version. Bumped only when the HEAD/CENSUS/FORM/SEAL arrangement changes,
/// never when a schema changes — a schema carries its own version in the head.
pub const PLATE_VERSION: u32 = 1;

/// The agreed suffix. The gap this crate closes is that nothing wrote one.
pub const PLATE_SUFFIX: &str = "holon";

pub const HEAD_OCTETS: usize = 32;
pub const SEAL_OCTETS: usize = 64;

const MAGIC_AT: usize = 0;
const PLATE_VERSION_AT: usize = 4;
const SCHEMA_TAG_AT: usize = 8;
const SCHEMA_VERSION_AT: usize = 12;
const CENSUS_OCTETS_AT: usize = 16;
const FORM_OCTETS_AT: usize = 24;

/// Four octets of `[A-Z0-9]` naming a form codec. It is the codec's own magic where the codec has
/// one: `HTEC` for the training ecology, `ERST` for the live current rest.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SchemaTag([u8; 4]);

impl SchemaTag {
    /// A tag, or `None` if any octet is outside `[A-Z0-9]`. Restricting the alphabet is what makes
    /// an unknown tag reportable as text in a refusal rather than as a hex blob.
    pub const fn new(octets: [u8; 4]) -> Option<Self> {
        let mut at = 0usize;
        while at < 4 {
            let octet = octets[at];
            let held = (octet >= b'A' && octet <= b'Z') || (octet >= b'0' && octet <= b'9');
            if !held {
                return None;
            }
            at += 1;
        }
        Some(Self(octets))
    }

    pub fn parse(text: &str) -> Option<Self> {
        let octets: [u8; 4] = text.as_bytes().try_into().ok()?;
        Self::new(octets)
    }

    pub const fn octets(self) -> [u8; 4] {
        self.0
    }
}

impl fmt::Display for SchemaTag {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        for octet in self.0 {
            write!(out, "{}", octet as char)?;
        }
        Ok(())
    }
}

impl fmt::Debug for SchemaTag {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(out, "SchemaTag({self})")
    }
}

/// One plate, opened and verified as a container. Its form has not been mounted: opening proves
/// the octets are intact, not that a body will come out of them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReadPlate {
    pub tag: SchemaTag,
    pub schema_version: u32,
    pub census: Census,
    pub form: Vec<u8>,
    pub form_sha256: [u8; 32],
    pub plate_sha256: [u8; 32],
}

impl ReadPlate {
    pub fn form_digest_hex(&self) -> String {
        hex(&self.form_sha256)
    }

    pub fn plate_digest_hex(&self) -> String {
        hex(&self.plate_sha256)
    }
}

/// Seal one plate. The two digests are computed here and only here.
pub fn seal(tag: SchemaTag, schema_version: u32, census: &Census, form: &[u8]) -> Vec<u8> {
    let census_octets = census.encode();
    let mut plate = Vec::with_capacity(HEAD_OCTETS + census_octets.len() + form.len() + SEAL_OCTETS);
    plate.extend_from_slice(&PLATE_MAGIC);
    plate.extend_from_slice(&PLATE_VERSION.to_le_bytes());
    plate.extend_from_slice(&tag.octets());
    plate.extend_from_slice(&schema_version.to_le_bytes());
    plate.extend_from_slice(&(census_octets.len() as u64).to_le_bytes());
    plate.extend_from_slice(&(form.len() as u64).to_le_bytes());
    debug_assert_eq!(plate.len(), HEAD_OCTETS);
    plate.extend_from_slice(&census_octets);
    plate.extend_from_slice(form);

    let form_sha256 = digest(form);
    // The binding folds the *stored* content digest, never the form. That is what keeps the two
    // failure species separable: a corrupted form moves the content digest and leaves this one
    // standing, so exactly one of the two refusals fires and it names the side that moved.
    let mut binding = Sha256::new();
    binding.update(&plate[..HEAD_OCTETS + census_octets.len()]);
    binding.update(&form_sha256);
    let plate_sha256 = binding.finish();

    plate.extend_from_slice(&form_sha256);
    plate.extend_from_slice(&plate_sha256);
    plate
}

/// Open one plate. Verifies the magic, the container version, every declared extent, and both
/// digests, in that order, so that the first thing that is wrong is the thing that is named.
pub fn open(octets: &[u8]) -> Result<ReadPlate, PlateRefusal> {
    let minimum = HEAD_OCTETS + SEAL_OCTETS;
    if octets.len() < minimum {
        return Err(PlateRefusal::ShortPlate {
            octets: octets.len(),
            minimum,
        });
    }
    let magic: [u8; 4] = octets[MAGIC_AT..MAGIC_AT + 4].try_into().expect("four");
    if magic != PLATE_MAGIC {
        return Err(PlateRefusal::NotAPlate { found: magic });
    }
    let plate_version = read_u32(octets, PLATE_VERSION_AT);
    if plate_version != PLATE_VERSION {
        return Err(PlateRefusal::PlateVersionUnheld {
            found: plate_version,
            held: PLATE_VERSION,
        });
    }
    let tag_octets: [u8; 4] = octets[SCHEMA_TAG_AT..SCHEMA_TAG_AT + 4]
        .try_into()
        .expect("four");
    let tag = SchemaTag::new(tag_octets).ok_or(PlateRefusal::SchemaTagMalformed {
        found: tag_octets,
    })?;
    let schema_version = read_u32(octets, SCHEMA_VERSION_AT);
    let census_octets = read_u64(octets, CENSUS_OCTETS_AT);
    let form_octets = read_u64(octets, FORM_OCTETS_AT);

    let body = octets.len() - HEAD_OCTETS - SEAL_OCTETS;
    let census_extent = usize::try_from(census_octets).map_err(|_| PlateRefusal::ExtentOverruns {
        field: "census_octets",
        declared: census_octets,
        remaining: body as u64,
    })?;
    if census_extent > body {
        return Err(PlateRefusal::ExtentOverruns {
            field: "census_octets",
            declared: census_octets,
            remaining: body as u64,
        });
    }
    let form_extent = usize::try_from(form_octets).map_err(|_| PlateRefusal::ExtentOverruns {
        field: "form_octets",
        declared: form_octets,
        remaining: (body - census_extent) as u64,
    })?;
    if form_extent != body - census_extent {
        return Err(PlateRefusal::ExtentOverruns {
            field: "form_octets",
            declared: form_octets,
            remaining: (body - census_extent) as u64,
        });
    }

    let census_start = HEAD_OCTETS;
    let form_start = census_start + census_extent;
    let seal_start = form_start + form_extent;
    let form = &octets[form_start..seal_start];
    let deposited_form_sha256: [u8; 32] = octets[seal_start..seal_start + 32]
        .try_into()
        .expect("thirty-two");
    let deposited_plate_sha256: [u8; 32] = octets[seal_start + 32..seal_start + 64]
        .try_into()
        .expect("thirty-two");

    // BOTH digests are computed before either is judged, because it is the PAIR that names the
    // region. Judging the content digest alone would report "the form moved" for a plate whose
    // recorded content digest is the thing that moved -- the form would be untouched and the
    // refusal would point at it.
    let recomputed_form = digest(form);
    let mut binding = Sha256::new();
    binding.update(&octets[..form_start]);
    binding.update(&deposited_form_sha256);
    let recomputed_plate = binding.finish();
    let content_holds = recomputed_form == deposited_form_sha256;
    let binding_holds = recomputed_plate == deposited_plate_sha256;
    match (content_holds, binding_holds) {
        (true, true) => {}
        // The recorded content digest is intact and still binds, so the FORM is the one region
        // that can have moved.
        (false, true) => {
            return Err(PlateRefusal::FormContentDrift {
                deposited: hex(&deposited_form_sha256),
                recomputed: hex(&recomputed_form),
                form_octets: form.len(),
            })
        }
        // The form still hashes to its recorded digest, so what moved is the declaration wrapped
        // around it: the head or the census.
        (true, false) => {
            return Err(PlateRefusal::PlateBindingDrift {
                deposited: hex(&deposited_plate_sha256),
                recomputed: hex(&recomputed_plate),
            })
        }
        // Neither digest holds. The recorded content digest itself has moved -- it no longer
        // describes the form AND it no longer binds -- or more than one region moved at once.
        (false, false) => {
            return Err(PlateRefusal::SealDrift {
                deposited_form: hex(&deposited_form_sha256),
                recomputed_form: hex(&recomputed_form),
                deposited_plate: hex(&deposited_plate_sha256),
                recomputed_plate: hex(&recomputed_plate),
            })
        }
    }

    let census = Census::decode(&octets[census_start..form_start]).map_err(PlateRefusal::Census)?;
    Ok(ReadPlate {
        tag,
        schema_version,
        census,
        form: form.to_vec(),
        form_sha256: deposited_form_sha256,
        plate_sha256: deposited_plate_sha256,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PlateRefusal {
    ShortPlate {
        octets: usize,
        minimum: usize,
    },
    NotAPlate {
        found: [u8; 4],
    },
    PlateVersionUnheld {
        found: u32,
        held: u32,
    },
    SchemaTagMalformed {
        found: [u8; 4],
    },
    ExtentOverruns {
        field: &'static str,
        declared: u64,
        remaining: u64,
    },
    /// The deposited form octets no longer hash to their recorded content digest. The evidence is
    /// corrupt.
    FormContentDrift {
        deposited: String,
        recomputed: String,
        form_octets: usize,
    },
    /// The form is intact and the head or census around it is not. The plate's declaration no
    /// longer binds the form it declares.
    PlateBindingDrift {
        deposited: String,
        recomputed: String,
    },
    /// Neither digest holds: the recorded content digest itself has moved, or more than one region
    /// moved at once. Reporting this as content drift would point the reader at a form that may be
    /// perfectly intact.
    SealDrift {
        deposited_form: String,
        recomputed_form: String,
        deposited_plate: String,
        recomputed_plate: String,
    },
    Census(CensusRefusal),
}

impl fmt::Display for PlateRefusal {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ShortPlate { octets, minimum } => write!(
                out,
                "REFUSED: {octets} octets cannot be a plate; the head and seal alone are {minimum}"
            ),
            Self::NotAPlate { found } => write!(
                out,
                "REFUSED: not a holon plate; octets 0..4 are {} where a plate opens `HLON`",
                printable(found)
            ),
            Self::PlateVersionUnheld { found, held } => write!(
                out,
                "REFUSED: plate container version {found} is not held; this reader holds {held}"
            ),
            Self::SchemaTagMalformed { found } => write!(
                out,
                "REFUSED: the schema tag {} is malformed; a tag is four octets of [A-Z0-9]",
                printable(found)
            ),
            Self::ExtentOverruns {
                field,
                declared,
                remaining,
            } => write!(
                out,
                "REFUSED: the head declares {field}={declared} with {remaining} octets of body \
                 present; the plate is truncated or its head has drifted"
            ),
            Self::FormContentDrift {
                deposited,
                recomputed,
                form_octets,
            } => write!(
                out,
                "REFUSED: CONTENT drift -- the {form_octets} deposited FORM octets no longer hold \
                 what was deposited.\n         deposited form_sha256 {deposited}\n         \
                 recomputed          {recomputed}\n         the binding digest still holds, so the \
                 head and census are intact and the FORM is what moved."
            ),
            Self::PlateBindingDrift {
                deposited,
                recomputed,
            } => write!(
                out,
                "REFUSED: BINDING drift -- the form is intact and the plate's declaration of it is \
                 not.\n         deposited plate_sha256 {deposited}\n         recomputed           \
                 {recomputed}\n         the content digest holds, so the HEAD or CENSUS is what \
                 moved."
            ),
            Self::SealDrift {
                deposited_form,
                recomputed_form,
                deposited_plate,
                recomputed_plate,
            } => write!(
                out,
                "REFUSED: SEAL drift -- neither digest holds.\n         deposited form_sha256  \
                 {deposited_form}\n         recomputed             {recomputed_form}\n         \
                 deposited plate_sha256 {deposited_plate}\n         recomputed             \
                 {recomputed_plate}\n         The recorded content digest itself has moved, or \
                 more than one region moved at once. The FORM may be intact; this refusal does not \
                 accuse it."
            ),
            Self::Census(refusal) => write!(out, "REFUSED: {refusal}"),
        }
    }
}

impl std::error::Error for PlateRefusal {}

fn printable(octets: &[u8; 4]) -> String {
    let rendered: String = octets
        .iter()
        .map(|octet| {
            if octet.is_ascii_graphic() {
                *octet as char
            } else {
                '.'
            }
        })
        .collect();
    format!("`{rendered}` (0x{})", hex(octets))
}

fn digest(octets: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(octets);
    hasher.finish()
}

fn read_u32(octets: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(octets[at..at + 4].try_into().expect("four"))
}

fn read_u64(octets: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(octets[at..at + 8].try_into().expect("eight"))
}
