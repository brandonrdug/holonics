//! What a schema is, and what a re-lit body must be able to do.
//!
//! A schema is a *held* form codec. The plate does not implement one and does not wrap one
//! generically: it holds a fixed, enumerable set, and a plate naming anything outside that set is
//! refused by name. There is no fallback path, no best-effort decode, and no "try the other
//! schema" — a guess about which body a file holds is the one failure this container exists to
//! make impossible.

use std::fmt;

use crate::census::{Census, CensusDisagreement};
use crate::plate::{PlateRefusal, SchemaTag};

/// One held form codec.
pub trait PlateSchema: Sync {
    /// The four-octet tag written into the plate head.
    fn tag(&self) -> SchemaTag;

    /// The form codec's own layout version, not the container's.
    fn version(&self) -> u32;

    /// One line naming the shape held, for `inspect` and for refusals.
    fn shape(&self) -> &'static str;

    /// The exact wire a deed for this schema is written in, for `--help`.
    fn deed_shape(&self) -> &'static str;

    /// Mount stored form octets through the real machine and **re-light a fresh current** off the
    /// result. This never returns the current that deposited the form; that current is gone.
    fn relight(&self, form: &[u8]) -> Result<Box<dyn LitBody>, String>;
}

/// A body that has been re-lit off a stored form.
///
/// It is a live body, not an image: it can be asked for its contemporary form at any moment, and
/// presenting a deed to it changes what that form is.
pub trait LitBody {
    /// Take the body's contemporary form. Never its currents — the currents are not representable
    /// here and no method returns them.
    fn form(&self) -> Result<Vec<u8>, String>;

    /// The census of the contemporary form, computed from this body rather than read from a file.
    fn census(&self) -> Result<Census, String>;

    /// Present one further deed at the body's mouth. Implementations receive the deed; the
    /// zero-return control is enforced above them in [`present_and_require_change`].
    fn present(&mut self, deed: &[u8]) -> Result<(), String>;
}

/// Present one deed and **require the body to change**.
///
/// `CLAUDE.md` §8: *a law that returns zero proves nothing about itself.* A re-lit body that
/// accepted a deed and stayed exactly as it was would satisfy every digest and every extent in the
/// container and still be inert, which is the failure a plate is most likely to hide. So the
/// mechanism itself demands the proof: a deed that leaves the form byte-identical is refused, and
/// the refusal says so.
///
/// Returns the before/after censuses so a caller can report which fields moved.
pub fn present_and_require_change(
    body: &mut dyn LitBody,
    deed: &[u8],
) -> Result<(Census, Census), ResumeRefusal> {
    let before_form = body
        .form()
        .map_err(|detail| ResumeRefusal::FormRefused { detail })?;
    let before = body
        .census()
        .map_err(|detail| ResumeRefusal::FormRefused { detail })?;
    body.present(deed)
        .map_err(|detail| ResumeRefusal::DeedRefused { detail })?;
    let after_form = body
        .form()
        .map_err(|detail| ResumeRefusal::FormRefused { detail })?;
    if after_form == before_form {
        return Err(ResumeRefusal::DeedChangedNothing {
            deed_octets: deed.len(),
            form_octets: after_form.len(),
        });
    }
    let after = body
        .census()
        .map_err(|detail| ResumeRefusal::FormRefused { detail })?;
    Ok((before, after))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResumeRefusal {
    Plate(PlateRefusal),
    /// The plate names a schema this reader does not hold. It is refused, not guessed at.
    ///
    /// `version` is `None` when the tag was supplied without one — a deposit names a schema by tag
    /// and takes the held codec's version, so there is no version to report and reporting a `0`
    /// would invent one.
    SchemaUnheld {
        tag: SchemaTag,
        version: Option<u32>,
        held: Vec<String>,
    },
    /// The tag is held and the codec version is not. Refused for the same reason: a version this
    /// reader does not hold is a different form, and reading it as the version it does hold would
    /// be a guess.
    SchemaVersionUnheld {
        tag: SchemaTag,
        found: u32,
        held: u32,
    },
    /// The schema's own codec refused the stored form.
    FormRefused {
        detail: String,
    },
    /// The form mounted, but re-taking it from the mounted body did not return the deposited
    /// octets. The plate holds something that is not a canonical form of its own schema.
    FormNotCanonical {
        tag: SchemaTag,
        deposited: usize,
        retaken: usize,
    },
    /// The plate's declared census and the re-lit body's census disagree.
    CensusDrift {
        field: String,
        declared: u64,
        relit: u64,
    },
    /// The plate declares a field the re-lit body does not carry.
    CensusFieldUnheld {
        field: String,
    },
    /// The re-lit body carries a field the plate never declared.
    CensusFieldUndeclared {
        field: String,
    },
    DeedRefused {
        detail: String,
    },
    /// The zero-return control, fired.
    DeedChangedNothing {
        deed_octets: usize,
        form_octets: usize,
    },
}

impl ResumeRefusal {
    pub(crate) fn from_disagreement(disagreement: CensusDisagreement) -> Self {
        match disagreement {
            CensusDisagreement::Drift {
                field,
                declared,
                relit,
            } => Self::CensusDrift {
                field,
                declared,
                relit,
            },
            CensusDisagreement::FieldUnheld { field } => Self::CensusFieldUnheld { field },
            CensusDisagreement::FieldUndeclared { field } => Self::CensusFieldUndeclared { field },
        }
    }
}

impl From<PlateRefusal> for ResumeRefusal {
    fn from(refusal: PlateRefusal) -> Self {
        Self::Plate(refusal)
    }
}

impl fmt::Display for ResumeRefusal {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Plate(refusal) => write!(out, "{refusal}"),
            Self::SchemaUnheld { tag, version, held } => write!(
                out,
                "REFUSED: schema {}, which this reader does not hold.\n         held: {}\n         \
                 A plate is not resumed by guessing which held schema it resembles.",
                match version {
                    Some(version) => format!("{tag}/{version}"),
                    None => tag.to_string(),
                },
                held.join(", ")
            ),
            Self::SchemaVersionUnheld { tag, found, held } => write!(
                out,
                "REFUSED: the plate declares schema {tag}/{found}; this reader holds {tag}/{held}. \
                 \n         A form at another codec version is another form, and reading it as \
                 this one would be a guess."
            ),
            Self::FormRefused { detail } => {
                write!(out, "REFUSED: the schema refused the stored form: {detail}")
            }
            Self::FormNotCanonical {
                tag,
                deposited,
                retaken,
            } => write!(
                out,
                "REFUSED: the {deposited} stored octets mounted as {tag}, but re-taking the form \
                 from the mounted body returned {retaken} octets that are not the same.\n         \
                 The plate does not hold a canonical form of the schema it declares."
            ),
            Self::CensusDrift {
                field,
                declared,
                relit,
            } => write!(
                out,
                "REFUSED: CENSUS drift -- the plate declares `{field}`={declared}; the re-lit body \
                 carries `{field}`={relit}.\n         Both digests hold, so the octets did not \
                 move: the plate's declaration was never true of the form it seals."
            ),
            Self::CensusFieldUnheld { field } => write!(
                out,
                "REFUSED: the plate declares the census field `{field}`, which the re-lit body \
                 does not carry."
            ),
            Self::CensusFieldUndeclared { field } => write!(
                out,
                "REFUSED: the re-lit body carries the census field `{field}`, which the plate \
                 never declared."
            ),
            Self::DeedRefused { detail } => {
                write!(out, "REFUSED: the re-lit body refused the deed: {detail}")
            }
            Self::DeedChangedNothing {
                deed_octets,
                form_octets,
            } => write!(
                out,
                "REFUSED: the re-lit body took {deed_octets} deed octets and its {form_octets}-octet \
                 form did not move.\n         A body that resumes inert satisfies every digest in \
                 the container and is still worthless; a law that returns zero proves nothing about \
                 itself."
            ),
        }
    }
}

impl std::error::Error for ResumeRefusal {}
