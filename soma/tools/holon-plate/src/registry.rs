//! The three operations: deposit a form, resume a plate, inspect a plate.
//!
//! ```text
//!   deposit   form octets  ──mount──▶  a body  ──▶  census + seal  ──▶  plate.holon
//!   resume    plate.holon  ──open──▶  verified  ──relight──▶  a FRESH current
//!   inspect   plate.holon  ──open──▶  verified  ──▶  reported, no body lit
//! ```
//!
//! `deposit` and `resume` both mount. That is deliberate and it is the round-trip discipline:
//! octets that hash correctly but do not mount are not a deposit, and a plate is never written
//! from octets nobody has put through a machine.
//!
//! `inspect` does **not** mount, and says so in its own report, because an inspection that lit a
//! body would be a resume wearing another name.

use crate::census::Census;
use crate::plate::{self, PlateRefusal, ReadPlate, SchemaTag};
use crate::schema::{PlateSchema, ResumeRefusal};
use crate::schemas::{CURRENT_SCHEMA, REBASE_SCHEMA, TRAINING_SCHEMA};

/// Every schema this reader holds. The set is fixed at compile time and enumerable at run time,
/// which is what lets a refusal print what *is* held beside what was asked for.
pub fn held_schemas() -> Vec<&'static dyn PlateSchema> {
    vec![&TRAINING_SCHEMA, &CURRENT_SCHEMA, &REBASE_SCHEMA]
}

fn held_names() -> Vec<String> {
    held_schemas()
        .iter()
        .map(|schema| format!("{}/{}", schema.tag(), schema.version()))
        .collect()
}

/// Resolve a tag and version to a held schema, or refuse by name. There is no nearest match and no
/// fallback: an unheld tag and an unheld version are two different refusals and both are terminal.
pub fn schema_for(tag: SchemaTag, version: u32) -> Result<&'static dyn PlateSchema, ResumeRefusal> {
    let by_tag: Vec<&'static dyn PlateSchema> = held_schemas()
        .into_iter()
        .filter(|schema| schema.tag() == tag)
        .collect();
    let Some(schema) = by_tag.first().copied() else {
        return Err(ResumeRefusal::SchemaUnheld {
            tag,
            version: Some(version),
            held: held_names(),
        });
    };
    if schema.version() != version {
        return Err(ResumeRefusal::SchemaVersionUnheld {
            tag,
            found: version,
            held: schema.version(),
        });
    }
    Ok(schema)
}

/// What a deposit returned.
#[derive(Debug)]
pub struct Deposited {
    pub plate: Vec<u8>,
    pub tag: SchemaTag,
    pub schema_version: u32,
    pub census: Census,
    pub form_octets: usize,
    pub form_sha256: String,
    pub plate_sha256: String,
}

/// Deposit one FORM.
///
/// The form octets are mounted through the schema's real machine, the form is **re-taken from the
/// mounted body**, and the two must be byte-identical before anything is written. A plate is
/// therefore never sealed around octets that only look like a form.
///
/// The census is computed from the mounted body, never parsed out of the input, which is what
/// makes it a second frame rather than a copy of the first.
///
/// No current is deposited. The currents that ran to bring the body to this form are not in the
/// returned octets and cannot be.
pub fn deposit(tag: SchemaTag, form: &[u8]) -> Result<Deposited, ResumeRefusal> {
    let schema = held_schemas()
        .into_iter()
        .find(|schema| schema.tag() == tag)
        .ok_or_else(|| ResumeRefusal::SchemaUnheld {
            tag,
            // a deposit names a schema by tag and takes the held codec's version, so there is no
            // declared version to report here
            version: None,
            held: held_names(),
        })?;
    let body = schema
        .relight(form)
        .map_err(|detail| ResumeRefusal::FormRefused { detail })?;
    let retaken = body
        .form()
        .map_err(|detail| ResumeRefusal::FormRefused { detail })?;
    if retaken != form {
        return Err(ResumeRefusal::FormNotCanonical {
            tag,
            deposited: form.len(),
            retaken: retaken.len(),
        });
    }
    let census = body
        .census()
        .map_err(|detail| ResumeRefusal::FormRefused { detail })?;
    let plate = plate::seal(tag, schema.version(), &census, form);
    let read = plate::open(&plate).map_err(ResumeRefusal::Plate)?;
    Ok(Deposited {
        plate,
        tag,
        schema_version: schema.version(),
        census,
        form_octets: form.len(),
        form_sha256: read.form_digest_hex(),
        plate_sha256: read.plate_digest_hex(),
    })
}

/// What a resume returned: a **fresh** body, lit off the stored form.
pub struct Relit {
    pub body: Box<dyn crate::schema::LitBody>,
    pub tag: SchemaTag,
    pub schema_version: u32,
    /// The census the plate declared.
    pub declared: Census,
    /// The census recomputed from the body that was re-lit. Equal to `declared` or this would have
    /// refused.
    pub relit: Census,
    pub form_octets: usize,
    pub form_sha256: String,
    pub plate_sha256: String,
}

// The live body is deliberately absent from this rendering. A body is not a value to be printed;
// what a caller can report about it is its contemporary form and that form's census, both of which
// are here.
impl std::fmt::Debug for Relit {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        out.debug_struct("Relit")
            .field("tag", &self.tag)
            .field("schema_version", &self.schema_version)
            .field("census", &self.relit)
            .field("form_octets", &self.form_octets)
            .field("form_sha256", &self.form_sha256)
            .field("plate_sha256", &self.plate_sha256)
            .field("body", &"<a re-lit body, not a value>")
            .finish()
    }
}

/// Resume one plate: verify it, then **re-light a fresh current** off the form it holds.
///
/// This is not a restore. The body returned here has never received anything; it is a new body
/// carrying the deposited form's organization. The current that deposited the plate died as it
/// flowed and no operation returns it.
///
/// Four gates, in order, each with its own refusal:
///
/// 1. the container — magic, version, extents, both digests;
/// 2. the schema — held tag, held version, no fallback;
/// 3. the form — it must mount, and re-taking it from the mounted body must return the same
///    octets;
/// 4. the census — the plate's declaration must agree with the re-lit body field for field.
pub fn resume(octets: &[u8]) -> Result<Relit, ResumeRefusal> {
    let read = plate::open(octets).map_err(ResumeRefusal::Plate)?;
    let form_sha256 = read.form_digest_hex();
    let plate_sha256 = read.plate_digest_hex();
    let schema = schema_for(read.tag, read.schema_version)?;
    let body = schema
        .relight(&read.form)
        .map_err(|detail| ResumeRefusal::FormRefused { detail })?;
    let retaken = body
        .form()
        .map_err(|detail| ResumeRefusal::FormRefused { detail })?;
    if retaken != read.form {
        return Err(ResumeRefusal::FormNotCanonical {
            tag: read.tag,
            deposited: read.form.len(),
            retaken: retaken.len(),
        });
    }
    let relit = body
        .census()
        .map_err(|detail| ResumeRefusal::FormRefused { detail })?;
    if let Some(disagreement) = read.census.first_disagreement(&relit) {
        return Err(ResumeRefusal::from_disagreement(disagreement));
    }
    Ok(Relit {
        body,
        tag: read.tag,
        schema_version: read.schema_version,
        declared: read.census,
        relit,
        form_octets: read.form.len(),
        form_sha256,
        plate_sha256,
    })
}

/// Re-deposit a body that is already in hand. Used after presenting a further deed.
pub fn redeposit(
    tag: SchemaTag,
    body: &dyn crate::schema::LitBody,
) -> Result<Deposited, ResumeRefusal> {
    let form = body
        .form()
        .map_err(|detail| ResumeRefusal::FormRefused { detail })?;
    deposit(tag, &form)
}

/// What an inspection reported.
pub struct Inspection {
    pub tag: SchemaTag,
    pub schema_version: u32,
    /// `None` when the plate names a schema this reader does not hold. That is reported here
    /// rather than refused, because reporting an unheld schema is exactly what an inspection is
    /// for; [`resume`] is where it becomes terminal.
    pub shape: Option<&'static str>,
    pub held: bool,
    pub census: Census,
    pub plate_octets: usize,
    pub form_octets: usize,
    pub census_octets: usize,
    pub form_sha256: String,
    pub plate_sha256: String,
}

/// Inspect one plate without lighting a body.
///
/// Verifies the container and both digests and reports the head, the census, and whether the
/// schema is held. It does **not** mount the form, so nothing it reports is evidence that a body
/// would come out — that claim belongs to [`resume`] and only [`resume`] can make it.
pub fn inspect(octets: &[u8]) -> Result<Inspection, PlateRefusal> {
    let read: ReadPlate = plate::open(octets)?;
    let form_sha256 = read.form_digest_hex();
    let plate_sha256 = read.plate_digest_hex();
    let held_schema = schema_for(read.tag, read.schema_version).ok();
    let census_octets = octets.len() - plate::HEAD_OCTETS - plate::SEAL_OCTETS - read.form.len();
    Ok(Inspection {
        tag: read.tag,
        schema_version: read.schema_version,
        shape: held_schema.map(|schema| schema.shape()),
        held: held_schema.is_some(),
        census_octets,
        census: read.census,
        plate_octets: octets.len(),
        form_octets: read.form.len(),
        form_sha256,
        plate_sha256,
    })
}
