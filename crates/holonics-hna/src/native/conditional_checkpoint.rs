//! Durable composition of a conditional relation, its retained condition current, and the
//! native field that supplies the receiver.  This is a cold wire boundary: remount installs the
//! three existing owners and returns their explicitly retained capabilities without replaying a
//! native operation or manufacturing a source map.

use crate::checkpoint::{hash_prefix, read_blob, read_transport, write_len, write_transport};
use crate::publication::{publish_new, PublicationError, PublicationReceipt};
use crate::HnaStreamState;
use holonic_engine::native_ecology::constitutive_fibre::{
    ConstitutiveFibreError, ConstitutiveSourceChart, NativeConstitutiveField, NativeFieldEmission,
    NativeFieldRest, NativeFieldSourceAnchor, ResidentConditionCurrent,
    ResidentConditionCurrentRest, ResidentConstitutiveFibre, ResidentConstitutiveFibreRest,
};
use holonic_engine::resident_section::ResidentSurface;
use std::fs::File;
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::Path;
use thiserror::Error;

const MAGIC: &[u8] = b"HNA-CONDITIONAL-FIELD\x01";
const END: &[u8] = b"HNA-CONDITIONAL-FIELD-END\x01";

#[derive(Debug, Error)]
pub enum ConditionalCheckpointError {
    #[error("conditional checkpoint I/O: {0}")]
    Io(#[from] io::Error),
    #[error("conditional checkpoint publication: {0}")]
    Publication(#[from] PublicationError),
    #[error("conditional checkpoint envelope: {0}")]
    Checkpoint(#[from] crate::checkpoint::CheckpointError),
    #[error("conditional checkpoint native rest: {0}")]
    Engine(#[from] ConstitutiveFibreError),
    #[error("conditional checkpoint composition: {0}")]
    Composition(String),
    #[error("conditional checkpoint checksum mismatch")]
    Checksum,
}

/// A complete cold composition.  The field rest owns its own source and anchor slot metadata;
/// relation and condition rests intentionally own no source capabilities.
pub struct NativeSavedConditionalField {
    relation: ResidentConstitutiveFibreRest,
    condition: ResidentConditionCurrentRest,
    field: NativeFieldRest,
    stream: HnaStreamState,
    application: Vec<u8>,
}

impl NativeSavedConditionalField {
    pub fn relation(&self) -> &ResidentConstitutiveFibreRest {
        &self.relation
    }

    pub fn condition(&self) -> &ResidentConditionCurrentRest {
        &self.condition
    }

    pub fn field(&self) -> &NativeFieldRest {
        &self.field
    }

    pub fn stream(&self) -> &HnaStreamState {
        &self.stream
    }

    pub fn application(&self) -> &[u8] {
        &self.application
    }

    pub fn source_slots(&self) -> &[Option<usize>] {
        self.field.source_slots()
    }

    pub fn anchor_slots(&self) -> &[Option<usize>] {
        self.field.anchor_slots()
    }

    pub fn read(path: impl AsRef<Path>) -> Result<Self, ConditionalCheckpointError> {
        let mut file = File::open(path)?;
        let length = file.metadata()?.len();
        let minimum = (MAGIC.len() + END.len() + 32 + 8) as u64;
        if length < minimum {
            return Err(ConditionalCheckpointError::Composition(
                "minimum checkpoint frame".into(),
            ));
        }
        let footer = length - END.len() as u64 - 32;
        file.seek(SeekFrom::Start(footer))?;
        let mut digest = [0; 32];
        file.read_exact(&mut digest)?;
        let mut end = vec![0; END.len()];
        file.read_exact(&mut end)?;
        if end != END {
            return Err(ConditionalCheckpointError::Composition(
                "footer marker".into(),
            ));
        }
        if hash_prefix(&mut file, footer)? != digest {
            return Err(ConditionalCheckpointError::Checksum);
        }

        file.seek(SeekFrom::Start(0))?;
        let mut magic = vec![0; MAGIC.len()];
        file.read_exact(&mut magic)?;
        if magic != MAGIC {
            return Err(ConditionalCheckpointError::Composition(
                "checkpoint kind/version".into(),
            ));
        }
        let stream = read_transport(&mut file, footer)?;
        let application = read_blob(&mut file, footer)?;
        let mut extent_bytes = [0; 8];
        file.read_exact(&mut extent_bytes)?;
        let extent = u64::from_le_bytes(extent_bytes);
        let start = file.stream_position()?;
        if start.checked_add(extent) != Some(footer) {
            return Err(ConditionalCheckpointError::Composition(
                "native composition extent".into(),
            ));
        }

        let relation = read_rest(&mut file, footer, |input, length| {
            ResidentConstitutiveFibreRest::read(input, length)
        })?;
        let condition = read_rest(&mut file, footer, |input, length| {
            ResidentConditionCurrentRest::read(input, length)
        })?;
        let field = read_rest(&mut file, footer, |input, length| {
            NativeFieldRest::read(input, length)
        })?;
        if file.stream_position()? != footer {
            return Err(ConditionalCheckpointError::Composition(
                "trailing native composition bytes".into(),
            ));
        }
        let saved = Self {
            relation,
            condition,
            field,
            stream,
            application,
        };
        saved.validate()?;
        Ok(saved)
    }

    pub fn validate(&self) -> Result<(), ConditionalCheckpointError> {
        self.relation.validate()?;
        self.condition.validate()?;
        self.field.validate()?;
        self.stream
            .validate()
            .map_err(|e| ConditionalCheckpointError::Composition(e.to_string()))?;
        validate_composition(&self.relation, &self.condition, &self.field)
    }

    /// Consume the cold composition into the existing three native owners.  The returned vectors
    /// are the exact capability slots supplied when the field was captured.
    pub fn remount<'chart>(
        self,
        surface: &'chart ResidentSurface<'chart>,
    ) -> Result<
        (
            ResidentConstitutiveFibre<'chart>,
            ResidentConditionCurrent<'chart>,
            NativeConstitutiveField<'chart>,
            Vec<Option<NativeFieldEmission>>,
            Vec<Option<NativeFieldSourceAnchor>>,
            HnaStreamState,
            Vec<u8>,
        ),
        ConditionalCheckpointError,
    > {
        self.validate()?;
        let Self {
            relation,
            condition,
            field,
            stream,
            application,
        } = self;
        let relation = ResidentConstitutiveFibre::remount(surface, relation)?;
        let condition = ResidentConditionCurrent::remount(surface, condition)?;
        let (field, sources, anchors) = NativeConstitutiveField::remount(surface, field)?;
        Ok((
            relation,
            condition,
            field,
            sources,
            anchors,
            stream,
            application,
        ))
    }
}

fn validate_composition(
    relation: &ResidentConstitutiveFibreRest,
    condition: &ResidentConditionCurrentRest,
    field: &NativeFieldRest,
) -> Result<(), ConditionalCheckpointError> {
    if relation.source_chart() != condition.source_chart() {
        return Err(ConditionalCheckpointError::Composition(
            "relation and condition source charts differ".into(),
        ));
    }
    let receiver_width = field
        .nodes()
        .checked_mul(2)
        .ok_or_else(|| ConditionalCheckpointError::Composition("receiver width overflow".into()))?;
    if relation.target_width() != receiver_width {
        return Err(ConditionalCheckpointError::Composition(
            "relation receiver width does not match field nodes".into(),
        ));
    }
    if !matches!(
        relation.source_chart(),
        ConstitutiveSourceChart::BilinearContact { .. }
    ) {
        return Err(ConditionalCheckpointError::Composition(
            "conditional checkpoint requires a bilinear relation chart".into(),
        ));
    }
    Ok(())
}

fn read_rest<T>(
    file: &mut File,
    end: u64,
    read: impl FnOnce(&mut io::Take<&mut File>, u64) -> Result<T, ConstitutiveFibreError>,
) -> Result<T, ConditionalCheckpointError> {
    let mut length_bytes = [0; 8];
    file.read_exact(&mut length_bytes)?;
    let length = u64::from_le_bytes(length_bytes);
    if file
        .stream_position()?
        .checked_add(length)
        .is_none_or(|offset| offset > end)
    {
        return Err(ConditionalCheckpointError::Composition(
            "native rest extent".into(),
        ));
    }
    let mut input = file.take(length);
    let rest = read(&mut input, length)?;
    if input.limit() != 0 {
        return Err(ConditionalCheckpointError::Composition(
            "trailing native rest bytes".into(),
        ));
    }
    Ok(rest)
}

/// Capture the three canonical native rests and publish one strict, checksummed checkpoint.
pub fn save_conditional_checkpoint(
    path: impl AsRef<Path>,
    relation: &ResidentConstitutiveFibre<'_>,
    condition: &ResidentConditionCurrent<'_>,
    field: &NativeConstitutiveField<'_>,
    sources: &[Option<&NativeFieldEmission>],
    anchors: &[Option<&NativeFieldSourceAnchor>],
    stream: &HnaStreamState,
    application: &[u8],
) -> Result<PublicationReceipt<()>, ConditionalCheckpointError> {
    let path = path.as_ref();
    if path.exists() {
        return Err(ConditionalCheckpointError::Publication(
            PublicationError::ExistingTarget {
                path: path.to_path_buf(),
            },
        ));
    }
    stream
        .validate()
        .map_err(|e| ConditionalCheckpointError::Composition(e.to_string()))?;
    let relation = relation.rest()?;
    let condition = condition.rest()?;
    let field = field.rest(sources, anchors)?;
    relation.validate()?;
    condition.validate()?;
    field.validate()?;
    validate_composition(&relation, &condition, &field)?;
    let receipt = publish_new(path, |file| {
        file.write_all(MAGIC)?;
        write_transport(file, stream)?;
        write_len(file, application.len())?;
        file.write_all(application)?;
        let extent_at = file.stream_position()?;
        file.write_all(&0u64.to_le_bytes())?;
        let start = file.stream_position()?;
        write_rest_blob(file, |out| relation.write(out).map_err(io::Error::other))?;
        write_rest_blob(file, |out| condition.write(out).map_err(io::Error::other))?;
        write_rest_blob(file, |out| field.write(out).map_err(io::Error::other))?;
        let end = file.stream_position()?;
        file.seek(SeekFrom::Start(extent_at))?;
        file.write_all(&(end - start).to_le_bytes())?;
        let digest = hash_prefix(file, end)?;
        file.seek(SeekFrom::Start(end))?;
        file.write_all(&digest)?;
        file.write_all(END)?;
        Ok(())
    })?;
    Ok(receipt)
}

fn write_rest_blob(
    file: &mut File,
    write: impl FnOnce(&mut io::BufWriter<&mut File>) -> io::Result<()>,
) -> io::Result<()> {
    let length_at = file.stream_position()?;
    file.write_all(&0u64.to_le_bytes())?;
    let start = file.stream_position()?;
    {
        let mut out = io::BufWriter::new(&mut *file);
        write(&mut out)?;
        out.flush()?;
    }
    let end = file.stream_position()?;
    file.seek(SeekFrom::Start(length_at))?;
    file.write_all(&(end - start).to_le_bytes())?;
    file.seek(SeekFrom::Start(end))?;
    Ok(())
}

#[cfg(test)]
mod tests;
