//! Native field persistence through the engine's existing wire. Exterior codec/delivery state
//! remains with its application; a saved field is not an implicit saved text or audio session.
//! The existing field wire retains per-occurrence numerical history. This wrapper does not
//! condense that history into learned generators or make it optional for contextual prediction.
use super::*;
use crate::publication::{publish_new, PublicationReceipt};
use holonic_engine::native_ecology::constitutive_fibre::{
    NativeFieldEmission, NativeFieldRest, NativeFieldSourceAnchor,
};
use std::{
    fs::File,
    io::{self, BufReader, BufWriter, Write},
    path::Path,
};

/// One cold field representation, consumed when remounted. Its source/anchor slots retain
/// native capabilities; array positions are delivery coordinates, not semantic identities.
pub struct NativeSavedField {
    rest: NativeFieldRest,
}

impl NativeSavedField {
    pub fn from_rest(rest: NativeFieldRest) -> Self {
        Self { rest }
    }
    pub fn into_rest(self) -> NativeFieldRest {
        self.rest
    }
    pub fn nodes(&self) -> usize {
        self.rest.nodes()
    }
    pub fn occurrences(&self) -> usize {
        self.rest.occurrences()
    }
    pub fn source_slots(&self) -> &[Option<usize>] {
        self.rest.source_slots()
    }
    pub fn anchor_slots(&self) -> &[Option<usize>] {
        self.rest.anchor_slots()
    }
    pub fn material_source(&self) -> Option<NativeMaterialTransportSource> {
        self.rest.material_transport_source()
    }
    pub fn material_target(&self) -> Option<NativeMaterialTarget> {
        self.rest.material_target()
    }

    /// Read the existing native field wire with its complete structural validation. This does
    /// not accept a text-session envelope or assert authenticity of externally supplied history.
    pub fn read(path: impl AsRef<Path>) -> Result<Self, NativeSessionError> {
        let file = File::open(path)?;
        let octets = file.metadata()?.len();
        Ok(Self::from_rest(NativeFieldRest::read(
            &mut BufReader::new(file),
            octets,
        )?))
    }

    /// Publish a new native field artifact without replacing another file. This borrows cold
    /// representation, never the live field's ownership. Application cursors are separate data.
    pub fn publish(
        &self,
        path: impl AsRef<Path>,
    ) -> Result<PublicationReceipt<()>, NativeSessionError> {
        Ok(publish_new(path, |file| {
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                file.set_permissions(std::fs::Permissions::from_mode(0o600))?;
            }
            let mut out = BufWriter::new(file);
            self.rest.write(&mut out).map_err(io::Error::other)?;
            out.flush()
        })?)
    }

    pub fn with_field<R, E>(
        self,
        operation: impl FnOnce(
            &mut NativeConstitutiveField<'_>,
            Vec<Option<NativeFieldEmission>>,
            Vec<Option<NativeFieldSourceAnchor>>,
        ) -> Result<R, E>,
    ) -> Result<R, E>
    where
        E: From<NativeSessionError>,
    {
        self.with_field_placed(None, operation)
    }

    /// Native standing remounts while older source carriers use a newly created archive.
    /// The complete checkpoint is sufficient; no previous machine's archive path is required.
    pub fn with_field_archived<R, E>(
        self,
        path: impl AsRef<Path>,
        operation: impl FnOnce(
            &mut NativeConstitutiveField<'_>,
            Vec<Option<NativeFieldEmission>>,
            Vec<Option<NativeFieldSourceAnchor>>,
        ) -> Result<R, E>,
    ) -> Result<R, E>
    where
        E: From<NativeSessionError>,
    {
        self.with_field_placed(Some(path.as_ref()), operation)
    }

    pub(crate) fn with_field_placed<R, E>(
        self,
        archive: Option<&Path>,
        operation: impl FnOnce(
            &mut NativeConstitutiveField<'_>,
            Vec<Option<NativeFieldEmission>>,
            Vec<Option<NativeFieldSourceAnchor>>,
        ) -> Result<R, E>,
    ) -> Result<R, E>
    where
        E: From<NativeSessionError>,
    {
        let readout = ResidentReadout::new()
            .map_err(|e| E::from(NativeSessionError::Application(e.to_string())))?;
        let surface = ResidentSurface::on(&readout)
            .map_err(|e| E::from(NativeSessionError::Application(e.to_string())))?;
        let result = match archive {
            Some(path) => {
                NativeConstitutiveField::remount_with_history_archive(&surface, self.rest, path)
            }
            None => NativeConstitutiveField::remount(&surface, self.rest),
        };
        let (mut field, sources, anchors) =
            result.map_err(NativeSessionError::from).map_err(E::from)?;
        operation(&mut field, sources, anchors)
    }
}
