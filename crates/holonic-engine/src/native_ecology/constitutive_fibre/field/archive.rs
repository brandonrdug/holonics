//! Exact exterior placement of immutable historical sections. Current numerical standing stays
//! resident; a later addressed source mounts its original carriers, without developmental replay.
use super::rest::{HeldRest, point_bytes, read_point};
use super::*;
use super::junction::operative::{HeldOperative,rest::OperativeHistoryRest};
use crate::native_ecology::constitutive_fibre::circulation::rest::{blob, read_blob};
use sha2::{Digest, Sha256};
use std::{
    cell::RefCell,
    fs::{File, OpenOptions},
    io::{Read, Seek, SeekFrom, Write},
    path::Path,
};

type Error = ConstitutiveFibreError;
fn error(e: impl std::fmt::Display) -> Error {
    Error::Rest(format!("field history placement: {e}"))
}

pub(super) struct FieldArchive {
    file: Rc<RefCell<File>>,
    written_octets: u64,
    restored_sources: u64,
    archived_until: usize,
    remounted: std::collections::BTreeSet<usize>,
    section_read_outs: u64,
    egress_section_octets: u64,
}

#[cfg(test)]
mod tests;
#[derive(Clone)]
pub(super) struct ArchivedField {
    file: Rc<RefCell<File>>,
    offset: u64,
    octets: u64,
    digest: [u8; 32],
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct NativeFieldHistoryPlacement {
    pub resident_occurrences: usize,
    pub archived_occurrences: usize,
    pub archive_written_octets: u64,
    pub restored_sources: u64,
    pub archive_section_read_outs: u64,
    pub archive_egress_section_octets: u64,
}

impl FieldArchive {
    pub(super) fn create(path: &Path) -> Result<Self, Error> {
        let mut options = OpenOptions::new();
        options.read(true).write(true).create_new(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt;
            options.mode(0o600);
        }
        let mut file = options.open(path).map_err(error)?;
        let magic = b"HNA-NATIVE-FIELD-HISTORY\x01";
        file.write_all(magic).map_err(error)?;
        file.sync_all().map_err(error)?;
        Ok(Self {
            file: Rc::new(RefCell::new(file)),
            written_octets: magic.len() as u64,
            restored_sources: 0,
            archived_until: 0,
            remounted: std::collections::BTreeSet::new(),
            section_read_outs: 0,
            egress_section_octets: 0,
        })
    }
    pub(super) fn append(&mut self, rest: &HeldRest) -> Result<ArchivedField, Error> {
        let mut bytes = vec![
            u8::from(rest.junction.is_some()),
            u8::from(rest.transport.is_some()) | (u8::from(rest.incoming.is_some()) << 1) | (u8::from(rest.operative.is_some())<<2),
        ];
        blob(&mut bytes, &point_bytes(&rest.source)?)?;
        for section in [&rest.junction, &rest.transport, &rest.incoming]
            .into_iter()
            .flatten()
        {
            blob(&mut bytes, &point_bytes(section)?)?;
        }
        if let Some(op)=&rest.operative {op.write(&mut |s|blob(&mut bytes,&point_bytes(s)?))?;}
        let digest: [u8; 32] = Sha256::digest(&bytes).into();
        let mut file = self.file.borrow_mut();
        let offset = file.seek(SeekFrom::End(0)).map_err(error)?;
        file.write_all(&bytes).map_err(error)?;
        self.written_octets = file.stream_position().map_err(error)?;
        Ok(ArchivedField {
            file: Rc::clone(&self.file),
            offset,
            octets: bytes.len() as u64,
            digest,
        })
    }
    pub(super) fn sync(&self) -> Result<(), Error> {
        self.file.borrow().sync_data().map_err(error)
    }
    pub(super) fn note_archived_prefix(&mut self, until: usize) {
        self.archived_until = until;
    }
}
impl ArchivedField {
    pub(super) fn read(&self) -> Result<HeldRest, Error> {
        let mut file = self.file.borrow_mut();
        file.seek(SeekFrom::Start(self.offset)).map_err(error)?;
        let count = usize::try_from(self.octets).map_err(error)?;
        let mut bytes = Vec::new();
        bytes.try_reserve_exact(count).map_err(error)?;
        (&mut *file)
            .take(self.octets)
            .read_to_end(&mut bytes)
            .map_err(error)?;
        if bytes.len() != count || Sha256::digest(&bytes).as_slice() != self.digest {
            return Err(error("historical section extent or wire checksum"));
        }
        if bytes.len() < 2 || bytes[0] > 1 || bytes[1] > 7 {
            return Err(error("historical section presence"));
        }
        let mut input = (&bytes[2..]).take(self.octets - 2);
        let source = read_point(&read_blob(&mut input)?)?;
        let junction = (bytes[0] == 1)
            .then(|| read_point(&read_blob(&mut input)?))
            .transpose()?;
        let transport = (bytes[1] & 1 == 1)
            .then(|| read_point(&read_blob(&mut input)?))
            .transpose()?;
        let incoming = (bytes[1] & 2 != 0)
            .then(|| read_point(&read_blob(&mut input)?))
            .transpose()?;
        let operative=(bytes[1]&4!=0).then(||OperativeHistoryRest::read(&mut ||read_point(&read_blob(&mut input)?))).transpose()?;
        if input.limit() != 0 {
            return Err(error("trailing historical section bytes"));
        }
        Ok(HeldRest {
            operative,
            source,
            incoming,
            junction,
            transport,
        })
    }
}

impl<'chart> ResidentFieldHistory<'chart> {
    pub(super) fn mount(
        surface: &'chart ResidentSurface<'chart>,
        rest: HeldRest,
    ) -> Result<Self, Error> {
        Ok(Self {
            operative: rest.operative.map(|op|HeldOperative::mount(surface,op)).transpose()?,
            section: surface.mount_section_rest(&rest.source)?,
            incoming: rest
                .incoming
                .map(|s| surface.mount_section_rest(&s).map(Rc::new))
                .transpose()?,
            junction: rest
                .junction
                .map(|s| surface.mount_section_rest(&s).map(Rc::new))
                .transpose()?,
            transport: rest
                .transport
                .map(|s| surface.mount_section_rest(&s).map(Rc::new))
                .transpose()?,
        })
    }
    fn rest(&self, surface: &ResidentSurface<'chart>) -> Result<HeldRest, Error> {
        Ok(HeldRest {
            operative:self.operative.as_ref().map(|o|o.rest(surface)).transpose()?,
            source: surface.detach_section(&self.section, 64)?,
            incoming: self
                .incoming
                .as_ref()
                .map(|s| surface.detach_section(s, 64))
                .transpose()?,
            junction: self
                .junction
                .as_ref()
                .map(|s| surface.detach_section(s, 64))
                .transpose()?,
            transport: self
                .transport
                .as_ref()
                .map(|s| surface.detach_section(s, 64))
                .transpose()?,
        })
    }
}
impl<'chart> HeldField<'chart> {
    pub(super) fn incoming_rest(
        &self,
        surface: &ResidentSurface<'chart>,
    ) -> Result<Option<ResidentSectionRest>, Error> {
        match &self.resident {
            Some(resident) => resident
                .incoming
                .as_ref()
                .map(|s| surface.detach_section(s, 64).map_err(Error::from))
                .transpose(),
            None => Ok(self.rest(surface)?.incoming),
        }
    }
    pub(super) fn source_rest(
        &self,
        surface: &ResidentSurface<'chart>,
    ) -> Result<ResidentSectionRest, Error> {
        match &self.resident {
            Some(resident) => Ok(surface.detach_section(&resident.section, 64)?),
            None => Ok(self.rest(surface)?.source),
        }
    }
    pub(super) fn junction_rest(
        &self,
        surface: &ResidentSurface<'chart>,
    ) -> Result<Option<ResidentSectionRest>, Error> {
        match &self.resident {
            Some(resident) => resident
                .junction
                .as_ref()
                .map(|s| surface.detach_section(s, 64).map_err(Error::from))
                .transpose(),
            None => Ok(self.rest(surface)?.junction),
        }
    }
    pub(super) fn transport_rest(
        &self,
        surface: &ResidentSurface<'chart>,
    ) -> Result<Option<ResidentSectionRest>, Error> {
        match &self.resident {
            Some(resident) => resident
                .transport
                .as_ref()
                .map(|s| surface.detach_section(s, 64).map_err(Error::from))
                .transpose(),
            None => Ok(self.rest(surface)?.transport),
        }
    }
    pub(super) fn resident(&self) -> Result<&ResidentFieldHistory<'chart>, Error> {
        self.resident
            .as_ref()
            .ok_or_else(|| error("historical source has not been placed on the device"))
    }
    pub(super) fn rest(&self, surface: &ResidentSurface<'chart>) -> Result<HeldRest, Error> {
        match (&self.resident, &self.archived) {
            (Some(resident), _) => resident.rest(surface),
            (None, Some(archived)) => archived.read(),
            (None, None) => Err(error("historical carrier is absent")),
        }
    }
    pub(super) fn with_resident<R>(
        &self,
        surface: &'chart ResidentSurface<'chart>,
        read: impl FnOnce(&ResidentFieldHistory<'chart>) -> Result<R, Error>,
    ) -> Result<R, Error> {
        if let Some(resident) = &self.resident {
            return read(resident);
        }
        // This is a specifically requested receiver over an immutable source, not a second
        // ecology. Native calculation still uses the resident device receiver.
        let mounted = ResidentFieldHistory::mount(surface, self.rest(surface)?)?;
        read(&mounted)
    }
}

impl<'chart> NativeConstitutiveField<'chart> {
    /// Start a fresh append-only exterior chart owned by this continuing field. No placement
    /// changes yet. Existing files refuse; an archive is not an independent native model.
    pub fn enable_history_archive(&mut self, path: impl AsRef<Path>) -> Result<(), Error> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(Error::Uncertain);
        }
        if self.archive.is_some() {
            return Err(error("history archive already exists"));
        }
        self.archive = Some(FieldArchive::create(path.as_ref())?);
        Ok(())
    }
    pub fn history_placement(&self) -> NativeFieldHistoryPlacement {
        NativeFieldHistoryPlacement {
            resident_occurrences: self.archive.as_ref().map_or(self.history.len(), |a| {
                self.history.len() - a.archived_until + a.remounted.len()
            }),
            archived_occurrences: self.archive.as_ref().map_or(0, |a| a.archived_until),
            archive_written_octets: self.archive.as_ref().map_or(0, |a| a.written_octets),
            restored_sources: self.archive.as_ref().map_or(0, |a| a.restored_sources),
            archive_section_read_outs: self.archive.as_ref().map_or(0, |a| a.section_read_outs),
            archive_egress_section_octets: self
                .archive
                .as_ref()
                .map_or(0, |a| a.egress_section_octets),
        }
    }
    pub fn has_history_archive(&self) -> bool {
        self.archive.is_some()
    }
    /// Transfer historical carriers before this exterior boundary to exact durable placement.
    /// The newest source and contemporary junction remain resident. All writes are made durable
    /// before any historical device section is released; failure retains the old placement.
    pub fn archive_history_before(
        &mut self,
        before: usize,
    ) -> Result<NativeFieldHistoryPlacement, Error> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(Error::Uncertain);
        }
        if before > self.history.len() {
            return Err(Error::ForeignOccurrence);
        }
        let until = before.min(self.history.len().saturating_sub(1));
        let archive = self
            .archive
            .as_mut()
            .ok_or_else(|| error("no declared exterior history chart"))?;
        let positions = (archive.archived_until..until)
            .chain(archive.remounted.range(..until).copied())
            .collect::<Vec<_>>();
        let before_transfer = self.relation.surface.census();
        let staged = (|| -> Result<Vec<(usize, ArchivedField)>, Error> {
            let mut staged = Vec::new();
            staged.try_reserve(positions.len()).map_err(error)?;
            for at in positions {
                let held = &self.history[at];
                if held.resident.is_none() {
                    continue;
                }
                let exterior = match &held.archived {
                    Some(exterior) => exterior.clone(),
                    None => archive.append(&held.rest(self.relation.surface)?)?,
                };
                staged.push((at, exterior));
            }
            archive.sync()?;
            Ok(staged)
        })();
        let after_transfer = self.relation.surface.census();
        archive.section_read_outs +=
            after_transfer.section_read_outs - before_transfer.section_read_outs;
        archive.egress_section_octets +=
            after_transfer.egress_section_octets - before_transfer.egress_section_octets;
        let staged = staged?;
        for (at, exterior) in staged {
            self.history[at].archived = Some(exterior);
            self.history[at].resident = None;
            archive.remounted.remove(&at);
        }
        archive.archived_until = archive.archived_until.max(until);
        Ok(self.history_placement())
    }
    pub(super) fn mount_history_source(&mut self, at: usize) -> Result<(), Error> {
        let held = self.history.get_mut(at).ok_or(Error::ForeignOccurrence)?;
        if held.resident.is_some() {
            return Ok(());
        }
        let mounted =
            ResidentFieldHistory::mount(self.relation.surface, held.rest(self.relation.surface)?)?;
        held.resident = Some(mounted);
        if let Some(archive) = &mut self.archive {
            archive.restored_sources += 1;
            archive.remounted.insert(at);
        }
        Ok(())
    }
}
