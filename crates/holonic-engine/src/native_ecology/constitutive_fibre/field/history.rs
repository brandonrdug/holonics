//! Resident carriers for the legacy constituted-field occurrence clock.
use super::junction::operative::HeldOperative;
use super::rest::HeldRest;
use super::*;

type Error = ConstitutiveFibreError;

impl<'chart> ResidentFieldHistory<'chart> {
    pub(super) fn mount(
        surface: &'chart ResidentSurface<'chart>,
        rest: HeldRest,
    ) -> Result<Self, Error> {
        Ok(Self {
            operative: rest
                .operative
                .map(|op| HeldOperative::mount(surface, op))
                .transpose()?,
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
            operative: self
                .operative
                .as_ref()
                .map(|o| o.rest(surface))
                .transpose()?,
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
        self.resident
            .incoming
            .as_ref()
            .map(|s| surface.detach_section(s, 64))
            .transpose()
    }

    pub(super) fn source_rest(
        &self,
        surface: &ResidentSurface<'chart>,
    ) -> Result<ResidentSectionRest, Error> {
        surface
            .detach_section(&self.resident.section, 64)
            .map_err(Error::from)
    }

    pub(super) fn junction_rest(
        &self,
        surface: &ResidentSurface<'chart>,
    ) -> Result<Option<ResidentSectionRest>, Error> {
        self.resident
            .junction
            .as_ref()
            .map(|s| surface.detach_section(s, 64))
            .transpose()
    }

    pub(super) fn transport_rest(
        &self,
        surface: &ResidentSurface<'chart>,
    ) -> Result<Option<ResidentSectionRest>, Error> {
        self.resident
            .transport
            .as_ref()
            .map(|s| surface.detach_section(s, 64))
            .transpose()
    }

    pub(super) fn rest(&self, surface: &ResidentSurface<'chart>) -> Result<HeldRest, Error> {
        self.resident.rest(surface)
    }

    pub(super) fn with_resident<R>(
        &self,
        _surface: &'chart ResidentSurface<'chart>,
        read: impl FnOnce(&ResidentFieldHistory<'chart>) -> Result<R, Error>,
    ) -> Result<R, Error> {
        read(&self.resident)
    }
}
