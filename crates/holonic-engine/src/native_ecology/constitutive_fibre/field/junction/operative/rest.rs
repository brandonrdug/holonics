use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::point_section;
use serde::{Deserialize, Serialize};

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(in super::super::super) struct OperativeWire {
    pub activated_at: usize,
    pub births: Vec<NativeOperativeContactBirth>,
    pub returns: usize,
}
#[derive(Debug, PartialEq, Eq)]
pub(in super::super::super) struct OperativeRest {
    pub current: [ResidentSectionRest; 6],
    pub initial: [ResidentSectionRest; 6],
    pub returns: Vec<[ResidentSectionRest; 4]>,
}
#[derive(Debug, PartialEq, Eq)]
pub(in super::super::super) struct OperativeHistoryRest {
    pub count: usize,
    pub b: ResidentSectionRest,
    pub bounds: ResidentSectionRest,
    pub trace: ResidentSectionRest,
}
impl OperativeHistoryRest {
    pub fn write(
        &self,
        section: &mut impl FnMut(&ResidentSectionRest) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let count = i64::try_from(self.count).map_err(invalid)?;
        section(
            &ResidentSectionRest::found(1, 1, ResidentGrain(0), 64, vec![(count, count)])
                .map_err(invalid)?,
        )?;
        for s in [&self.b, &self.bounds, &self.trace] {
            section(s)?;
        }
        Ok(())
    }
    pub fn read(
        section: &mut impl FnMut() -> Result<ResidentSectionRest, Error>,
    ) -> Result<Self, Error> {
        let count = section()?;
        point_section(&count, 1, 1)?;
        let count = usize::try_from(count.intervals[0].0).map_err(invalid)?;
        Ok(Self {
            count,
            b: section()?,
            bounds: section()?,
            trace: section()?,
        })
    }
    pub fn validate(&self, d: usize, expected: usize) -> Result<(), Error> {
        if self.count != expected {
            return Err(invalid("historical contact population"));
        }
        point_section(&self.b, expected.max(1), 4)?;
        point_section(&self.bounds, 1, 4)?;
        point_section(&self.trace, 1, 18 * d + 12)?;
        if wides(&self.bounds.intervals)?.iter().any(|v| *v < 0) {
            return Err(invalid("historical map/current radius"));
        }
        for w in self.trace.intervals[..18 * d].chunks_exact(18) {
            if ![0, 1].contains(&w[17].0)
                || (w[17].0==1 && w[..17].iter().all(|v|v.0==0))
                || w[..17].iter().any(|v| v.0 < 0 || v.0 > u32::MAX as i64)
            {
                return Err(invalid("historical residual limb"));
            }
        }
        if wides(&self.trace.intervals[18 * d..])?
            .iter()
            .any(|v| *v < 0)
        {
            return Err(invalid("historical residual bound"));
        }
        Ok(())
    }
}
impl OperativeRest {
    pub fn read(
        wire: &OperativeWire,
        section: &mut impl FnMut() -> Result<ResidentSectionRest, Error>,
    ) -> Result<Self, Error> {
        let mut six = || -> Result<[ResidentSectionRest; 6], Error> {
            Ok([
                section()?,
                section()?,
                section()?,
                section()?,
                section()?,
                section()?,
            ])
        };
        let current = six()?;
        let initial = six()?;
        let returns = (0..wire.returns)
            .map(|_| Ok([section()?, section()?, section()?, section()?]))
            .collect::<Result<Vec<_>, Error>>()?;
        Ok(Self {
            current,
            initial,
            returns,
        })
    }
    pub fn write(
        &self,
        section: &mut impl FnMut(&ResidentSectionRest) -> Result<(), Error>,
    ) -> Result<(), Error> {
        for s in self
            .current
            .iter()
            .chain(&self.initial)
            .chain(self.returns.iter().flatten())
        {
            section(s)?;
        }
        Ok(())
    }
    pub fn validate(&self, wire: &OperativeWire, n: usize) -> Result<(), Error> {
        let d = 6 * n;
        let m = d / 2;
        let k = wire.births.len();
        let initial = wire
            .births
            .iter()
            .filter(|b| b.receiving < wire.activated_at)
            .count();
        let validate = |s: &[ResidentSectionRest; 6], k: usize| -> Result<(), Error> {
            for (s, r, w) in [
                (&s[0], k.max(1), 2 * d),
                (&s[1], k.max(1), 4),
                (&s[2], 1, 4),
                (&s[3], 1, 4 * m * m),
                (&s[4], 1, 2 * d),
                (&s[5], 1, 8),
            ] {
                point_section(s, r, w)?;
            }
            if wides(&s[2].intervals)?
                .iter()
                .chain(wides(&s[5].intervals)?.iter())
                .any(|v| *v < 0)
            {
                return Err(invalid("map/current or moment radius"));
            }
            Ok(())
        };
        validate(&self.current, k)?;
        validate(&self.initial, initial)?;
        if self.returns.len() != wire.returns {
            return Err(invalid("operative return chronology"));
        }
        for r in &self.returns {
            for (s, rows, w) in [
                (&r[0], 2, 2 * d),
                (&r[1], 2, 4 * initial.max(1)),
                (&r[2], initial.max(1), 4),
                (&r[3], 1, 4),
            ] {
                point_section(s, rows, w)?;
            }
            if wides(&r[3].intervals)?.iter().any(|v| *v < 0) {
                return Err(invalid("returned radius"));
            }
        }
        Ok(())
    }
}
impl<'c> OperativeState<'c> {
    pub(in super::super::super) fn wire(&self) -> OperativeWire {
        OperativeWire {
            activated_at: self.activated_at,
            births: self.births.clone(),
            returns: self.returns.len(),
        }
    }
    pub(in super::super::super) fn rest(
        &self,
        surface: &ResidentSurface<'c>,
    ) -> Result<OperativeRest, Error> {
        let read = |s: &ResidentSection<'c>| surface.detach_section(s, 64).map_err(Error::from);
        let sections = |s: &OperativeSections<'c>| -> Result<[ResidentSectionRest; 6], Error> {
            Ok([
                read(&s.map)?,
                read(&s.b)?,
                read(&s.bounds)?,
                read(&s.covariance)?,
                read(&s.aggregate)?,
                read(&s.moment_bounds)?,
            ])
        };
        Ok(OperativeRest {
            current: sections(&self.sections)?,
            initial: sections(&self.initial)?,
            returns: self
                .returns
                .iter()
                .map(|r| {
                    Ok([
                        read(&r.ports)?,
                        read(&r.currents)?,
                        read(&r.b)?,
                        read(&r.bounds)?,
                    ])
                })
                .collect::<Result<_, Error>>()?,
        })
    }
    pub(in super::super::super) fn remount(
        surface: &'c ResidentSurface<'c>,
        wire: OperativeWire,
        rest: OperativeRest,
        grain: u32,
    ) -> Result<Self, Error> {
        let mount = |s: ResidentSectionRest| surface.mount_section_rest(&s).map_err(Error::from);
        let sections = |s: [ResidentSectionRest; 6]| -> Result<Rc<OperativeSections<'c>>, Error> {
            let [map, b, bounds, covariance, aggregate, moment_bounds] = s;
            Ok(Rc::new(OperativeSections {
                map: Rc::new(mount(map)?),
                b: Rc::new(mount(b)?),
                bounds: Rc::new(mount(bounds)?),
                covariance: mount(covariance)?,
                aggregate: mount(aggregate)?,
                moment_bounds: mount(moment_bounds)?,
            }))
        };
        let returns = rest
            .returns
            .into_iter()
            .map(|r| {
                let [ports, currents, b, bounds] = r;
                Ok(Rc::new(OperativeReturn {
                    origin: Rc::new(()),
                    ports: mount(ports)?,
                    currents: mount(currents)?,
                    b: mount(b)?,
                    bounds: mount(bounds)?,
                }))
            })
            .collect::<Result<Vec<_>, Error>>()?;
        Ok(Self {
            sections: sections(rest.current)?,
            initial: sections(rest.initial)?,
            activated_at: wire.activated_at,
            grain,
            births: wire.births,
            origin: Rc::new(()),
            returns,
        })
    }
}
impl<'c> HeldOperative<'c> {
    pub(in super::super::super) fn rest(
        &self,
        surface: &ResidentSurface<'c>,
    ) -> Result<OperativeHistoryRest, Error> {
        Ok(OperativeHistoryRest {
            count: self.count,
            b: surface.detach_section(&self.b, 64)?,
            bounds: surface.detach_section(&self.bounds, 64)?,
            trace: surface.detach_section(&self.trace, 64)?,
        })
    }
    pub(in super::super::super) fn mount(
        surface: &'c ResidentSurface<'c>,
        rest: OperativeHistoryRest,
    ) -> Result<Self, Error> {
        Ok(Self {
            count: rest.count,
            b: Rc::new(surface.mount_section_rest(&rest.b)?),
            bounds: Rc::new(surface.mount_section_rest(&rest.bounds)?),
            trace: Rc::new(surface.mount_section_rest(&rest.trace)?),
        })
    }
}
