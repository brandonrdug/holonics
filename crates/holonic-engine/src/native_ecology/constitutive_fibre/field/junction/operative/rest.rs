use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::point_section;
use serde::{Deserialize, Serialize};

#[derive(Clone,Debug,PartialEq,Eq,Serialize,Deserialize)]
#[serde(deny_unknown_fields)]
pub(in super::super::super) struct OperativeSourceOverlapFrame {
    pub source:usize,
    pub count:usize,
}
#[derive(Clone,Debug,PartialEq,Eq,Serialize,Deserialize)]
#[serde(deny_unknown_fields)]
pub(in super::super::super) struct OperativeMapProgramFrame {
    pub at_cut:usize,
    pub return_count:usize,
    pub contact_count:usize,
}
#[derive(Debug,PartialEq,Eq)]
pub(in super::super::super) struct OperativeMapProgramRest {
    pub map:ResidentSectionRest,
    pub births:Vec<ResidentSectionRest>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(in super::super::super) struct OperativeReturnFrame {
    pub at_cut: usize,
    pub contact_count: usize,
    /// Omitted legacy frames store both factors over the complete contact population.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub factor_count: Option<usize>,
    /// First factor is the source passage's interior difference; payload stores only ell.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub current_difference_source: Option<usize>,
    #[serde(default,skip_serializing_if="Option::is_none")]
    pub source_overlap:Option<OperativeSourceOverlapFrame>,
    /// Explicit zero generator; its wire payload is the canonical one-word zero marker.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub zero_internal_delta: bool,
    #[serde(default)]
    pub realization: NativeContactRealization,
}
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(in super::super::super) struct OperativeWire {
    pub activated_at: usize,
    pub births: Vec<NativeOperativeContactBirth>,
    pub returns: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub return_frames: Vec<OperativeReturnFrame>,
    #[serde(default,skip_serializing_if="Option::is_none")]
    pub map_program:Option<OperativeMapProgramFrame>,
}
#[derive(Debug, PartialEq, Eq)]
pub(in super::super::super) struct OperativeRest {
    pub current: [ResidentSectionRest; 6],
    pub initial: [ResidentSectionRest; 6],
    pub returns: Vec<[ResidentSectionRest; 4]>,
    pub source_overlaps:Vec<Option<[ResidentSectionRest;2]>>,
    pub program:Option<OperativeMapProgramRest>,
}
#[derive(Debug, PartialEq, Eq)]
pub(in super::super::super) struct OperativeHistoryRest {
    pub count: usize,
    pub b: ResidentSectionRest,
    pub bounds: ResidentSectionRest,
    pub trace: ResidentSectionRest,
}
impl OperativeWire {
    fn frame(&self, i: usize) -> OperativeReturnFrame {
        self.return_frames
            .get(i)
            .cloned()
            .unwrap_or_else(|| OperativeReturnFrame {
                at_cut: self.activated_at,
                factor_count: None,
                current_difference_source: None,
                source_overlap:None,
                zero_internal_delta: false,
                realization: NativeContactRealization::EnclosedFlow,
                contact_count: self
                    .births
                    .iter()
                    .filter(|b| b.receiving < self.activated_at)
                    .count(),
            })
    }
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
                || (w[17].0 == 1 && w[..17].iter().all(|v| v.0 == 0))
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
        let program=wire.map_program.as_ref().map(|p| {
            let count=wire.births.len().checked_sub(p.contact_count).ok_or_else(||invalid("program birth domain"))?;
            Ok::<_,Error>(OperativeMapProgramRest{map:section()?,births:(0..count).map(|_|section()).collect::<Result<_,_>>()?})
        }).transpose()?;
        let mut returns=Vec::new();let mut source_overlaps=Vec::new();
        for i in 0..wire.returns {
            returns.push([section()?,section()?,section()?,section()?]);
            source_overlaps.push(wire.frame(i).source_overlap.is_some().then(||Ok::<_,Error>([section()?,section()?])).transpose()?);
        }
        Ok(Self {
            current,
            initial,
            returns,
            source_overlaps,program,
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
        {
            section(s)?;
        }
        if let Some(program)=&self.program {section(&program.map)?;for birth in &program.births {section(birth)?;}}
        for (r,h) in self.returns.iter().zip(&self.source_overlaps) {
            for s in r {section(s)?;}if let Some(h)=h {for s in h {section(s)?;}}
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
        if self.returns.len() != wire.returns || self.source_overlaps.len()!=wire.returns {
            return Err(invalid("operative return chronology"));
        }
        match (&wire.map_program,&self.program) {
            (Some(p),Some(rest))=>{
                if p.at_cut<wire.activated_at || p.return_count>wire.returns
                    || p.contact_count!=wire.births.partition_point(|b|b.receiving<p.at_cut)
                    || rest.births.len()!=wire.births.len()-p.contact_count {return Err(invalid("map program anchor"));}
                point_section(&rest.map,p.contact_count.max(1),2*d)?;
                for birth in &rest.births {point_section(birth,1,2*d)?;}
                for i in 0..wire.returns {
                    let frame=wire.frame(i);
                    if (i<p.return_count && (frame.at_cut>p.at_cut || frame.source_overlap.is_some()))
                        || (i>=p.return_count && frame.at_cut<p.at_cut) {return Err(invalid("map program return cut"));}
                }
            },
            (None,None)=>{},_=>return Err(invalid("map program presence")),
        }
        if !wire.return_frames.is_empty() && wire.return_frames.len() != wire.returns {
            return Err(invalid("operative return frames"));
        }
        let mut cut = wire.activated_at;
        for (i, r) in self.returns.iter().enumerate() {
            let frame = wire.frame(i);
            if frame.at_cut < cut
                || frame.contact_count
                    != wire
                        .births
                        .iter()
                        .filter(|b| b.receiving < frame.at_cut)
                        .count()
            {
                return Err(invalid("operative return population or order"));
            }
            cut = frame.at_cut;
            let initial = frame.contact_count;
            let factors = frame.factor_count.unwrap_or(initial);
            if factors > initial { return Err(invalid("return factor domain")); }
            for (s, rows, w) in [
                (&r[0], 2, 2 * d),
                (&r[1], if frame.current_difference_source.is_some(){1}else{2}, 4 * factors.max(1)),
                (&r[3], 1, 4),
            ] {
                point_section(s, rows, w)?;
            }
            if frame.zero_internal_delta {
                point_section(&r[2], 1, 1)?;
                if r[2].intervals != [(0,0)] { return Err(invalid("nonzero implicit internal delta")); }
            } else {
                point_section(&r[2], initial.max(1), 4)?;
            }
            if wides(&r[3].intervals)?.iter().any(|v| *v < 0) {
                return Err(invalid("returned radius"));
            }
            match (&frame.source_overlap,&self.source_overlaps[i]) {
                (Some(h),Some(values))=>{
                    if wire.map_program.is_none() || h.source<wire.activated_at
                        || h.source.checked_add(1).is_none_or(|s|s>=frame.at_cut)
                        || h.count>factors || h.count>wire.births.partition_point(|b|b.receiving<=h.source) {
                        return Err(invalid("source overlap domain"));
                    }
                    point_section(&values[0],h.count.max(1),4)?;
                    point_section(&values[1],h.count.max(1),2)?;
                    if wides(&values[1].intervals)?.iter().any(|v|*v<0) {return Err(invalid("source overlap radius"));}
                },
                (None,None)=>{},_=>return Err(invalid("source overlap presence")),
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
            map_program:self.program.as_ref().map(|p|OperativeMapProgramFrame{at_cut:p.at_cut,return_count:p.return_count,contact_count:p.contact_count}),
            return_frames: self
                .returns
                .iter()
                .map(|r| OperativeReturnFrame {
                    at_cut: r.at_cut,
                    contact_count: r.contact_count,
                    factor_count: (r.factor_count != r.contact_count).then_some(r.factor_count),
                    current_difference_source: r.current_difference_source,
                    source_overlap:r.source_overlap.as_ref().map(|h|OperativeSourceOverlapFrame{source:h.source,count:h.count}),
                    zero_internal_delta: r.b.is_none(),
                    realization: r.realization,
                })
                .collect(),
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
            program:self.program.as_ref().map(|p|Ok::<_,Error>(OperativeMapProgramRest {
                map:read(&p.map)?,births:p.births.iter().map(|b|read(b)).collect::<Result<_,_>>()?,
            })).transpose()?,
            source_overlaps:self.returns.iter().map(|r|r.source_overlap.as_ref().map(|h|
                Ok::<_,Error>([read(&h.coefficients)?,read(&h.errors)?])).transpose()).collect::<Result<_,_>>()?,
            current: sections(&self.sections)?,
            initial: sections(&self.initial)?,
            returns: self
                .returns
                .iter()
                .map(|r| {
                    Ok([
                        read(&r.ports)?,
                        read(&r.currents)?,
                        match &r.b {
                            Some(b) => read(b)?,
                            None => ResidentSectionRest::found(1,1,ResidentGrain(0),64,vec![(0,0)]).map_err(invalid)?,
                        },
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
        let program=match (wire.map_program.as_ref(),rest.program) {
            (Some(p),Some(rest))=>Some(OperativeMapProgram{at_cut:p.at_cut,return_count:p.return_count,
                contact_count:p.contact_count,map:Rc::new(mount(rest.map)?),
                births:rest.births.into_iter().map(|b|mount(b).map(Rc::new)).collect::<Result<_,_>>()?}),
            (None,None)=>None,_=>return Err(invalid("map program presence")),
        };
        let returns = rest
            .returns
            .into_iter()
            .zip(rest.source_overlaps)
            .enumerate()
            .map(|(i, (r,h))| {
                let frame = wire.frame(i);
                let [ports, currents, b, bounds] = r;
                // Cold-wire inspection is a representation check. It changes no current,
                // coefficient, error bound or chronology, and never reads hot semantic state.
                let b = if frame.zero_internal_delta || b.intervals.iter().all(|v| *v == (0,0)) {
                    None
                } else { Some(Rc::new(mount(b)?)) };
                Ok(Rc::new(OperativeReturn {
                    source_overlap:match (frame.source_overlap,h) {
                        (Some(h),Some([coefficients,errors]))=>Some(OperativeSourceOverlap{source:h.source,count:h.count,
                            coefficients:Rc::new(mount(coefficients)?),errors:Rc::new(mount(errors)?)}),
                        (None,None)=>None,_=>return Err(invalid("source overlap presence")),
                    },
                    at_cut: frame.at_cut,
                    contact_count: frame.contact_count,
                    factor_count: frame.factor_count.unwrap_or(frame.contact_count),
                    current_difference_source: frame.current_difference_source,
                    realization: frame.realization,
                    origin: Rc::new(()),
                    ports: Rc::new(mount(ports)?),
                    currents: Rc::new(mount(currents)?),
                    b,
                    bounds: Rc::new(mount(bounds)?),
                }))
            })
            .collect::<Result<Vec<_>, Error>>()?;
        Ok(Self {
            recent_producers:Default::default(),
            sections: sections(rest.current)?,
            initial: sections(rest.initial)?,
            activated_at: wire.activated_at,
            grain,
            births: wire.births,
            origin: Rc::new(()),
            returns,
            program,
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
