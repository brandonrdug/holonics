use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{
    blob, point_bytes, point_section, read_blob, read_point,
};
use std::io::{Read, Write};
const MAGIC: &[u8] = b"HNA-FIELD-CURRENT-SOURCE-REST\x01";
fn invalid(s: impl std::fmt::Display) -> Error {
    Error::Rest(format!("field current source: {s}"))
}

/// Immutable producing sections for an outstanding comparison, without a second live field.
#[derive(Debug, PartialEq, Eq)]
pub struct NativeFieldCurrentSourceRest {
    cut: usize,
    grain: u32,
    width: usize,
    births: Vec<NativeOperativeContactBirth>,
    packed: ResidentSectionRest,
    report: ResidentSectionRest,
    producing: [ResidentSectionRest; 6],
}
impl NativeFieldCurrentSourceRest {
    fn validate(&self) -> Result<(), Error> {
        let k = self.births.len();
        let d = self.width.checked_sub(2 * k).ok_or(Error::Shape)?;
        if d == 0
            || d % 6 != 0
            || !(1..=120).contains(&self.grain)
            || self
                .births
                .iter()
                .any(|b| b.source >= b.receiving || b.receiving >= self.cut)
        {
            return Err(invalid("source extent/grain/births"));
        }
        point_section(&self.packed, 1, 2 * (self.width + 1))?;
        point_section(&self.report, 1, 12 * (d + 1))?;
        for (v, (rows, width)) in self.producing.iter().zip([
            (k.max(1), 2 * d),
            (k.max(1), 4),
            (1, 4),
            (1, d * d),
            (1, 2 * d),
            (1, 8),
        ]) {
            point_section(v, rows, width)?;
        }
        let q = wides(&self.packed.intervals)?;
        let report = wides(&self.report.intervals)?;
        let b = wides(&self.producing[1].intervals)?;
        if q[self.width] < 0
            || q[..d] != report[d + 1..2 * d + 1]
            || q[d..self.width] != b[..2 * k]
            || (0..5).any(|j| report[j * (d + 1) + d] < 0)
            || report[6 * (d + 1) - 1] <= 0
            || wides(&self.producing[2].intervals)?.iter().any(|v| *v < 0)
            || wides(&self.producing[5].intervals)?.iter().any(|v| *v < 0)
        {
            return Err(invalid("source/report/internal bounds"));
        }
        Ok(())
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), Error> {
        self.validate()?;
        out.write_all(MAGIC).map_err(invalid)?;
        blob(
            out,
            &serde_json::to_vec(&(self.cut, self.grain, self.width, &self.births))
                .map_err(invalid)?,
        )?;
        for s in std::iter::once(&self.packed)
            .chain(std::iter::once(&self.report))
            .chain(&self.producing)
        {
            blob(out, &point_bytes(s)?)?;
        }
        Ok(())
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, Error> {
        let mut input = input.take(octets);
        let mut magic = vec![0; MAGIC.len()];
        input.read_exact(&mut magic).map_err(invalid)?;
        if magic != MAGIC {
            return Err(invalid("source witness version"));
        }
        let (cut, grain, width, births) =
            serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?;
        let mut sections = Vec::new();
        for _ in 0..8 {
            sections.push(read_point(&read_blob(&mut input)?)?);
        }
        if input.limit() != 0 {
            return Err(invalid("trailing source witness bytes"));
        }
        let [packed, report, map, b, bounds, covariance, aggregate, moment_bounds] =
            sections.try_into().map_err(|_| Error::Shape)?;
        let rest = Self {
            cut,
            grain,
            width,
            births,
            packed,
            report,
            producing: [map, b, bounds, covariance, aggregate, moment_bounds],
        };
        rest.validate()?;
        Ok(rest)
    }
}
impl NativeFieldCurrentSource<'_> {
    pub fn rest(&self) -> Result<NativeFieldCurrentSourceRest, Error> {
        let p = &self._producing;
        let section =
            |s: &ResidentSection<'_>| self.surface.detach_section(s, 64).map_err(Error::from);
        let rest = NativeFieldCurrentSourceRest {
            cut: self.cut,
            grain: self.grain,
            width: self.width,
            births: self.births.clone(),
            packed: section(&self.packed)?,
            report: section(&self.report)?,
            producing: [
                section(&p.map)?,
                section(&p.b)?,
                section(&p.bounds)?,
                section(&p.covariance)?,
                section(&p.aggregate)?,
                section(&p.moment_bounds)?,
            ],
        };
        rest.validate()?;
        Ok(rest)
    }
}
impl<'c> NativeConstitutiveField<'c> {
    /// Bind the immutable producing witness to the remounted move owner. Its D and current
    /// may precede the contemporary material; replacing them would corrupt delayed gradients.
    pub fn remount_current_source(
        &mut self,
        rest: NativeFieldCurrentSourceRest,
    ) -> Result<NativeFieldCurrentSource<'c>, Error> {
        rest.validate()?;
        let op = self
            .junction
            .as_ref()
            .and_then(|j| j.operative.as_ref())
            .ok_or(Error::Shape)?;
        if rest.cut != self.history.len()
            || rest.grain != op.grain
            || rest.births != op.births
            || rest.width != 6 * self.nodes() + 2 * op.births.len()
        {
            return Err(invalid("source field/incidence domain"));
        }
        let s = self.relation.surface;
        let mount = |x: &ResidentSectionRest| s.mount_section_rest(x).map_err(Error::from);
        let [map, b, bounds, covariance, aggregate, moment_bounds] = &rest.producing;
        Ok(NativeFieldCurrentSource {
            surface: s,
            owner: Rc::clone(&self.owner),
            cut: rest.cut,
            grain: rest.grain,
            width: rest.width,
            births: rest.births,
            packed: Rc::new(mount(&rest.packed)?),
            report: Rc::new(mount(&rest.report)?),
            material: std::cell::OnceCell::new(),
            reflection: std::cell::OnceCell::new(),
            _producing: Rc::new(OperativeSections {
                map: Rc::new(mount(map)?),
                b: Rc::new(mount(b)?),
                bounds: Rc::new(mount(bounds)?),
                covariance: mount(covariance)?,
                aggregate: mount(aggregate)?,
                moment_bounds: mount(moment_bounds)?,
            }),
        })
    }
}
