use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{
    blob, point_bytes, read_blob, read_point,
};
use std::io::{Read, Write};
type Error = ConstitutiveFibreError;
fn invalid(s: impl std::fmt::Display) -> Error {
    Error::Rest(format!("producing reaction: {s}"))
}
#[derive(Debug, PartialEq, Eq)]
pub struct FieldReactionEnclosureRest {
    source: ResidentSectionRest,
    condition: ResidentSectionRest,
    output: ResidentSectionRest,
    material: NormalMaterialRest,
}
impl FieldReactionEnclosureRest {
    pub fn write(&self, out: &mut impl Write) -> Result<(), Error> {
        for section in [&self.source, &self.condition, &self.output] {
            blob(out, &point_bytes(section)?)?;
        }
        let mut material = Vec::new();
        self.material.write(&mut material)?;
        blob(out, &material)
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, Error> {
        let mut input = input.take(octets);
        let source = read_point(&read_blob(&mut input)?)?;
        let condition = read_point(&read_blob(&mut input)?)?;
        let output = read_point(&read_blob(&mut input)?)?;
        let bytes = read_blob(&mut input)?;
        let material = NormalMaterialRest::read(&mut bytes.as_slice(), bytes.len() as u64)?;
        if input.limit() != 0 {
            return Err(invalid("trailing bytes"));
        }
        Ok(Self {
            source,
            condition,
            output,
            material,
        })
    }
}
impl FieldReactionEnclosure<'_> {
    pub fn rest(&self) -> Result<FieldReactionEnclosureRest, Error> {
        Ok(FieldReactionEnclosureRest {
            source: self.source.rest()?,
            condition: self
                .material
                .surface
                .detach_section(&self.producing_condition, 64)?,
            output: self.output.rest()?,
            material: self.material.rest()?,
        })
    }
}
impl<'c> ResidentGeneratorNeighborhood<'c> {
    pub fn remount_field_reaction(
        &self,
        member: usize,
        rest: FieldReactionEnclosureRest,
    ) -> Result<FieldReactionEnclosure<'c>, Error> {
        let current = self
            .material(member)?
            .predictive
            .as_ref()
            .ok_or(Error::Shape)?;
        let present = &current.material;
        if rest.material.grain() != present.grain()
            || rest.material.source_chart() != present.source_chart()
            || rest.material.targets() != present.targets()
        {
            return Err(invalid("producing material domain"));
        }
        let surface = present.retained_view().surface;
        let grain = rest.material.grain();
        let source = ResidentNormalEnclosure::remount(surface, rest.source, grain)?;
        let output = ResidentNormalEnclosure::remount(surface, rest.output, grain)?;
        let producing_condition = surface.mount_section_rest(&rest.condition)?;
        let condition = ResidentConstitutiveCurrent::rational(&producing_condition)?;
        let material = rest.material.remount(surface)?.retained_view();
        // Validate the exact source/condition chart on the producing material, without
        // substituting contemporary M or changing any continuing model state.
        let recomputed = material.read_applied_bilinear(source.view(), condition)?;
        if recomputed.inspect()? != output.inspect()? {
            return Err(invalid("retained reaction differs from producing action"));
        }
        Ok(FieldReactionEnclosure {
            source,
            producing_condition,
            output,
            material,
            owner: Rc::clone(&self.owner),
            member,
        })
    }
}
