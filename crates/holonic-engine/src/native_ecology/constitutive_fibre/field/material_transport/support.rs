//! Native restriction of an immutable material report to its actual coordinate support.
//! The decoder retains every original word, including phase, common radii and source lineage.
use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{blob, expect, read_blob};
use std::io::{Read, Write};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeMaterialReportPackingRest {
    pub lineage: NativeFieldLineage,
    pub target_chart: NativeMaterialTarget,
    pub nodes: usize,
    pub targets: usize,
    pub coordinates: Vec<usize>,
    pub packed: ResidentSectionRest,
}
pub struct NativeMaterialReportPacking<'c> {
    surface: &'c ResidentSurface<'c>,
    lineage: NativeFieldLineage,
    target_chart: NativeMaterialTarget,
    nodes: usize,
    targets: usize,
    coordinates: Vec<usize>,
    support: ResidentSection<'c>,
    packed: ResidentSection<'c>,
}
impl NativeMaterialReportPackingRest {
    pub fn write(&self, out: &mut impl Write) -> Result<(), ConstitutiveFibreError> {
        self.validate()?;
        out.write_all(b"HNA-MATERIAL-SUPPORT\x01")
            .map_err(|e| ConstitutiveFibreError::Rest(e.to_string()))?;
        let metadata = serde_json::to_vec(&(
            &self.lineage,
            self.target_chart,
            self.nodes,
            self.targets,
            &self.coordinates,
        ))
        .map_err(|e| ConstitutiveFibreError::Rest(e.to_string()))?;
        blob(out, &metadata)?;
        blob(out, &super::super::rest::point_bytes(&self.packed)?)?;
        Ok(())
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, ConstitutiveFibreError> {
        let mut input = input.take(octets);
        expect(&mut input, b"HNA-MATERIAL-SUPPORT\x01")?;
        let (lineage, target_chart, nodes, targets, coordinates) =
            serde_json::from_slice(&read_blob(&mut input)?)
                .map_err(|e| ConstitutiveFibreError::Rest(e.to_string()))?;
        let packed = super::super::rest::read_point(&read_blob(&mut input)?)?;
        if input.limit() != 0 {
            return Err(ConstitutiveFibreError::Rest(
                "trailing material support data".into(),
            ));
        }
        let value = Self {
            lineage,
            target_chart,
            nodes,
            targets,
            coordinates,
            packed,
        };
        value.validate()?;
        Ok(value)
    }

    fn validate(&self) -> Result<(), ConstitutiveFibreError> {
        let words = self
            .nodes
            .checked_mul(68)
            .and_then(|v| v.checked_add(96))
            .and_then(|v| {
                self.coordinates
                    .len()
                    .checked_mul(82)
                    .and_then(|c| v.checked_add(c))
            })
            .ok_or(ConstitutiveFibreError::Shape)?;
        if self.target_chart.dimension(self.nodes) != Some(self.targets)
            || self.coordinates.iter().any(|i| *i >= self.targets)
            || self.coordinates.windows(2).any(|p| p[0] >= p[1])
            || self.packed.rows != 1
            || self.packed.width != words
            || self.packed.intervals.len() != words
            || self.packed.bound_octaves != 64
            || self.packed.grain.0 != 0
            || self.packed.intervals.iter().any(|(a, b)| a != b)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        Ok(())
    }
}
impl<'c> NativeMaterialReportPacking<'c> {
    fn enact(&self, operation: u32) -> Result<ResidentSection<'c>, ConstitutiveFibreError> {
        let width = if operation == 3 {
            4 * self.targets + 2
        } else {
            82 * self.targets + 68 * self.nodes + 96
        };
        let output = self.surface.fresh_section(1, width, ResidentGrain(0))?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface.record_material_support(
                &lane,
                operation,
                &self.packed,
                &self.support,
                self.nodes,
                self.targets,
                self.coordinates.len(),
                &output,
            )?;
        }
        passage.close(0, &output, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "material support unfolding: {:?}",
                receipt.obstruction
            )));
        }
        Ok(output)
    }
    pub fn coordinates(&self) -> &[usize] {
        &self.coordinates
    }
    pub fn dense_report_words(&self) -> usize {
        82 * self.targets + 68 * self.nodes + 96
    }
    pub fn packed_report_words(&self) -> usize {
        self.packed.width()
    }
    pub fn resident_octets(&self) -> u64 {
        self.support.resident_octets() + self.packed.resident_octets()
    }
    /// Cold decoding of the finite report chart, not selection of a source from its causal fibre.
    pub fn unfold(&self) -> Result<ResidentSectionRest, ConstitutiveFibreError> {
        Ok(self.surface.detach_section(&self.enact(2)?, 64)?)
    }
    /// Reuse the packet receiver with only the required first-current face unfolded on device.
    /// The other ten current balls, factors and raw evaluation reports stay packed.
    pub fn read_packet(&self) -> Result<NativeMaterialPacketReading, ConstitutiveFibreError> {
        self.read_packet_quadrature(NativePacketQuadrature::Real)
    }
    pub fn read_packet_quadrature(&self,quadrature:NativePacketQuadrature)->Result<NativeMaterialPacketReading,ConstitutiveFibreError>{
        let current = self.enact(3)?;
        NativeMaterialPacketReading::read_in_quadrature(
            self.surface,
            &current,
            self.lineage.occurrence,
            self.target_chart,
            self.targets,quadrature,
        )
    }

    pub fn rest(&self) -> Result<NativeMaterialReportPackingRest, ConstitutiveFibreError> {
        let value = NativeMaterialReportPackingRest {
            lineage: self.lineage.clone(),
            target_chart: self.target_chart,
            nodes: self.nodes,
            targets: self.targets,
            coordinates: self.coordinates.clone(),
            packed: self.surface.detach_section(&self.packed, 64)?,
        };
        value.validate()?;
        Ok(value)
    }
    pub fn remount(
        surface: &'c ResidentSurface<'c>,
        rest: NativeMaterialReportPackingRest,
    ) -> Result<Self, ConstitutiveFibreError> {
        rest.validate()?;
        let mut indices = vec![(-1, -1); rest.targets + 1];
        indices[0] = (rest.coordinates.len() as i64, rest.coordinates.len() as i64);
        for (i, at) in rest.coordinates.iter().enumerate() {
            indices[i + 1] = (*at as i64, *at as i64);
        }
        let support = surface.mount_section_rest(
            &ResidentSectionRest::found(1, indices.len(), ResidentGrain(0), 64, indices)
                .map_err(|_| ConstitutiveFibreError::Shape)?,
        )?;
        Ok(Self {
            surface,
            lineage: rest.lineage,
            target_chart: rest.target_chart,
            nodes: rest.nodes,
            targets: rest.targets,
            coordinates: rest.coordinates,
            support,
            packed: surface.mount_section_rest(&rest.packed)?,
        })
    }
}
impl<'c> NativeConstitutiveField<'c> {
    /// Restrict an actual immutable report on device. Only the coordinate inventory crosses
    /// the process boundary for allocation; no amplitude/current determines a host branch.
    pub fn pack_material_report(
        &self,
        at: usize,
    ) -> Result<NativeMaterialReportPacking<'c>, ConstitutiveFibreError> {
        if !self.material_transport_source().is_some_and(NativeMaterialTransportSource::is_operative)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let nodes = self.nodes();
        let targets = self
            .material_target_dimension()
            .ok_or(ConstitutiveFibreError::Shape)?;
        let event = self
            .history
            .get(at)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        let surface = self.relation.surface;
        let report = event.with_resident(surface, |r| {
            r.transport.clone().ok_or(ConstitutiveFibreError::Uncertain)
        })?;
        let support = surface.fresh_section(1, targets + 1, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_material_support(
                &lane, 0, &report, &support, nodes, targets, 0, &support,
            )?;
        }
        passage.close(0, &support, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "material support discovery: {:?}",
                receipt.obstruction
            )));
        }
        let indices = surface.read_out(&support)?;
        if indices.iter().any(|(a, b)| a != b) || indices[0].0 < 0 || indices[0].0 > targets as i64
        {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let count = indices[0].0 as usize;
        let coordinates = indices[1..1 + count]
            .iter()
            .map(|p| usize::try_from(p.0).map_err(|_| ConstitutiveFibreError::Shape))
            .collect::<Result<Vec<_>, _>>()?;
        if coordinates.iter().any(|i| *i >= targets)
            || coordinates.windows(2).any(|p| p[0] >= p[1])
            || indices[1 + count..].iter().any(|p| p.0 != -1)
        {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let packed = surface.fresh_section(1, 68 * nodes + 96 + 82 * count, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_material_support(
                &lane, 1, &report, &support, nodes, targets, count, &packed,
            )?;
        }
        passage.close(0, &packed, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "material support packing: {:?}",
                receipt.obstruction
            )));
        }
        Ok(NativeMaterialReportPacking {
            surface,
            lineage: event.lineage.clone(),
            target_chart: self.material_target().unwrap(),
            nodes,
            targets,
            coordinates,
            support,
            packed,
        })
    }
}
#[cfg(test)]
mod tests;

// Cold serialization of the same finite report chart. These routines move durable
// words; they are never called by native learning, topology or coefficient formation.
fn coordinate_word(n: usize, t: usize, axis: usize, w: usize) -> usize {
    let [beta, _, _, _, raw, _, _] = super::contextual::offsets_for(n, t);
    if w < 44 {
        (w / 4) * (4 * t + 2) + 4 * axis + w % 4
    } else if w < 52 {
        let w = w - 44;
        beta + (w / 4) * 4 * t + 4 * axis + w % 4
    } else {
        let w = w - 52;
        raw + (w / 10) * 10 * t + 10 * axis + w % 10
    }
}
fn common_word(n: usize, t: usize, w: usize) -> usize {
    let [_, output, _, _, _, meta, _] = super::contextual::offsets_for(n, t);
    if w < 22 {
        (w / 2) * (4 * t + 2) + 4 * t + w % 2
    } else if w < 68 * n + 68 {
        output + w - 22
    } else {
        meta + w - (68 * n + 68)
    }
}
impl NativeMaterialReportPackingRest {
    pub(in super::super) fn from_report(
        lineage: NativeFieldLineage,
        target_chart: NativeMaterialTarget,
        nodes: usize,
        report: &ResidentSectionRest,
    ) -> Result<Self, ConstitutiveFibreError> {
        let targets = target_chart
            .dimension(nodes)
            .ok_or(ConstitutiveFibreError::Shape)?;
        if report.rows != 1
            || report.width != 82 * targets + 68 * nodes + 96
            || report.grain.0 != 0
            || report.intervals.iter().any(|(a, b)| a != b)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let coordinates = (0..targets)
            .filter(|axis| {
                (0..82).any(|w| report.intervals[coordinate_word(nodes, targets, *axis, w)].0 != 0)
            })
            .collect::<Vec<_>>();
        let common = 68 * nodes + 96;
        let mut words = Vec::with_capacity(common + 82 * coordinates.len());
        words.extend((0..common).map(|w| report.intervals[common_word(nodes, targets, w)]));
        for axis in &coordinates {
            words.extend(
                (0..82).map(|w| report.intervals[coordinate_word(nodes, targets, *axis, w)]),
            );
        }
        let packed = ResidentSectionRest::found(1, words.len(), ResidentGrain(0), 64, words)
            .map_err(|_| ConstitutiveFibreError::Shape)?;
        let value = Self {
            lineage,
            target_chart,
            nodes,
            targets,
            coordinates,
            packed,
        };
        value.validate()?;
        Ok(value)
    }
    pub(in super::super) fn unfold_rest(
        &self,
    ) -> Result<ResidentSectionRest, ConstitutiveFibreError> {
        self.validate()?;
        let width = self
            .targets
            .checked_mul(82)
            .and_then(|v| self.nodes.checked_mul(68).and_then(|n| v.checked_add(n)))
            .and_then(|v| v.checked_add(96))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let mut words = Vec::new();
        words
            .try_reserve_exact(width)
            .map_err(|e| ConstitutiveFibreError::Rest(e.to_string()))?;
        words.resize(width, (0, 0));
        let common = 68 * self.nodes + 96;
        for w in 0..common {
            words[common_word(self.nodes, self.targets, w)] = self.packed.intervals[w];
        }
        for (row, axis) in self.coordinates.iter().enumerate() {
            for w in 0..82 {
                words[coordinate_word(self.nodes, self.targets, *axis, w)] =
                    self.packed.intervals[common + 82 * row + w];
            }
        }
        ResidentSectionRest::found(1, width, ResidentGrain(0), 64, words)
            .map_err(|_| ConstitutiveFibreError::Shape)
    }
}
