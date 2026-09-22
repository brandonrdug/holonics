//! Persist the executable word at its producing cut, never at contemporary material.
use super::*;
use holonic_engine::native_ecology::constitutive_fibre::NormalMaterialRest;

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
struct Header {
    spec: IncidentModelSpec,
    epoch: u64,
    generations: u64,
    observations: u64,
    next_comparison: u64,
    pending: Vec<PendingHeader>,
}
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
struct PendingHeader {
    id: u64,
    epoch: u64,
    held: Vec<bool>,
    admitted: Vec<Vec<bool>>,
}
#[derive(Debug, PartialEq, Eq)]
struct PendingRest {
    source: NativeFieldCurrentSourceRest,
    anchor: ResidentSectionRest,
    output: ResidentSectionRest,
    material: Vec<NormalMaterialRest>,
}
#[derive(Debug, PartialEq, Eq)]
pub struct NativeIncidentModelRest {
    header: Header,
    field: NativeFieldRest,
    material: Vec<NormalMaterialRest>,
    pending: Vec<PendingRest>,
}
fn blob(out: &mut impl Write, data: &[u8]) -> Result<(), NativeSessionError> {
    out.write_all(&(data.len() as u64).to_le_bytes())?;
    out.write_all(data)?;
    Ok(())
}
fn read_blob<R: Read>(input: &mut std::io::Take<R>) -> Result<Vec<u8>, NativeSessionError> {
    let mut word = [0; 8];
    input.read_exact(&mut word)?;
    let count = u64::from_le_bytes(word);
    if count > input.limit() {
        return Err(invalid("truncated incident rest"));
    }
    let count = usize::try_from(count).map_err(invalid)?;
    let mut data = Vec::new();
    data.try_reserve_exact(count).map_err(invalid)?;
    data.resize(count, 0);
    input.read_exact(&mut data)?;
    Ok(data)
}
impl NativeIncidentModelRest {
    pub(crate) fn roots(&self) -> usize {
        self.field.nodes()
    }
    pub(crate) fn members(&self) -> usize {
        self.material.len()
    }
    pub(crate) fn epoch(&self) -> u64 {
        self.header.epoch
    }
    pub(crate) fn has_prediction(&self, id: u64) -> bool {
        self.header.pending.iter().any(|p| p.id == id)
    }
    pub(crate) fn write(&self, out: &mut impl Write) -> Result<(), NativeSessionError> {
        out.write_all(b"HNA-INCIDENT-FIELD\x01")?;
        blob(out, &serde_json::to_vec(&self.header).map_err(invalid)?)?;
        let mut data = Vec::new();
        self.field.write(&mut data)?;
        blob(out, &data)?;
        for material in &self.material {
            let mut data = Vec::new();
            material.write(&mut data)?;
            blob(out, &data)?;
        }
        for pending in &self.pending {
            let mut data = Vec::new();
            pending.source.write(&mut data)?;
            blob(out, &data)?;
            blob(out, &pending.anchor.canonical_bytes().map_err(invalid)?)?;
            blob(out, &pending.output.canonical_bytes().map_err(invalid)?)?;
            for material in &pending.material {
                let mut data = Vec::new();
                material.write(&mut data)?;
                blob(out, &data)?;
            }
        }
        Ok(())
    }
    pub(crate) fn read(input: &mut impl Read, octets: u64) -> Result<Self, NativeSessionError> {
        let mut input = input.take(octets);
        let mut magic = [0; 19];
        input.read_exact(&mut magic)?;
        if &magic != b"HNA-INCIDENT-FIELD\x01" {
            return Err(invalid("incident model rest version"));
        }
        let header: Header = serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?;
        let layout = header.spec.compile()?;
        let data = read_blob(&mut input)?;
        let field = NativeFieldRest::read(&mut data.as_slice(), data.len() as u64)?;
        let mut read_material=|input:&mut std::io::Take<&mut _>|->Result<Vec<NormalMaterialRest>,NativeSessionError>{
            (0..layout.material_features.len()).map(|_|{let data=read_blob(input)?;
                Ok(NormalMaterialRest::read(&mut data.as_slice(),data.len() as u64)?)}).collect()
        };
        let material = read_material(&mut input)?;
        let mut pending = Vec::new();
        for _ in &header.pending {
            let data = read_blob(&mut input)?;
            let source =
                NativeFieldCurrentSourceRest::read(&mut data.as_slice(), data.len() as u64)?;
            let anchor = ResidentSectionRest::read(&read_blob(&mut input)?).map_err(invalid)?;
            let output = ResidentSectionRest::read(&read_blob(&mut input)?).map_err(invalid)?;
            pending.push(PendingRest {
                source,
                anchor,
                output,
                material: read_material(&mut input)?,
            });
        }
        if input.limit() != 0 {
            return Err(invalid("trailing incident rest data"));
        }
        Ok(Self {
            header,
            field,
            material,
            pending,
        })
    }
    pub(crate) fn remount<'c>(
        self,
        surface: &'c ResidentSurface<'c>,
    ) -> Result<IncidentFieldModel<'c>, NativeSessionError> {
        let (field, _, _) = NativeConstitutiveField::remount(surface, self.field)?;
        let mut model = IncidentFieldModel::new_model(field, self.header.spec)?;
        model.materials = self
            .material
            .into_iter()
            .map(|m| m.remount(surface))
            .collect::<Result<Vec<_>, _>>()?;
        if model.materials.len() != model.layout.material_features.len() {
            return Err(invalid("restored incident material population"));
        }
        let source = model.field.read_current_source()?;
        let grain = source.enclosure().grain();
        for (material, &features) in model.materials.iter().zip(&model.layout.material_features) {
            if material.source_complex() != features
                || material.targets() != model.layout.width / 2
                || material.grain() != grain
            {
                return Err(invalid("restored incident material chart"));
            }
        }
        model.epoch = self.header.epoch;
        model.generations = self.header.generations;
        model.observations = self.header.observations;
        model.next_comparison = self.header.next_comparison;
        for (h, p) in self.header.pending.into_iter().zip(self.pending) {
            if h.id >= model.next_comparison
                || h.epoch > model.epoch
                || model.pending.contains_key(&h.id)
            {
                return Err(invalid("incident pending chronology"));
            }
            let source = model.field.remount_current_source(p.source)?;
            let grain = source.enclosure().grain();
            let anchor = Rc::new(ResidentNormalEnclosure::remount(surface, p.anchor, grain)?);
            if p.material.len() != model.layout.material_features.len()
                || p.material
                    .iter()
                    .zip(&model.layout.material_features)
                    .any(|(m, &features)| {
                        m.source_chart().complex_sources() != Some(features)
                            || m.targets() != model.layout.width / 2
                            || m.grain() != grain
                    })
            {
                return Err(invalid("pending incident material chart"));
            }
            let material = p
                .material
                .into_iter()
                .map(|m| m.remount(surface).map(|m| m.retained_view()))
                .collect::<Result<Vec<_>, _>>()?;
            if h.held.len() != anchor.view().components() / 2
                || h.held[source.boundary_components() / 2..]
                    .iter()
                    .any(|v| *v)
            {
                return Err(invalid("incident pending anchor mask"));
            }
            let (steps, output) =
                model.evaluate(&source, &material, &anchor, &h.held, &h.admitted)?;
            let recorded = ResidentNormalEnclosure::remount(surface, p.output, grain)?;
            if output.inspect()? != recorded.inspect()? {
                return Err(invalid(
                    "incident producing word does not reconstruct recorded endpoint",
                ));
            }
            model.pending.insert(
                h.id,
                Rc::new(IncidentWord {
                    machine: model.layout.machine.clone(),
                    source,
                    material,
                    anchor,
                    held: h.held,
                    admitted: h.admitted,
                    steps,
                    output,
                    epoch: h.epoch,
                    solver: model.spec.solver(),
                    solve_steps: model.spec.solve_steps(),
                }),
            );
        }
        Ok(model)
    }
}
impl IncidentFieldModel<'_> {
    pub(crate) fn rest(&self) -> Result<NativeIncidentModelRest, NativeSessionError> {
        let header = Header {
            spec: self.spec.clone(),
            epoch: self.epoch,
            generations: self.generations,
            observations: self.observations,
            next_comparison: self.next_comparison,
            pending: self
                .pending
                .iter()
                .map(|(&id, p)| PendingHeader {
                    id,
                    epoch: p.epoch,
                    held: p.held.clone(),
                    admitted: p.admitted.clone(),
                })
                .collect(),
        };
        let pending = self
            .pending
            .values()
            .map(|p| {
                Ok(PendingRest {
                    source: p.source.rest()?,
                    anchor: p.anchor.rest()?,
                    output: p.output.rest()?,
                    material: p
                        .material
                        .iter()
                        .map(|m| m.rest())
                        .collect::<Result<Vec<_>, _>>()?,
                })
            })
            .collect::<Result<Vec<_>, NativeSessionError>>()?;
        Ok(NativeIncidentModelRest {
            header,
            field: self.field.rest(&[], &[])?,
            material: self
                .materials
                .iter()
                .map(|m| m.rest())
                .collect::<Result<Vec<_>, _>>()?,
            pending,
        })
    }
}
