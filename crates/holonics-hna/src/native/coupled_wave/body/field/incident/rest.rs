//! Persist outstanding comparisons. A legacy word keeps its producing cut (`\x01`); a
//! generator comparison keeps only its producing operands and binding (`\x03`) and is read
//! through the contemporary field and material when observed. The retired `\x02` source tape
//! is refused, not reinterpreted.
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
    /// Retired `\x02` per-occurrence source tape. Decoded only to refuse it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    source_episode: Option<serde_json::Value>,
    /// `\x03` generator comparison: binding, clock origin, passage length and declared relation.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    source_moment: Option<GeneratorSourceMomentMeta>,
    id: u64,
    epoch: u64,
    held: Vec<bool>,
    admitted: Vec<Vec<bool>>,
}
#[derive(Debug, PartialEq, Eq)]
enum PendingRest {
    /// A legacy word at its producing cut.
    Frozen {
        source: NativeFieldCurrentSourceRest,
        anchor: ResidentSectionRest,
        output: ResidentSectionRest,
        material: Vec<NormalMaterialRest>,
    },
    /// A generator comparison: its producing operands and no material or field cut.
    Moment {
        anchor: ResidentSectionRest,
        output: ResidentSectionRest,
        condition: Option<ResidentSectionRest>,
    },
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
        out.write_all(
            if self
                .header
                .pending
                .iter()
                .any(|p| p.source_moment.is_some())
            {
                b"HNA-INCIDENT-FIELD\x03"
            } else {
                b"HNA-INCIDENT-FIELD\x01"
            },
        )?;
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
            match pending {
                PendingRest::Frozen {
                    source,
                    anchor,
                    output,
                    material,
                } => {
                    let mut data = Vec::new();
                    source.write(&mut data)?;
                    blob(out, &data)?;
                    blob(out, &anchor.canonical_bytes().map_err(invalid)?)?;
                    blob(out, &output.canonical_bytes().map_err(invalid)?)?;
                    for material in material {
                        let mut data = Vec::new();
                        material.write(&mut data)?;
                        blob(out, &data)?;
                    }
                }
                PendingRest::Moment {
                    anchor,
                    output,
                    condition,
                } => {
                    blob(out, &anchor.canonical_bytes().map_err(invalid)?)?;
                    blob(out, &output.canonical_bytes().map_err(invalid)?)?;
                    if let Some(condition) = condition {
                        blob(out, &condition.canonical_bytes().map_err(invalid)?)?;
                    }
                }
            }
        }
        Ok(())
    }
    pub(crate) fn read(input: &mut impl Read, octets: u64) -> Result<Self, NativeSessionError> {
        let mut input = input.take(octets);
        let mut magic = [0; 19];
        input.read_exact(&mut magic)?;
        let moments = &magic == b"HNA-INCIDENT-FIELD\x03";
        let tape = &magic == b"HNA-INCIDENT-FIELD\x02";
        if &magic != b"HNA-INCIDENT-FIELD\x01" && !moments && !tape {
            return Err(invalid("incident model rest version"));
        }
        let header: Header = serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?;
        if tape || header.pending.iter().any(|p| p.source_episode.is_some()) {
            return Err(invalid(
                "incident rest \\x02 retains a per-occurrence generator source tape; that format is retired by the moment law and is not reinterpreted",
            ));
        }
        if header.pending.iter().any(|p| p.source_moment.is_some()) != moments {
            return Err(invalid("incident moment rest tag"));
        }
        let layout = header.spec.compile()?;
        let data = read_blob(&mut input)?;
        let field = NativeFieldRest::read(&mut data.as_slice(), data.len() as u64)?;
        let read_material=|input:&mut std::io::Take<&mut _>|->Result<Vec<NormalMaterialRest>,NativeSessionError>{
            (0..layout.material_features.len()).map(|_|{let data=read_blob(input)?;
                Ok(NormalMaterialRest::read(&mut data.as_slice(),data.len() as u64)?)}).collect()
        };
        let material = read_material(&mut input)?;
        let mut pending = Vec::new();
        for pending_header in &header.pending {
            if pending_header.source_moment.is_some() {
                let anchor = ResidentSectionRest::read(&read_blob(&mut input)?).map_err(invalid)?;
                let output = ResidentSectionRest::read(&read_blob(&mut input)?).map_err(invalid)?;
                let condition = if layout.source_condition_ports > 0 {
                    Some(ResidentSectionRest::read(&read_blob(&mut input)?).map_err(invalid)?)
                } else {
                    None
                };
                pending.push(PendingRest::Moment {
                    anchor,
                    output,
                    condition,
                });
                continue;
            }
            let data = read_blob(&mut input)?;
            let source =
                NativeFieldCurrentSourceRest::read(&mut data.as_slice(), data.len() as u64)?;
            let anchor = ResidentSectionRest::read(&read_blob(&mut input)?).map_err(invalid)?;
            let output = ResidentSectionRest::read(&read_blob(&mut input)?).map_err(invalid)?;
            let material = read_material(&mut input)?;
            pending.push(PendingRest::Frozen {
                source,
                anchor,
                output,
                material,
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
            let word = match (h.source_moment, p) {
                (
                    Some(meta),
                    PendingRest::Moment {
                        anchor,
                        output,
                        condition,
                    },
                ) => {
                    // Contemporary field: the comparison is read through it when observed.
                    let source = model.field.read_current_source()?;
                    let grain = source.enclosure().grain();
                    let anchor = Rc::new(ResidentNormalEnclosure::remount(surface, anchor, grain)?);
                    let output = ResidentNormalEnclosure::remount(surface, output, grain)?;
                    let condition = condition
                        .map(|rest| {
                            ResidentNormalEnclosureSection::remount(
                                surface,
                                rest,
                                model.layout.sites.len(),
                                model.layout.width * model.layout.source_condition_ports,
                                grain,
                            )
                        })
                        .transpose()?;
                    model.remount_moment_comparison(
                        meta, source, anchor, output, condition, h.held, h.admitted, h.epoch,
                    )?
                }
                (
                    None,
                    PendingRest::Frozen {
                        source,
                        anchor,
                        output,
                        material,
                    },
                ) => {
                    let source = model.field.remount_current_source(source)?;
                    let grain = source.enclosure().grain();
                    let anchor = Rc::new(ResidentNormalEnclosure::remount(surface, anchor, grain)?);
                    if material.len() != model.layout.material_features.len()
                        || material.iter().zip(&model.layout.material_features).any(
                            |(m, &features)| {
                                m.source_chart().complex_sources() != Some(features)
                                    || m.targets() != model.layout.width / 2
                                    || m.grain() != grain
                            },
                        )
                    {
                        return Err(invalid("pending incident material chart"));
                    }
                    let material = material
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
                    let (steps, recomputed) =
                        model.evaluate(&source, &material, &anchor, &h.held, &h.admitted, None)?;
                    let recorded = ResidentNormalEnclosure::remount(surface, output, grain)?;
                    if recomputed.inspect()? != recorded.inspect()? {
                        return Err(invalid(
                            "incident producing word does not reconstruct recorded endpoint",
                        ));
                    }
                    IncidentWord {
                        source_moment: None,
                        external_condition: None,
                        machine: model.layout.machine.clone(),
                        source,
                        material,
                        anchor,
                        held: h.held,
                        admitted: h.admitted,
                        steps,
                        output: recomputed,
                        epoch: h.epoch,
                        solver: model.spec.solver(),
                        solve_steps: model.spec.solve_steps(),
                        enclosure_propagation: model.spec.enclosure_propagation(),
                    }
                }
                _ => return Err(invalid("incident pending rest kind")),
            };
            model.pending.insert(h.id, Rc::new(word));
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
                    source_episode: None,
                    source_moment: p.source_moment.as_ref().map(|m| m.meta.clone()),
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
                Ok(if p.source_moment.is_some() {
                    PendingRest::Moment {
                        anchor: p.anchor.rest()?,
                        output: p.output.rest()?,
                        condition: p
                            .external_condition
                            .as_ref()
                            .map(|c| c.rest())
                            .transpose()?,
                    }
                } else {
                    PendingRest::Frozen {
                        source: p.source.rest()?,
                        anchor: p.anchor.rest()?,
                        output: p.output.rest()?,
                        material: p
                            .material
                            .iter()
                            .map(|m| m.rest())
                            .collect::<Result<Vec<_>, _>>()?,
                    }
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
