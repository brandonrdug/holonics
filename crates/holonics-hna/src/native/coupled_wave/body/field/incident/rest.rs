//! Persist outstanding comparisons as their producing operands (`\x05`): a prepared boundary,
//! or a passage's moment `m` and phase-weighted condition `c` (per-symbol sums for a symbol
//! passage) with its declaration, fixed in the passage length. Every comparison is read at the
//! contemporary constitution when observed, so no producing cut is written.
//!
//! The current writer uses `\x01` only for an empty pending set and `\x05` for pending
//! operands. Previous frozen-word, source-tape and accumulated-anchor layouts are not read.
use super::machine_episode::{ComparisonSource, SymbolSums};
use super::*;
use holonic_engine::native_ecology::constitutive_fibre::NormalMaterialRest;

const OPERANDS: &[u8; 19] = b"HNA-INCIDENT-FIELD\x05";
const EMPTY_PENDING: &[u8; 19] = b"HNA-INCIDENT-FIELD\x01";

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
struct Header {
    spec: IncidentModelSpec,
    epoch: u64,
    generations: u64,
    observations: u64,
    next_comparison: u64,
    pending: Vec<PendingHeader>,
    /// Declared residual of committed-current rebases (absent before the first commit).
    #[serde(default, skip_serializing_if = "IncidentRebaseResidual::is_empty")]
    rebase: IncidentRebaseResidual,
    /// Receipt of power-neutral reaction deposits (absent under the legacy law).
    #[serde(default, skip_serializing_if = "ReactionDepositRecord::is_empty")]
    reaction: ReactionDepositRecord,
}
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
struct PendingHeader {
    /// A generator passage: binding, clock origin, passage length and contact counts.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    source_moment: Option<GeneratorSourceMomentMeta>,
    id: u64,
    epoch: u64,
    held: Vec<bool>,
    admitted: Vec<Vec<bool>>,
}

#[derive(Debug, PartialEq, Eq)]
enum PendingRest {
    /// A prepared boundary, as its caller supplied it.
    Boundary(ResidentSectionRest),
    /// A generator passage: an encoded-row passage stores its moment `m` and condition `c`; a
    /// symbol passage (`alphabet` in the header) stores its per-symbol sums `C` in `moment` and
    /// per-port sums `D` in `condition`.
    Moment {
        moment: ResidentSectionRest,
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
    /// The active empty-pending `\x01` form remains; pending operands are written under `\x05`.
    pub(crate) fn write(&self, out: &mut impl Write) -> Result<(), NativeSessionError> {
        out.write_all(if self.pending.is_empty() {
            EMPTY_PENDING
        } else {
            OPERANDS
        })?;
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
                PendingRest::Boundary(boundary) => {
                    blob(out, &boundary.canonical_bytes().map_err(invalid)?)?;
                }
                PendingRest::Moment { moment, condition } => {
                    blob(out, &moment.canonical_bytes().map_err(invalid)?)?;
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
        let operands = &magic == OPERANDS;
        let empty = &magic == EMPTY_PENDING;
        if !operands && !empty {
            return Err(invalid("incident model rest version"));
        }
        let header: Header = serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?;
        let any_moment = header.pending.iter().any(|p| p.source_moment.is_some());
        if empty && !header.pending.is_empty() {
            return Err(invalid("incident pending comparisons require operand rest \\x05"));
        }
        if operands && header.pending.is_empty() {
            return Err(invalid("empty incident rest requires current empty tag \\x01"));
        }
        if !operands && any_moment {
            return Err(invalid("incident pending moment requires operand rest \\x05"));
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
                let moment = ResidentSectionRest::read(&read_blob(&mut input)?).map_err(invalid)?;
                let condition = if layout.source_condition_ports > 0 {
                    Some(ResidentSectionRest::read(&read_blob(&mut input)?).map_err(invalid)?)
                } else {
                    None
                };
                pending.push(PendingRest::Moment { moment, condition });
                continue;
            }
            pending.push(PendingRest::Boundary(
                ResidentSectionRest::read(&read_blob(&mut input)?).map_err(invalid)?,
            ));
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
        model.rebase = self.header.rebase.clone();
        model.reaction_record = self.header.reaction.clone();
        let ports = model.layout.source_condition_ports;
        for (h, p) in self.header.pending.into_iter().zip(self.pending) {
            if h.id >= model.next_comparison || h.epoch > model.epoch || model.is_pending(h.id) {
                return Err(invalid("incident pending chronology"));
            }
            let comparison = match (h.source_moment, p) {
                (Some(meta), PendingRest::Moment { moment, condition }) => {
                    let source = match meta.alphabet {
                        None => ComparisonSource::Rows {
                            moment: Rc::new(ResidentNormalEnclosure::remount(
                                surface, moment, grain,
                            )?),
                            condition: condition
                                .map(|rest| {
                                    ResidentNormalEnclosureSection::remount(
                                        surface,
                                        rest,
                                        model.layout.sites.len(),
                                        model.layout.width * ports,
                                        grain,
                                    )
                                    .map(Rc::new)
                                })
                                .transpose()?,
                        },
                        Some(_) => {
                            let rows = meta
                                .present_symbols
                                .len()
                                .checked_mul(meta.binding.injection_sites.len())
                                .ok_or_else(|| invalid("symbol sum rest extent"))?;
                            // Width of one mounted affine coefficient row at this grain.
                            let width = ResidentNormalEnclosureSection::affine_coefficients(
                                surface,
                                &[relational_geometry::AffineMap3::identity()],
                                grain,
                            )?
                            .components();
                            ComparisonSource::Symbols(SymbolSums {
                                moment: Rc::new(ResidentNormalEnclosureSection::remount(
                                    surface, moment, rows, width, grain,
                                )?),
                                ports: condition
                                    .map(|rest| {
                                        ResidentNormalEnclosureSection::remount(
                                            surface,
                                            rest,
                                            rows * ports,
                                            width,
                                            grain,
                                        )
                                        .map(Rc::new)
                                    })
                                    .transpose()?,
                            })
                        }
                    };
                    model.remount_comparison(Some(meta), source, h.held, h.admitted, h.epoch)?
                }
                (None, PendingRest::Boundary(rest)) => {
                    let prepared = ResidentNormalEnclosure::remount(surface, rest, grain)?;
                    model.remount_comparison(
                        None,
                        ComparisonSource::Boundary(Rc::new(prepared)),
                        h.held,
                        h.admitted,
                        h.epoch,
                    )?
                }
                _ => return Err(invalid("incident pending rest kind")),
            };
            model.comparisons.insert(h.id, Rc::new(comparison));
        }
        Ok(model)
    }
}
impl IncidentFieldModel<'_> {
    pub(crate) fn rest(&self) -> Result<NativeIncidentModelRest, NativeSessionError> {
        let mut pending_headers = Vec::with_capacity(self.comparisons.len());
        let mut pending = Vec::with_capacity(self.comparisons.len());
        for (&id, comparison) in &self.comparisons {
            pending_headers.push(PendingHeader {
                source_moment: comparison.meta().cloned(),
                id,
                epoch: comparison.epoch(),
                held: comparison.held().to_vec(),
                admitted: comparison.admitted().to_vec(),
            });
            pending.push(match comparison.source() {
                ComparisonSource::Boundary(boundary) => PendingRest::Boundary(boundary.rest()?),
                ComparisonSource::Rows { moment, condition } => PendingRest::Moment {
                    moment: moment.rest()?,
                    condition: condition.as_ref().map(|c| c.rest()).transpose()?,
                },
                ComparisonSource::Symbols(sums) => PendingRest::Moment {
                    moment: sums.moment.rest()?,
                    condition: sums.ports.as_ref().map(|d| d.rest()).transpose()?,
                },
            });
        }
        let header = Header {
            spec: self.spec.clone(),
            epoch: self.epoch,
            generations: self.generations,
            observations: self.observations,
            next_comparison: self.next_comparison,
            pending: pending_headers,
            rebase: self.rebase.clone(),
            reaction: self.reaction_record.clone(),
        };
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

#[cfg(test)]
mod format_tests {
    use super::*;

    #[test]
    fn retired_incident_pending_tags_are_refused() {
        for version in [2u8, 3, 4] {
            let mut bytes = b"HNA-INCIDENT-FIELD".to_vec();
            bytes.push(version);
            assert!(NativeIncidentModelRest::read(&mut bytes.as_slice(), bytes.len() as u64)
                .is_err());
        }
    }
}
