//! Persist outstanding comparisons as their producing operands (`\x05`): a prepared boundary,
//! or a passage's moment `m` and phase-weighted condition `c` (per-symbol sums for a symbol
//! passage) with its declaration, fixed in the passage length. Every comparison is read at the
//! contemporary constitution when observed, so no producing cut is written.
//!
//! Older wires still decode, converted to the same operands (plan phase 12a):
//! - `\x01` (and the frozen entries of `\x04`): a legacy word at its producing cut
//!   (field source, anchor, output, material views). The boundary part of its anchor is the
//!   retained operand; the frozen source, output and material are read and dropped.
//! - `\x02`: the retired per-occurrence source tape. Its encoded rows are the retained
//!   operands; the moment and condition are accumulated through the body's source maps at
//!   remount, and every per-occurrence word is dropped.
//! - `\x04`: generator moments, unchanged.
//!
//! The retired `\x03` accumulated-anchor form (its anchor mixes the producing standing
//! `U^N q₀` into `m`, so `m` cannot be recovered) is refused, not reinterpreted.
use super::machine_episode::{ComparisonSource, SymbolSums};
use super::*;
use holonic_engine::native_ecology::constitutive_fibre::NormalMaterialRest;

const OPERANDS: &[u8; 19] = b"HNA-INCIDENT-FIELD\x05";
const LEGACY_WORDS: &[u8; 19] = b"HNA-INCIDENT-FIELD\x01";
const LEGACY_TAPE: &[u8; 19] = b"HNA-INCIDENT-FIELD\x02";
const RETIRED_ANCHORS: &[u8; 19] = b"HNA-INCIDENT-FIELD\x03";
const LEGACY_MOMENTS: &[u8; 19] = b"HNA-INCIDENT-FIELD\x04";

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
    /// Retired `\x02` per-occurrence source tape (`LegacyEpisodeMeta`). Decoded to its operands.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    source_episode: Option<serde_json::Value>,
    /// A generator passage: binding, clock origin, passage length and contact counts.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    source_moment: Option<GeneratorSourceMomentMeta>,
    id: u64,
    epoch: u64,
    held: Vec<bool>,
    admitted: Vec<Vec<bool>>,
}

/// The declaration of a retired `\x02` source tape: the passage and its per-edge relation.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct LegacyEpisodeMeta {
    binding: GeneratorSourceBinding,
    start: u64,
    rows: usize,
    components: usize,
    #[serde(default)]
    contacts: Vec<GeneratorSourceContact>,
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
    /// A legacy frozen word, decoded: only its anchor is kept, whose boundary part is the
    /// retained operand (converted at remount). Its source, output and material were dropped.
    Frozen { anchor: ResidentSectionRest },
    /// A retired source tape, decoded: its encoded rows (converted to the moment at remount).
    Tape { encoded: ResidentSectionRest },
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
    /// A body without outstanding comparisons keeps the original `\x01` bytes; outstanding
    /// comparisons are written as operands under `\x05`. A decoded legacy entry is converted by
    /// remounting the body; it is never written back in its retired form.
    pub(crate) fn write(&self, out: &mut impl Write) -> Result<(), NativeSessionError> {
        if self
            .pending
            .iter()
            .any(|p| matches!(p, PendingRest::Frozen { .. } | PendingRest::Tape { .. }))
        {
            return Err(invalid(
                "a decoded legacy incident comparison converts to its operands at remount; remount the body before writing it",
            ));
        }
        out.write_all(if self.pending.is_empty() {
            LEGACY_WORDS
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
                PendingRest::Frozen { .. } | PendingRest::Tape { .. } => unreachable!(),
            }
        }
        Ok(())
    }
    pub(crate) fn read(input: &mut impl Read, octets: u64) -> Result<Self, NativeSessionError> {
        let mut input = input.take(octets);
        let mut magic = [0; 19];
        input.read_exact(&mut magic)?;
        if &magic == RETIRED_ANCHORS {
            return Err(invalid(
                "incident rest \\x03 retains generator comparisons as producing anchors U^N q0 + m; the moment is not separable from that standing, so the format is retired and not reinterpreted (observe or release its comparisons before saving)",
            ));
        }
        let (operands, tape, moments) = match &magic {
            m if m == OPERANDS => (true, false, false),
            m if m == LEGACY_WORDS => (false, false, false),
            m if m == LEGACY_TAPE => (false, true, false),
            m if m == LEGACY_MOMENTS => (false, false, true),
            _ => return Err(invalid("incident model rest version")),
        };
        let header: Header = serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?;
        let any_moment = header.pending.iter().any(|p| p.source_moment.is_some());
        let any_episode = header.pending.iter().any(|p| p.source_episode.is_some());
        if (any_episode && !tape)
            || (tape && any_moment)
            || (!operands && any_moment != moments)
        {
            return Err(invalid("incident rest tag and pending kinds"));
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
            if operands {
                pending.push(PendingRest::Boundary(
                    ResidentSectionRest::read(&read_blob(&mut input)?).map_err(invalid)?,
                ));
                continue;
            }
            // A legacy frozen word (and, in `\x02`, its source tape): the producing cut is read,
            // checked for its declared layout, and dropped.
            let data = read_blob(&mut input)?;
            NativeFieldCurrentSourceRest::read(&mut data.as_slice(), data.len() as u64)?;
            let anchor = ResidentSectionRest::read(&read_blob(&mut input)?).map_err(invalid)?;
            ResidentSectionRest::read(&read_blob(&mut input)?).map_err(invalid)?;
            read_material(&mut input)?;
            if pending_header.source_episode.is_some() {
                let encoded = ResidentSectionRest::read(&read_blob(&mut input)?).map_err(invalid)?;
                pending.push(PendingRest::Tape { encoded });
            } else {
                pending.push(PendingRest::Frozen { anchor });
            }
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
        let boundary = source.boundary_components();
        let joint = boundary + source.internal_components();
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
                (None, PendingRest::Frozen { anchor }) => {
                    // The anchor is `P(boundary ⊕ b_pre)`; its boundary part is the operand.
                    let anchor = ResidentNormalEnclosure::remount(surface, anchor, grain)?;
                    if anchor.view().components() != joint {
                        return Err(invalid("incident pending anchor chart"));
                    }
                    let prepared = anchor.view().restrict(0..boundary)?;
                    model.remount_comparison(
                        None,
                        ComparisonSource::Boundary(Rc::new(prepared)),
                        h.held,
                        h.admitted,
                        h.epoch,
                    )?
                }
                (None, PendingRest::Tape { encoded }) => {
                    let meta: LegacyEpisodeMeta = serde_json::from_value(
                        h.source_episode
                            .ok_or_else(|| invalid("incident source tape declaration"))?,
                    )
                    .map_err(invalid)?;
                    if h.held.iter().any(|v| *v) {
                        return Err(invalid("incident source tape receiver mask"));
                    }
                    let encoded = ResidentNormalEnclosureSection::remount(
                        surface,
                        encoded,
                        meta.rows,
                        meta.components,
                        grain,
                    )?;
                    model.comparison_from_tape(
                        meta.binding,
                        meta.start,
                        &encoded,
                        &meta.contacts,
                        joint,
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
                source_episode: None,
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
impl NativeIncidentModelRest {
    /// Test fixture writer of the retired `\x01` layout: every boundary comparison is written as
    /// the frozen word a pre-12a build wrote (field source, anchor, output, material views),
    /// read from the model's contemporary cut. Only the layout matters for the decoder.
    pub(crate) fn write_legacy_frozen(
        model: &mut IncidentFieldModel<'_>,
        out: &mut impl Write,
    ) -> Result<(), NativeSessionError> {
        let rest = model.rest()?;
        if rest.header.pending.iter().any(|p| p.source_moment.is_some()) {
            return Err(invalid("legacy frozen fixture holds boundary comparisons only"));
        }
        out.write_all(LEGACY_WORDS)?;
        blob(out, &serde_json::to_vec(&rest.header).map_err(invalid)?)?;
        let mut data = Vec::new();
        rest.field.write(&mut data)?;
        blob(out, &data)?;
        for material in &rest.material {
            let mut data = Vec::new();
            material.write(&mut data)?;
            blob(out, &data)?;
        }
        let ids = model.comparisons.keys().copied().collect::<Vec<_>>();
        for id in ids {
            let word = model.contemporary_comparison_word(id, None)?;
            let mut data = Vec::new();
            word.source.rest()?.write(&mut data)?;
            blob(out, &data)?;
            blob(out, &word.anchor.rest()?.canonical_bytes().map_err(invalid)?)?;
            blob(out, &word.output.rest()?.canonical_bytes().map_err(invalid)?)?;
            for material in &word.material {
                let mut data = Vec::new();
                material.rest()?.write(&mut data)?;
                blob(out, &data)?;
            }
        }
        Ok(())
    }

    /// Test fixture writer of the retired `\x02` source-tape layout for one encoded-row passage:
    /// the episode declaration with its per-edge relation, the frozen word parts and the encoded
    /// rows, as a pre-moment build wrote them.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn write_legacy_tape(
        model: &mut IncidentFieldModel<'_>,
        id: u64,
        binding: &GeneratorSourceBinding,
        start: u64,
        encoded: &ResidentNormalEnclosureSection<'_>,
        contacts: &[GeneratorSourceContact],
        out: &mut impl Write,
    ) -> Result<(), NativeSessionError> {
        let mut rest = model.rest()?;
        if rest.header.pending.len() != 1 || rest.header.pending[0].id != id {
            return Err(invalid("legacy tape fixture holds one passage comparison"));
        }
        let word = model.contemporary_comparison_word(id, None)?;
        let pending = &mut rest.header.pending[0];
        pending.source_moment = None;
        pending.source_episode = Some(serde_json::json!({
            "binding": binding, "start": start, "rows": encoded.rows(),
            "components": encoded.components(), "contacts": contacts,
        }));
        out.write_all(LEGACY_TAPE)?;
        blob(out, &serde_json::to_vec(&rest.header).map_err(invalid)?)?;
        let mut data = Vec::new();
        rest.field.write(&mut data)?;
        blob(out, &data)?;
        for material in &rest.material {
            let mut data = Vec::new();
            material.write(&mut data)?;
            blob(out, &data)?;
        }
        let mut data = Vec::new();
        word.source.rest()?.write(&mut data)?;
        blob(out, &data)?;
        blob(out, &word.anchor.rest()?.canonical_bytes().map_err(invalid)?)?;
        blob(out, &word.output.rest()?.canonical_bytes().map_err(invalid)?)?;
        for material in &word.material {
            let mut data = Vec::new();
            material.rest()?.write(&mut data)?;
            blob(out, &data)?;
        }
        blob(out, &encoded.rest()?.canonical_bytes().map_err(invalid)?)?;
        Ok(())
    }
}
