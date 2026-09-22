//! Cold rest for the fixed generator source/phase presentation.
//!
//! The body owns each comparison's source Holon (per-symbol phase-weighted sums and their
//! declaration, fixed in the passage length). This packet owns the current E/R material and,
//! per outstanding comparison, only its clock origin, passage length, receiving binding and
//! alphabet binding (occurrences per codec identity, `|A|` words). No encoded rows, per-cell
//! symbols, per-edge contacts, producing material copies or frozen receiver faces are written:
//! an outstanding comparison is read at the contemporary constitution when it is observed.

use super::super::incident_encoder::IncidentEncoder;
use super::super::incident_receiver::{IncidentTextCohort, phase::GeneratorTextReceiver};
use super::*;
use crate::native::GeneratorPhaseReceiverBinding;
use holonic_engine::native_ecology::constitutive_fibre::NormalMaterialRest;
use holonic_engine::resident_section::ResidentGrain;
use serde::{Deserialize, Serialize};
use std::io::Cursor;

fn material_bytes(material: &NormalMaterialRest) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    material.write(&mut bytes).map_err(invalid)?;
    Ok(bytes)
}

fn read_material(bytes: &[u8]) -> Result<NormalMaterialRest> {
    NormalMaterialRest::read(&mut Cursor::new(bytes), bytes.len() as u64).map_err(invalid)
}

/// One outstanding comparison at rest: fixed in the passage length, not a producing cut.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct GeneratorPendingRest {
    pub id: u64,
    pub receiver_binding: GeneratorPhaseReceiverBinding,
    pub start: u64,
    pub cells: usize,
    /// Occurrences per codec identity `0..|A|` at request time.
    pub symbol_counts: Vec<usize>,
    /// The presentation's fixed-size request record and exterior exposure pairing.
    pub record: super::GeneratorRetainedRecord,
}

/// The pre-moment wire kept encoded rows, a frozen encoder copy and frozen receiver faces (and
/// the per-cell preparation) for every outstanding comparison. Those are producing cuts and
/// `O(N)` relations, not the fixed pending operands; a rest that carries them is refused with its
/// reason rather than silently reinterpreted.
impl<'de> Deserialize<'de> for GeneratorPendingRest {
    fn deserialize<D: serde::Deserializer<'de>>(
        deserializer: D,
    ) -> std::result::Result<Self, D::Error> {
        use serde::de::IgnoredAny;
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct Wire {
            id: u64,
            receiver_binding: GeneratorPhaseReceiverBinding,
            start: u64,
            cells: Option<usize>,
            symbol_counts: Option<Vec<usize>>,
            record: Option<super::GeneratorRetainedRecord>,
            preparation: Option<IgnoredAny>,
            encoded_symbols: Option<IgnoredAny>,
            encoded_rows: Option<IgnoredAny>,
            encoded_row_count: Option<IgnoredAny>,
            encoded_width: Option<IgnoredAny>,
            grain_bits: Option<IgnoredAny>,
            encoded_producing_material: Option<IgnoredAny>,
            frozen_text: Option<IgnoredAny>,
            frozen_support: Option<IgnoredAny>,
            frozen_cohorts: Option<IgnoredAny>,
            frozen_cohort_material: Option<IgnoredAny>,
        }
        let wire = Wire::deserialize(deserializer)?;
        if wire.encoded_rows.is_some()
            || wire.encoded_producing_material.is_some()
            || wire.frozen_text.is_some()
            || wire.frozen_support.is_some()
            || wire.frozen_cohort_material.is_some()
            || wire.encoded_symbols.is_some()
            || wire.encoded_row_count.is_some()
            || wire.encoded_width.is_some()
            || wire.grain_bits.is_some()
            || wire.frozen_cohorts.is_some()
            || wire.preparation.is_some()
        {
            return Err(serde::de::Error::custom(
                "generator pending rest carries encoded source rows or frozen receiver faces \
                 (the pre-moment wire); an outstanding comparison is now read at the \
                 contemporary constitution and keeps no producing cut. Observe or release it \
                 with the build that wrote this checkpoint, then save again",
            ));
        }
        let (Some(cells), Some(symbol_counts), Some(record)) =
            (wire.cells, wire.symbol_counts, wire.record)
        else {
            return Err(serde::de::Error::custom(
                "generator pending rest lacks its passage length, alphabet binding or request record",
            ));
        };
        Ok(Self {
            id: wire.id,
            receiver_binding: wire.receiver_binding,
            start: wire.start,
            cells,
            symbol_counts,
            record,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GeneratorPresentationRest {
    pub encoder_material: Vec<Vec<u8>>,
    pub encoder_identities: Vec<usize>,
    pub receiver_text: Vec<u8>,
    pub receiver_support: Vec<u8>,
    pub receiver_cohorts: Vec<IncidentTextCohort>,
    pub receiver_cohort_material: Vec<Vec<u8>>,
    pub pending: Vec<GeneratorPendingRest>,
    pub next_event: u64,
}

impl<'c> GeneratorPresentation<'c> {
    pub(crate) fn rest(&self) -> Result<GeneratorPresentationRest> {
        let (encoder_material, encoder_identities) = self.encoder.rest_with_identities()?;
        let receiver = self.receiver.inner();
        let pending = self
            .pending
            .iter()
            .map(|(&id, pending)| GeneratorPendingRest {
                id,
                receiver_binding: self.receiver_binding.clone(),
                start: pending.start,
                cells: pending.cells,
                symbol_counts: pending.symbol_counts.clone(),
                record: pending.record.clone(),
            })
            .collect::<Vec<_>>();
        Ok(GeneratorPresentationRest {
            encoder_material: encoder_material
                .iter()
                .map(material_bytes)
                .collect::<Result<_>>()?,
            encoder_identities,
            receiver_text: material_bytes(&receiver.text_rest()?)?,
            receiver_support: material_bytes(&receiver.support_rest()?)?,
            receiver_cohorts: receiver.cohorts().to_vec(),
            receiver_cohort_material: receiver
                .text_cohort_rests()?
                .iter()
                .map(material_bytes)
                .collect::<Result<Vec<_>>>()?,
            pending,
            next_event: self.next_event,
        })
    }
}

impl GeneratorPresentationRest {
    pub(crate) fn remount<'c>(
        self,
        surface: &'c ResidentSurface<'c>,
        spec: &FieldSessionSpec,
        body: &NativeCoupledBody<'c>,
    ) -> Result<GeneratorPresentation<'c>> {
        let options = spec
            .generator
            .as_ref()
            .ok_or_else(|| invalid("generator presentation rest requires generator spec"))?;
        let body_spec = body.generator_field_spec()?;
        if body_spec != &options.field {
            return Err(invalid("generator body/spec rest mismatch"));
        }
        let (rows, width, grain, _) = body.incident_dimensions()?;
        let expected_width = 12usize;
        if rows != options.field.machine.sites().len()
            || width != expected_width
            || grain != ResidentGrain(spec.fractional_bits)
        {
            return Err(invalid("generator presentation rest layout"));
        }
        let source_width = options
            .source
            .injection_sites
            .len()
            .checked_mul(6)
            .ok_or_else(|| invalid("generator source rest width"))?;
        let encoder_material = self
            .encoder_material
            .iter()
            .map(|bytes| read_material(bytes))
            .collect::<Result<Vec<_>>>()?;
        if encoder_material.is_empty()
            || encoder_material
                .iter()
                .any(|material| material.targets() != source_width / 2)
        {
            return Err(invalid("generator encoder source width"));
        }
        let mut encoder = IncidentEncoder::remount_with_identities(
            surface,
            encoder_material,
            self.encoder_identities,
        )?;
        encoder.bind_seed(BoundaryMaterialSeed::new(
            options.material_seed,
            spec.fractional_bits,
        ));
        let current_boundary = super::receiver_boundary(surface, spec, None)?;
        let receiver_cohorts = self.receiver_cohorts;
        let receiver_codec_version = receiver_cohorts
            .last()
            .map_or(0, |cohort| cohort.codec_version);
        let receiver = GeneratorTextReceiver::remount_with_cohorts(
            surface,
            current_boundary,
            read_material(&self.receiver_text)?,
            read_material(&self.receiver_support)?,
            receiver_cohorts,
            self.receiver_cohort_material
                .iter()
                .map(|bytes| read_material(bytes))
                .collect::<Result<Vec<_>>>()?,
            receiver_codec_version,
        )?;
        let mut presentation = GeneratorPresentation {
            encoder,
            receiver,
            pending: std::collections::BTreeMap::new(),
            next_event: self.next_event,
            receiver_binding: options.receiver.clone(),
            readings: Default::default(),
        };
        for pending in self.pending {
            let rows = pending.cells;
            if pending.receiver_binding != options.receiver
                || pending.start > presentation.next_event
                || pending.start.checked_add(rows as u64).is_none()
                || pending.symbol_counts.iter().sum::<usize>() != rows
                || pending.symbol_counts.len() > spec.symbols.len()
                || pending.record.output_symbols
                    != pending.record.request_extent + pending.record.response_aperture
                || pending.record.response_aperture != spec.response_aperture()?
                || pending.record.request_extent > rows
            {
                return Err(invalid("generator pending source/receiver chart"));
            }
            let declared = body.generator_comparison_declaration(pending.id)?;
            if declared.binding != options.source
                || declared.start != pending.start
                || declared.rows != rows
                || declared.components != source_width
                || declared.alphabet != Some(pending.symbol_counts.len())
            {
                return Err(invalid("generator pending body/source binding mismatch"));
            }
            if let Some(pairing) = &pending.record.exposure_pairing {
                if pairing.family.provider.is_empty()
                    || pairing.family.record_group.is_empty()
                    || pairing.response_symbols != pending.record.response_aperture
                    || pairing.request_text_sha256 != pending.record.held_text_sha256
                {
                    return Err(invalid("generator retained exposure digest"));
                }
            }
            presentation.pending.insert(
                pending.id,
                GeneratorPending {
                    start: pending.start,
                    cells: pending.cells,
                    symbol_counts: pending.symbol_counts,
                    record: pending.record,
                },
            );
        }
        Ok(presentation)
    }
}
