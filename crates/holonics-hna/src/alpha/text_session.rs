//! An exterior text application over one borrowed native field. Every received or self-emitted
//! symbol uses that field's ordinary recurrence. There is no optimizer, response lookup or model
//! clone here. A report is not a durable session artifact.
use super::{
    material::AlphaMaterialError,
    text_codec::{
        TEXT_INPUT_CHANNELS, TextCodeDisposition, TextCodeReading, TextSymbol,
        read_constitutive_text_symbol, read_text_symbol,
    },
};
use holonic_engine::native_ecology::constitutive_fibre::{
    NativeConstitutiveField, NativeFieldEmission, NativeFieldOccurrence, NativeFieldSourceAnchor,
};
use serde::Serialize;

/// An exterior receiving family over the same field. Emitted symbols still enter the ordinary
/// recurrence and can change its successor; this choice supplies no separate learning law.
#[derive(Clone, Copy, Debug, Default, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum TextCurrentReceiver {
    #[default]
    Material,
    Constitutive,
}

#[derive(Debug, Serialize)]
#[serde(tag = "kind", content = "reason", rename_all = "kebab-case")]
pub enum TextGenerationDisposition {
    CompletedPart,
    Open,
    ReservedCodeword,
    Interrupted,
    NativeRefusal(String),
}

#[derive(Debug, Serialize)]
pub struct TextGeneration {
    pub native_from: usize,
    pub native_until: usize,
    pub emitted_octets: Vec<u8>,
    pub readings: Vec<TextCodeReading>,
    pub disposition: TextGenerationDisposition,
    pub pending_return: Option<TextSymbol>,
}

pub(super) struct TextFieldSource {
    pub(super) source: NativeFieldEmission,
    pub(super) occurrence: usize,
}

pub struct TextFieldSession<'field, 'chart> {
    pub(super) field: &'field mut NativeConstitutiveField<'chart>,
    pub(super) latest: Option<TextFieldSource>,
    pub(super) next_anchor: Option<NativeFieldSourceAnchor>,
    pub(super) pending: Option<(TextSymbol, NativeFieldOccurrence)>,
}

impl<'field, 'chart> TextFieldSession<'field, 'chart> {
    pub fn on(
        field: &'field mut NativeConstitutiveField<'chart>,
    ) -> Result<Self, AlphaMaterialError> {
        if field.nodes() != TEXT_INPUT_CHANNELS || !field.has_paired_junction() {
            return Err(AlphaMaterialError::Apparatus(
                "text session requires the declared paired text field".into(),
            ));
        }
        Ok(Self {
            field,
            latest: None,
            next_anchor: None,
            pending: None,
        })
    }
    pub fn field(&self) -> &NativeConstitutiveField<'chart> {
        self.field
    }
    /// Read-only condensation of two actual field contacts. This preserves application/source
    /// chronology and delegates the complete shared-drive condition to the native owner.
    pub fn condense_shared_drive_mode(
        &mut self,
        left: usize,
        right: usize,
    ) -> Result<
        holonic_engine::native_ecology::constitutive_fibre::NativeSharedDriveMode<'chart>,
        AlphaMaterialError,
    > {
        Ok(self.field.condense_shared_drive_mode(left, right)?)
    }
    /// Receive this field's already admitted mode through its actual complete material map.
    /// This reads the existing operator and does not enact another developmental occurrence.
    pub fn read_material_mode(
        &mut self,
        source: usize,
        mode: &holonic_engine::native_ecology::constitutive_fibre::NativeSharedDriveMode<'chart>,
    ) -> Result<
        holonic_engine::native_ecology::constitutive_fibre::NativeMaterialModeReturn<'chart>,
        AlphaMaterialError,
    > {
        Ok(self.field.read_material_mode_using(source, mode)?)
    }
    /// Exterior placement at a declared application boundary. This does not enact a symbol.
    pub fn archive_history(&mut self) -> Result<(), AlphaMaterialError> {
        let at = self.field.occurrence_count();
        self.field.archive_history_before(at)?;
        Ok(())
    }
    pub fn pending_symbol(&self) -> Option<TextSymbol> {
        self.pending.as_ref().map(|v| v.0)
    }
    /// A declared inscription boundary, without resetting the continuing ecology. An available
    /// parent supplies shared historical standing to the first actual symbol of this part.
    pub fn begin_part(
        &mut self,
        anchor: Option<&NativeFieldSourceAnchor>,
    ) -> Result<(), AlphaMaterialError> {
        if self.pending.is_some() {
            return Err(AlphaMaterialError::Apparatus(
                "native reception is pending".into(),
            ));
        }
        self.latest = None;
        self.next_anchor = anchor.cloned();
        Ok(())
    }
    pub fn retain_part_source(&self) -> Result<NativeFieldSourceAnchor, AlphaMaterialError> {
        let latest = self
            .latest
            .as_ref()
            .ok_or_else(|| AlphaMaterialError::Apparatus("no completed native source".into()))?;
        Ok(self.field.retain_source(&latest.source)?)
    }
    pub fn receive(&mut self, symbol: TextSymbol) -> Result<(), AlphaMaterialError> {
        self.stage(symbol)?;
        self.retry_pending()
    }
    /// Retain one decoded exterior symbol and its actual source before native enactment.
    /// This boundary can be checkpointed; another input cannot overwrite it.
    pub fn stage(&mut self, symbol: TextSymbol) -> Result<(), AlphaMaterialError> {
        if self.pending.is_some() {
            return Err(AlphaMaterialError::Apparatus(
                "native reception is pending".into(),
            ));
        }
        let occurrence = if let Some(anchor) = self.next_anchor.take() {
            NativeFieldOccurrence::through_anchor(&anchor, symbol.inputs())
        } else if let Some(previous) = self.latest.take() {
            NativeFieldOccurrence::through(previous.source, symbol.inputs())
        } else {
            NativeFieldOccurrence::entering(symbol.inputs())
        };
        self.pending = Some((symbol, occurrence));
        Ok(())
    }
    /// A known arithmetic refusal keeps this exact occurrence; unknown completion is refused
    /// by the native owner. No symbol is changed, and no successful occurrence is replayed.
    pub fn retry_pending(&mut self) -> Result<(), AlphaMaterialError> {
        let (_, occurrence) = self
            .pending
            .as_mut()
            .ok_or_else(|| AlphaMaterialError::Apparatus("no pending native reception".into()))?;
        let next = self.field.advance_resident(occurrence)?;
        self.latest = Some(TextFieldSource {
            occurrence: next.lineage.occurrence,
            source: next.source,
        });
        self.pending = None;
        Ok(())
    }
    pub fn generate(&mut self, work_limit: usize) -> TextGeneration {
        self.generate_with_receiver(work_limit, TextCurrentReceiver::Material)
    }

    pub fn generate_with_receiver(
        &mut self,
        work_limit: usize,
        receiver: TextCurrentReceiver,
    ) -> TextGeneration {
        let mut result = TextGeneration {
            native_from: self.field.occurrence_count(),
            native_until: self.field.occurrence_count(),
            emitted_octets: Vec::new(),
            readings: Vec::new(),
            disposition: TextGenerationDisposition::Interrupted,
            pending_return: self.pending_symbol(),
        };
        for _ in 0..work_limit {
            let Some(latest) = &self.latest else {
                result.disposition = TextGenerationDisposition::NativeRefusal(
                    "no available source or an earlier reception is pending".into(),
                );
                break;
            };
            let received = match receiver {
                TextCurrentReceiver::Material => read_text_symbol(self.field, latest.occurrence),
                TextCurrentReceiver::Constitutive => self
                    .field
                    .retain_source(&latest.source)
                    .map_err(AlphaMaterialError::from)
                    .and_then(|source| read_constitutive_text_symbol(self.field, &source)),
            };
            let reading = match received {
                Ok(reading) => reading,
                Err(error) => {
                    result.disposition =
                        TextGenerationDisposition::NativeRefusal(error.to_string());
                    break;
                }
            };
            let symbol = match reading.disposition {
                TextCodeDisposition::Symbol { symbol } => Some(symbol),
                TextCodeDisposition::Open => {
                    result.disposition = TextGenerationDisposition::Open;
                    None
                }
                TextCodeDisposition::Reserved { .. } => {
                    result.disposition = TextGenerationDisposition::ReservedCodeword;
                    None
                }
            };
            result.readings.push(reading);
            let Some(symbol) = symbol else {
                break;
            };
            if let TextSymbol::Octet(value) = symbol {
                result.emitted_octets.push(value);
            }
            if let Err(error) = self.receive(symbol) {
                result.disposition = TextGenerationDisposition::NativeRefusal(error.to_string());
                break;
            }
            if symbol == TextSymbol::EndPart {
                result.disposition = TextGenerationDisposition::CompletedPart;
                break;
            }
        }
        result.native_until = self.field.occurrence_count();
        result.pending_return = self.pending_symbol();
        result
    }
}
