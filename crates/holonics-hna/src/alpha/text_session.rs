//! An exterior text application over one borrowed native field. Every received or self-emitted
//! symbol uses that field's ordinary recurrence. There is no optimizer, response lookup or model
//! clone here. A report is not a durable session artifact.
use super::{
    material::AlphaMaterialError,
    text_codec::{
        present_constitutive_text_return, present_material_packet, read_text_symbol_on, TextDirection, TextCodeDisposition, TextCodeReading,
        TextSymbol, TEXT_INPUT_CHANNELS,
    },
};
use holonic_engine::native_ecology::constitutive_fibre::{
    NativeConstitutiveField, NativeFieldEmission, NativeFieldOccurrence, NativeFieldReceiverStatus,
    NativeFieldSourceAnchor, ResidentConstitutiveReturn, ResidentContextualSection,
};
use serde::Serialize;
#[cfg(test)]
mod native_tests;

/// An exterior receiving family over the same field. Emitted symbols still enter the ordinary
/// recurrence and can change its successor; this choice supplies no separate learning law.
#[derive(Clone, Copy, Debug, Default, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum TextCurrentReceiver {
    #[default]
    Material,
    Constitutive,
}

/// A native application is the normal joint-packet path. The other modes retain explicit
/// observation and withdrawal controls for comparisons.
#[derive(Clone,Copy,Debug,PartialEq,Eq,Serialize)]
#[serde(rename_all="kebab-case")]
pub enum TextGenerationSourceMode { Actuation, Observation, Withdrawal }

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
    pub(super) duplex:bool,
    pub(super) pending_direction:TextDirection,
    pub(super) latest: Option<TextFieldSource>,
    pub(super) next_anchor: Option<NativeFieldSourceAnchor>,
    pub(super) pending: Option<(TextSymbol, NativeFieldOccurrence)>,
    pub(super) pending_native: Option<ResidentConstitutiveReturn<'chart>>,
}

impl<'field, 'chart> TextFieldSession<'field, 'chart> {
    pub fn on(
        field: &'field mut NativeConstitutiveField<'chart>,
    ) -> Result<Self, AlphaMaterialError> {
        if field.nodes() != TEXT_INPUT_CHANNELS || !field.has_paired_junction()
            || matches!(field.material_target(),Some(holonic_engine::native_ecology::constitutive_fibre::NativeMaterialTarget::TensorProduct{factor_width}) if factor_width!=2) {
            return Err(AlphaMaterialError::Apparatus(
                "text session requires the declared paired text field".into(),
            ));
        }
        Ok(Self {
            field,
            duplex:false,
            pending_direction:TextDirection::Incoming,
            latest: None,
            next_anchor: None,
            pending: None,
            pending_native: None,
        })
    }
    pub fn duplex(&self)->bool{self.duplex}
    /// Declare the two-port codec before cultivation. Old models keep their recorded chart.
    pub fn enable_duplex(&mut self)->Result<(),AlphaMaterialError>{
        if self.field.occurrence_count()!=0 || self.pending.is_some() || self.field.material_target()!=Some(holonic_engine::native_ecology::constitutive_fibre::NativeMaterialTarget::TensorProduct{factor_width:2}){
            return Err(AlphaMaterialError::Apparatus("duplex text must be founded on an empty binary packet field".into()));
        }
        self.duplex=true;Ok(())
    }
    pub fn pending_direction(&self)->Option<TextDirection>{self.pending.as_ref().map(|_|self.pending_direction)}
    pub fn field(&self) -> &NativeConstitutiveField<'chart> {
        self.field
    }
    pub fn enable_operative_contacts(&mut self) -> Result<(), AlphaMaterialError> {
        Ok(self.field.enable_operative_contacts()?)
    }
    /// Apply the native constrained contact response to the latest actual reception. This
    /// supplies no application-authored delta or new occurrence. Failure preserves the field
    /// as it stood after that reception, and success preserves its available emission.
    pub fn respond_to_latest_material(
        &mut self,
        group_width: usize,
        metric: holonic_engine::native_ecology::constitutive_fibre::NativeMaterialPullbackMetric,
    ) -> Result<Option<holonic_engine::native_ecology::constitutive_fibre::NativeMaterialContactResponse<'chart>>, AlphaMaterialError> {
        self.respond_to_latest_material_with_realization(group_width,metric,
            holonic_engine::native_ecology::constitutive_fibre::NativeContactRealization::EnclosedFlow)
    }
    pub fn respond_to_latest_material_with_realization(
        &mut self,
        group_width: usize,
        metric: holonic_engine::native_ecology::constitutive_fibre::NativeMaterialPullbackMetric,
        realization: holonic_engine::native_ecology::constitutive_fibre::NativeContactRealization,
    ) -> Result<Option<holonic_engine::native_ecology::constitutive_fibre::NativeMaterialContactResponse<'chart>>, AlphaMaterialError> {
        self.respond_to_latest_material_observing(group_width, metric, realization, |_, _| ()).map(|r| r.0)
    }
    /// A declared read-only observer may inspect the actual response before its ordinary commit.
    /// Its result does not gate the update. In particular, a diagnostic can return its own error
    /// as R while the native return still proceeds through the same publication owner.
    pub fn respond_to_latest_material_observing<R>(
        &mut self,
        group_width: usize,
        metric: holonic_engine::native_ecology::constitutive_fibre::NativeMaterialPullbackMetric,
        realization: holonic_engine::native_ecology::constitutive_fibre::NativeContactRealization,
        observer: impl FnOnce(&NativeConstitutiveField<'chart>,
            &holonic_engine::native_ecology::constitutive_fibre::NativeMaterialContactResponse<'chart>) -> R,
    ) -> Result<(Option<holonic_engine::native_ecology::constitutive_fibre::NativeMaterialContactResponse<'chart>>, Option<R>), AlphaMaterialError> {
        if self.pending.is_some() {
            return Err(AlphaMaterialError::Apparatus("native reception is pending".into()));
        }
        let Some(latest)=self.latest.as_ref() else {return Ok((None,None));};
        let query=if metric==holonic_engine::native_ecology::constitutive_fibre::NativeMaterialPullbackMetric::SquaredCurrent {
            let Some(query)=self.field.pull_back_material_current(latest.occurrence)? else {return Ok((None,None));};
            query
        } else {
            let Some(returned)=self.field.normalized_material_return(latest.occurrence,group_width,
                holonic_engine::resident_section::SeriesAperture(32))? else {return Ok((None,None));};
            self.field.pull_back_material_source(&returned,metric)?
        };
        let response=self.field.material_contact_response(query)?;
        let observed = observer(self.field, &response);
        self.field.apply_material_contact_realization(&response,realization)?;
        Ok((Some(response),Some(observed)))
    }
    /// Native contact/current staging over this same borrowed field. It changes no source
    /// capability or developmental occurrence, and cannot outlive the field's decoder.
    pub fn stage_operative_contacts(
        &mut self,
    ) -> Result<
        holonic_engine::native_ecology::constitutive_fibre::NativeOperativeContactStaging<
            '_,
            'chart,
        >,
        AlphaMaterialError,
    > {
        Ok(self.field.stage_operative_contacts()?)
    }
    /// Derive immutable contextual material from this body's actual passages, preserving
    /// the text session's current source and application chronology.
    pub fn derive_contextual_contrast(
        &mut self,
        receiving: [usize; 2],
    ) -> Result<ResidentContextualSection<'chart>, AlphaMaterialError> {
        Ok(self.field.derive_contextual_contrast(receiving)?)
    }
    /// Retain the whole native point return for the next ordinary field occurrence. Only the
    /// exterior codeword is read; its amplitude and phase are not re-encoded as unit impulses.
    pub fn stage_native_return(
        &mut self,
        returned: ResidentConstitutiveReturn<'chart>,
    ) -> Result<TextSymbol, AlphaMaterialError> {
        if self.pending.is_some() {
            return Err(AlphaMaterialError::Apparatus(
                "native reception is pending".into(),
            ));
        }
        if returned.target_width() != 2 * TEXT_INPUT_CHANNELS {
            return Err(AlphaMaterialError::Apparatus(
                "native return has a different receiving chart".into(),
            ));
        }
        let reading = returned.read_differential_pairs(0, super::text_codec::TEXT_BIT_PAIRS)?;
        if reading.status != NativeFieldReceiverStatus::Unique || reading.unresolved != 0 {
            return Err(AlphaMaterialError::Apparatus("native text-current reception requires a supported actual point and resolved codeword".into()));
        }
        let symbol = TextSymbol::from_codeword(reading.positive as u16).ok_or_else(|| {
            AlphaMaterialError::Apparatus(
                "native current lies outside the text codeword chart".into(),
            )
        })?;
        self.stage_presented_native_return(returned, symbol)?;
        Ok(symbol)
    }
    // Both callers have read this immutable return's supported point and exact codeword.
    // Keep that reading; generation must not issue a second identical terminal readout.
    fn stage_presented_native_return(
        &mut self,
        returned: ResidentConstitutiveReturn<'chart>,
        symbol: TextSymbol,
    ) -> Result<(), AlphaMaterialError> {
        if self.duplex || self.pending.is_some() || returned.target_width() != 2 * TEXT_INPUT_CHANNELS {
            return Err(AlphaMaterialError::Apparatus("incompatible pending native return".into()));
        }
        let occurrence = if let Some(anchor) = self.next_anchor.take() {
            NativeFieldOccurrence::through_anchor(&anchor, vec![])
        } else if let Some(previous) = self.latest.take() {
            NativeFieldOccurrence::through(previous.source, vec![])
        } else {
            NativeFieldOccurrence::entering(vec![])
        };
        self.pending = Some((symbol, occurrence));
        self.pending_native = Some(returned);
        self.pending_direction=TextDirection::Incoming;
        Ok(())
    }
    pub fn receive_native_return(
        &mut self,
        returned: ResidentConstitutiveReturn<'chart>,
    ) -> Result<TextSymbol, AlphaMaterialError> {
        let symbol = self.stage_native_return(returned)?;
        self.retry_pending()?;
        Ok(symbol)
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
    /// Change only the representation of retained native return factors.
    pub fn condense_current_journal(&mut self) -> Result<
        holonic_engine::native_ecology::constitutive_fibre::NativeOperativeCurrentFactorCondensation,
        AlphaMaterialError> {
        Ok(self.field.condense_operative_current_journal()?)
    }
    /// Exterior placement at a declared application boundary. This does not enact a symbol.
    pub fn archive_history(&mut self) -> Result<(), AlphaMaterialError> {
        let at = self.field.occurrence_count();
        self.field.archive_history_before(at)?;
        Ok(())
    }
    /// Apply a caused codec face with fresh canonical input impulses. This is a driven exterior
    /// boundary, not amplitude transport of the retained material ball. Source lineage survives
    /// the presentation; a repeated face does not establish a complete-current cycle or closure.
    pub fn stage_material_actuation(&mut self,actuation:holonic_engine::native_ecology::constitutive_fibre::NativeMaterialActuation)
        ->Result<TextSymbol,AlphaMaterialError>{
        self.stage_material_actuation_with_phases(actuation,None)
    }
    /// A declared input-phase realization, with unchanged complete tensor target. Its actual
    /// input is retained on refusal/restart; no phase is inferred from an expected text answer.
    pub fn stage_material_actuation_with_phases(&mut self,actuation:holonic_engine::native_ecology::constitutive_fibre::NativeMaterialActuation,
        phases:Option<&[holonic_engine::ExactWavePhaseTransport]>) ->Result<TextSymbol,AlphaMaterialError>{
        if self.pending.is_some() || self.next_anchor.is_some(){return Err(AlphaMaterialError::Apparatus("incompatible pending material actuation".into()));}
        let latest=self.latest.as_ref().ok_or_else(||AlphaMaterialError::Apparatus("no available material source".into()))?;
        if !actuation.describes_source(&latest.source){return Err(AlphaMaterialError::Apparatus("foreign material actuation".into()));}
        let direction=match actuation.reading().quadrature {
            holonic_engine::native_ecology::constitutive_fibre::NativePacketQuadrature::Real=>TextDirection::Incoming,
            holonic_engine::native_ecology::constitutive_fibre::NativePacketQuadrature::Imaginary=>TextDirection::Outgoing,
        };
        if !self.duplex && direction!=TextDirection::Incoming{return Err(AlphaMaterialError::Apparatus("actuation is outside the text boundary chart".into()));}
        let reading=present_material_packet(actuation.reading().clone())?;
        let TextCodeDisposition::Symbol{symbol}=reading.disposition else{return Err(AlphaMaterialError::Apparatus("material actuation has no text face".into()));};
        let canonical=symbol.inputs_on(direction);
        let input=match phases {
            Some(phases)=>actuation.reading().target_chart.transport_factor_phases(&canonical,phases)?,
            None=>canonical,
        };
        let latest=self.latest.take().unwrap();
        let occurrence=NativeFieldOccurrence::actuating(latest.source,input,actuation);
        self.pending=Some((symbol,occurrence));self.pending_direction=direction;Ok(symbol)
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
        self.receive_on(symbol,TextDirection::Incoming)
    }
    pub fn receive_on(&mut self,symbol:TextSymbol,direction:TextDirection)->Result<(),AlphaMaterialError>{
        self.stage_on(symbol,direction)?;self.retry_pending()
    }
    /// Retain one decoded exterior symbol and its actual source before native enactment.
    /// This boundary can be checkpointed; another input cannot overwrite it.
    pub fn stage(&mut self, symbol: TextSymbol) -> Result<(), AlphaMaterialError> {
        self.stage_on(symbol,TextDirection::Incoming)
    }
    pub fn stage_on(&mut self,symbol:TextSymbol,direction:TextDirection)->Result<(),AlphaMaterialError>{
        if self.pending.is_some() {
            return Err(AlphaMaterialError::Apparatus(
                "native reception is pending".into(),
            ));
        }
        let occurrence = if let Some(anchor) = self.next_anchor.take() {
            NativeFieldOccurrence::through_anchor(&anchor, symbol.inputs_on(if self.duplex{direction}else{TextDirection::Incoming}))
        } else if let Some(previous) = self.latest.take() {
            NativeFieldOccurrence::through(previous.source, symbol.inputs_on(if self.duplex{direction}else{TextDirection::Incoming}))
        } else {
            NativeFieldOccurrence::entering(symbol.inputs_on(if self.duplex{direction}else{TextDirection::Incoming}))
        };
        self.pending = Some((symbol, occurrence));
        self.pending_direction=direction;
        Ok(())
    }
    /// A known arithmetic refusal keeps this exact occurrence; unknown completion is refused
    /// by the native owner. No symbol is changed, and no successful occurrence is replayed.
    pub fn retry_pending(&mut self) -> Result<(), AlphaMaterialError> {
        let (_, occurrence) = self
            .pending
            .as_mut()
            .ok_or_else(|| AlphaMaterialError::Apparatus("no pending native reception".into()))?;
        let next = if let Some(native) = &self.pending_native {
            self.field
                .advance_current_resident(occurrence, native.current())?
        } else {
            self.field.advance_resident(occurrence)?
        };
        self.latest = Some(TextFieldSource {
            occurrence: next.lineage.occurrence,
            source: next.source,
        });
        self.pending = None;
        self.pending_native = None;
        self.pending_direction=TextDirection::Incoming;
        Ok(())
    }
    /// Continue the same ecology through its declared feedback boundary. `work_limit` reports
    /// interruption; a learned EndPart reports the codec's part boundary. Neither is a general
    /// extinction law or proof that the produced answer fulfills its situated request.
    pub fn generate(&mut self, work_limit: usize) -> TextGeneration {
        self.generate_with_receiver(work_limit, TextCurrentReceiver::Material)
    }

    pub fn generate_with_receiver(
        &mut self,
        work_limit: usize,
        receiver: TextCurrentReceiver,
    ) -> TextGeneration {
        let source_mode=if matches!(receiver,TextCurrentReceiver::Material) && matches!(self.field.material_target(),Some(holonic_engine::native_ecology::constitutive_fibre::NativeMaterialTarget::TensorProduct{..})){
            TextGenerationSourceMode::Actuation
        }else{TextGenerationSourceMode::Observation};
        self.generate_with_source_mode(work_limit,receiver,source_mode)
    }
    /// Declared source-incidence intervention for comparison. Withdrawing the self contact
    /// still advances the same field through an unlinked occurrence; it is not a model default.
    pub fn generate_with_source_contact(&mut self,work_limit:usize,receiver:TextCurrentReceiver,source_contact:bool)->TextGeneration{
        self.generate_with_source_mode(work_limit,receiver,if source_contact{TextGenerationSourceMode::Observation}else{TextGenerationSourceMode::Withdrawal})
    }
    pub fn generate_with_source_mode(&mut self,work_limit:usize,receiver:TextCurrentReceiver,source_mode:TextGenerationSourceMode)->TextGeneration{
        self.generate_in_actuation_chart(work_limit,receiver,source_mode,None)
    }
    /// Apply the same declared phase transports to each generated tensor factor. The field
    /// keeps its current chart and coefficients; this is an exterior actuation intervention.
    pub fn generate_with_factor_phases(&mut self,work_limit:usize,phases:&[holonic_engine::ExactWavePhaseTransport])->TextGeneration{
        self.generate_in_actuation_chart(work_limit,TextCurrentReceiver::Material,TextGenerationSourceMode::Actuation,Some(phases))
    }
    fn generate_in_actuation_chart(&mut self,work_limit:usize,receiver:TextCurrentReceiver,
        source_mode:TextGenerationSourceMode,phases:Option<&[holonic_engine::ExactWavePhaseTransport]>)->TextGeneration{
        let mut result = TextGeneration {
            native_from: self.field.occurrence_count(),
            native_until: self.field.occurrence_count(),
            emitted_octets: Vec::new(),
            readings: Vec::new(),
            disposition: TextGenerationDisposition::Interrupted,
            pending_return: self.pending_symbol(),
        };
        if let Some(phases)=phases {
            let validation=self.field.material_target().ok_or_else(||AlphaMaterialError::Apparatus("missing phase target".into()))
                .and_then(|target|target.transport_factor_phases(
                    &vec![holonic_engine::native_ecology::constitutive_fibre::NativePhaseCurrent::unit();self.field.nodes()],phases)
                    .map_err(AlphaMaterialError::from));
            if let Err(error)=validation {
                result.disposition=TextGenerationDisposition::NativeRefusal(error.to_string());return result;
            }
        }
        if self.duplex && matches!(receiver,TextCurrentReceiver::Constitutive){
            result.disposition=TextGenerationDisposition::NativeRefusal("duplex text uses its joint material receiver".into());return result;
        }
        for _ in 0..work_limit {
            let Some(latest) = &self.latest else {
                result.disposition = TextGenerationDisposition::NativeRefusal(
                    "no available source or an earlier reception is pending".into(),
                );
                break;
            };
            let mut native_return = None;
            let mut material_actuation = None;
            let received = match receiver {
                TextCurrentReceiver::Material => {
                    let direction=if self.duplex{TextDirection::Outgoing}else{TextDirection::Incoming};
                    if source_mode==TextGenerationSourceMode::Actuation {
                        self.field.read_material_actuation(&latest.source,direction.quadrature()).map_err(AlphaMaterialError::from).and_then(|actuation|{
                            let reading=present_material_packet(actuation.reading().clone())?;material_actuation=Some(actuation);Ok(reading)
                        })
                    }else{read_text_symbol_on(self.field,latest.occurrence,direction)}
                },
                TextCurrentReceiver::Constitutive => self
                    .field
                    .retain_source(&latest.source)
                    .map_err(AlphaMaterialError::from)
                    .and_then(|source| {
                        let returned = self.field.read_constitutive_source(&source)?;
                        let reading = present_constitutive_text_return(&returned)?;
                        if reading.native.constitutive_status() == Some(NativeFieldReceiverStatus::Unique) {
                            native_return = Some(returned);
                        }
                        Ok(reading)
                    }),
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
            // A supported point return has an existing native ingress; keep its amplitude and
            // phase instead of replacing it with the decoded codeword's unit impulses.
            // A material actuation carries the selected receiver face and its actual source.
            // Its tensor-basis realization is not an observed target or a recovered latent point.
            if source_mode==TextGenerationSourceMode::Withdrawal {
                if let Err(error)=self.begin_part(None){result.disposition=TextGenerationDisposition::NativeRefusal(error.to_string());break;}
            }
            let received = if let Some(actuation)=material_actuation {
                self.stage_material_actuation_with_phases(actuation,phases).and_then(|_|self.retry_pending())
            } else if let Some(returned) = native_return {
                self.stage_presented_native_return(returned, symbol)
                    .and_then(|_| self.retry_pending())
            } else {
                self.receive_on(symbol,TextDirection::Outgoing)
            };
            if let Err(error) = received {
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
