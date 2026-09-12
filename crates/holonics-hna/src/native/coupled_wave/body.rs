//! Move-owned adapter for affine and dependent coupled-wave bodies.
//!
//! This layer only transfers ownership and routes declared native operations.  It does not
//! select a material alternative or read device sections into host numerical state.
use super::super::NativeSessionError;
use holonic_engine::{
    native_ecology::constitutive_fibre::{
        ConstitutiveSourceRefusal, CoupledConstitutiveRest, NormalCoupledContact,
        NormalFamilyBasisFace, NormalWaveBasisChart, NormalWaveCoupled, NormalWaveRest,
        ResidentConstitutiveCurrent, ResidentConstitutiveSection, ResidentCoupledConstitutive,
        ResidentNormalWave, WaveSourceReceiver,
    },
    resident_section::{ResidentSection, ResidentSurface},
};
use serde_json::{Value, json};
use std::io::{Read, Write};

fn invalid(message: impl ToString) -> NativeSessionError {
    NativeSessionError::Application(message.to_string())
}

enum BodyState<'c> {
    Affine(ResidentNormalWave<'c, NormalWaveCoupled<'c>>),
    Constitutive(ResidentCoupledConstitutive<'c>),
}

pub struct NativeCoupledBody<'c> {
    state: Option<BodyState<'c>>,
}

impl<'c> NativeCoupledBody<'c> {
    /// An affine body is available only while it is the actual continuing representation.
    /// The frozen substrate of a dependent generator is deliberately not exposed here.
    pub fn affine_wave(&self)->Option<&ResidentNormalWave<'c,NormalWaveCoupled<'c>>>{
        match self.state.as_ref()? {BodyState::Affine(w)=>Some(w),BodyState::Constitutive(_)=>None}
    }
    pub(crate) fn from_wave(wave: ResidentNormalWave<'c, NormalWaveCoupled<'c>>) -> Self {
        Self {
            state: Some(BodyState::Affine(wave)),
        }
    }

    pub(crate) fn from_constitutive(body: ResidentCoupledConstitutive<'c>) -> Self {
        Self {
            state: Some(BodyState::Constitutive(body)),
        }
    }

    fn state(&self) -> Result<&BodyState<'c>, NativeSessionError> {
        self.state
            .as_ref()
            .ok_or_else(|| invalid("coupled body owner is vacant"))
    }

    fn state_mut(&mut self) -> Result<&mut BodyState<'c>, NativeSessionError> {
        self.state
            .as_mut()
            .ok_or_else(|| invalid("coupled body owner is vacant"))
    }

    pub fn epoch(&self) -> u64 {
        match self.state.as_ref().expect("initialized coupled body") {
            BodyState::Affine(wave) => wave.epoch(),
            BodyState::Constitutive(body) => body.epoch(),
        }
    }

    pub fn pending_coupled_predictions(&self) -> usize {
        match self.state.as_ref().expect("initialized coupled body") {
            BodyState::Affine(wave) => wave.pending_coupled_predictions(),
            BodyState::Constitutive(body) => body.pending_prediction_ids().count(),
        }
    }

    pub fn scope(&self) -> &'static str {
        match self.state.as_ref().expect("initialized coupled body") {
            BodyState::Affine(_) => "projected-family-joint",
            BodyState::Constitutive(_) => "declared-source-section",
        }
    }

    pub fn roots(&self) -> usize {
        match self.state.as_ref().expect("initialized coupled body") {
            BodyState::Affine(w) => w.normal_material().roots(),
            BodyState::Constitutive(b) => b.roots(),
        }
    }
    pub fn members(&self) -> usize {
        match self.state.as_ref().expect("initialized coupled body") {
            BodyState::Affine(w) => w.neighborhood().members(),
            BodyState::Constitutive(b) => b.members(),
        }
    }
    pub fn passages(&self) -> u64 {
        match self.state.as_ref().expect("initialized coupled body") {
            BodyState::Affine(w) => w.current().passages(),
            BodyState::Constitutive(b) => b.passages(),
        }
    }
    pub fn normal_observations(&self) -> Option<u64> {
        match self.state.as_ref().expect("initialized coupled body") {
            BodyState::Affine(w) => Some(w.normal_material().observations()),
            BodyState::Constitutive(_) => None,
        }
    }

    pub fn read_basis_face(
        &mut self,
        basis: &NormalWaveBasisChart<'c>,
    ) -> Result<NormalFamilyBasisFace<'c>, NativeSessionError> {
        match self.state_mut()? {
            BodyState::Affine(wave) => Ok(wave.read_basis_face(basis)?),
            BodyState::Constitutive(body) => Ok(body.read_basis_face(basis)?),
        }
    }

    pub fn advance(
        &mut self,
        member: usize,
        chart: WaveSourceReceiver,
        retain: bool,
    ) -> Result<Option<u64>, NativeSessionError> {
        match self.state_mut()? {
            BodyState::Constitutive(body) => {
                if retain {
                    Ok(Some(body.predict_member(member, chart)?))
                } else {
                    body.advance_member(member, chart)?;
                    Ok(None)
                }
            }
            BodyState::Affine(wave) => {
                let id = wave.contact_ids().find(|id| {
                    wave.contact(*id).ok().is_some_and(|c| {
                        c.member() == member && c.relation().source_receiver() == chart
                    })
                });
                let contact = match id {
                    Some(id) => wave.contact(id)?,
                    None => wave.admit_contact_in_chart(member, chart)?,
                };
                if retain {
                    Ok(Some(wave.predict_contact(&contact)?.handle.id()))
                } else {
                    wave.advance_contact(&contact)?;
                    Ok(None)
                }
            }
        }
    }

    fn affine_contact(
        wave: &mut ResidentNormalWave<'c, NormalWaveCoupled<'c>>,
        member: usize,
        chart: WaveSourceReceiver,
    ) -> Result<NormalCoupledContact<'c>, NativeSessionError> {
        if let Some(id) = wave.contact_ids().find(|id| {
            wave.contact(*id)
                .ok()
                .is_some_and(|c| c.member() == member && c.relation().source_receiver() == chart)
        }) {
            return Ok(wave.contact(id)?);
        }
        Ok(wave.admit_contact_in_chart(member, chart)?)
    }

    // Session codecs retain the original text and cursor for retry; this owned packet is
    // a disposable mount until the native operation accepts it. The engine API returns it
    // on refusal. Do not expose this error-only codec wrapper as a native ownership API.
    pub(crate) fn actuate_field(
        &mut self,
        member: usize,
        chart: WaveSourceReceiver,
        source: ResidentSection<'c>,
        rational: bool,
    ) -> Result<(), NativeSessionError> {
        match self.state_mut()? {
            BodyState::Constitutive(body) => body
                .actuate_field(member, chart, source, rational)
                .map_err(|e: ConstitutiveSourceRefusal<'c>| e.reason.into()),
            BodyState::Affine(wave) => {
                let contact = Self::affine_contact(wave, member, chart)?;
                let section = if rational {
                    ResidentConstitutiveSection::rationals(&source)?
                } else {
                    ResidentConstitutiveSection::integers(&source)?
                };
                wave.actuate_contact_section(&contact, section)
                    .map(|_| ())
                    .map_err(Into::into)
            }
        }
    }

    pub(crate) fn receive_next(
        &mut self,
        member: usize,
        chart: WaveSourceReceiver,
        source: ResidentSection<'c>,
        rational: bool,
    ) -> Result<(), NativeSessionError> {
        match self.state_mut()? {
            BodyState::Constitutive(body) => body
                .receive_next_current(member, chart, source, rational)
                .map_err(|e: ConstitutiveSourceRefusal<'c>| e.reason.into()),
            BodyState::Affine(wave) => {
                let contact = Self::affine_contact(wave, member, chart)?;
                let observed = if rational {
                    ResidentConstitutiveCurrent::rational(&source)?
                } else {
                    ResidentConstitutiveCurrent::integers(&source)?
                };
                wave.receive_contact_next(&contact, observed)
                    .map(|_| ())
                    .map_err(Into::into)
            }
        }
    }

    pub fn pending_ids(&self) -> Result<Vec<u64>, NativeSessionError> {
        Ok(match self.state()? {
            BodyState::Affine(wave) => wave.pending_coupled_prediction_ids().collect(),
            BodyState::Constitutive(body) => body.pending_prediction_ids().collect(),
        })
    }

    pub fn inspect_relation(
        &mut self,
        member: usize,
        chart: WaveSourceReceiver,
    ) -> Result<Value, NativeSessionError> {
        match self.state_mut()? {
            BodyState::Affine(wave) => {
                let id = wave
                    .contact_ids()
                    .find(|id| {
                        wave.contact(*id).is_ok_and(|c| {
                            c.member() == member && c.relation().source_receiver() == chart
                        })
                    })
                    .ok_or_else(|| {
                        invalid("no live contact for this session member and receiver")
                    })?;
                let contact = wave.contact(id)?;
                let candidate = wave.read_contact(&contact)?;
                Ok(
                    json!({"scope":"unpublished-conditional-family","epoch":wave.epoch(),"contact":id,"member":member,"receiver":chart,"reading":candidate.read_receiver()?.inspect()?}),
                )
            }
            BodyState::Constitutive(body) => {
                let epoch = body.epoch();
                let proposed = body.read_proposed_member(member, chart)?;
                Ok(
                    json!({"scope":"unpublished-source-section","epoch":epoch,"member":member,"receiver":chart,"reading":proposed.successor_section().read_receiver()?.inspect()?}),
                )
            }
        }
    }
    pub fn compare(
        &mut self,
        id: u64,
        observed: ResidentConstitutiveCurrent<'_, 'c>,
        row: Option<usize>,
    ) -> Result<Value, NativeSessionError> {
        let epoch = self.epoch();
        let describe=|comparison:&holonic_engine::native_ecology::constitutive_fibre::NormalCoupledComparison<'c>,conditional:bool|->Result<Value,NativeSessionError>{
            let row=row.map(|i|comparison.inspect_row(i)).transpose()?;
            Ok(json!({"scope":if conditional {"dependent-producing-family-section"} else {"joint-producing-family-comparison"},
                "prediction":id,"member":comparison.member(),"receiver":comparison.relation().source_receiver(),
                "producing_material_cut":comparison.relation().relation_cut(),"source_epoch":id-1,"produced_epoch":id,"contemporary_epoch":epoch,
                "parameter_rows":comparison.parameter_rows(),"feature_components":comparison.feature_components(),
                "material_deposited":false,"pending_retained":true,"coefficient_row":row}))
        };
        match self.state_mut()? {
            BodyState::Affine(wave) => {
                let handle = wave.pending_coupled_prediction(id)?;
                let comparison = wave.compare_coupled_prediction(&handle, observed)?;
                describe(&comparison, false)
            }
            BodyState::Constitutive(body) => {
                let section = body.compare_prediction(id, observed)?;
                describe(section.comparison(), section.root().is_some())
            }
        }
    }
    pub fn incorporate(
        &mut self,
        id: u64,
        observed: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<Value, NativeSessionError> {
        // Finish every fallible comparison/receiver operation before transferring the owner.
        let (comparison, coordinates) = match self.state_mut()? {
            BodyState::Affine(wave) => {
                let handle = wave.pending_coupled_prediction(id)?;
                let comparison = wave.compare_coupled_prediction(&handle, observed)?;
                let coordinates = comparison
                    .source()
                    .receiver_coordinates()?
                    .into_coordinates();
                (comparison, coordinates)
            }
            BodyState::Constitutive(b) => {
                if !b.has_prediction(id) {
                    return Err(invalid("no available producing comparison"));
                }
                let before=b.epoch();
                b.incorporate_prediction(id,observed)?;
                return Ok(json!({"return_published":true,"prediction_consumed":id,
                    "before_epoch":before,"after_epoch":b.epoch(),"material_returns":b.material_returns(),
                    "receiver_scope":"declared-source-section","receiver_origin":"joined-producing-source",
                    "representation":"source-dependent-generator"}));
            }
        };
        let before = self.epoch();
        let Some(BodyState::Affine(wave)) = self.state.take() else {
            unreachable!("exclusive affine transfer")
        };
        match wave.into_constitutive_continuation(comparison, coordinates) {
            Ok(body) => {
                let after = body.epoch();
                self.state = Some(BodyState::Constitutive(body));
                Ok(
                    json!({"return_published":true,"prediction_consumed":id,"before_epoch":before,"after_epoch":after,
                    "receiver_scope":"declared-source-section","receiver_origin":"producing-family-receiver","representation":"source-dependent-generator"}),
                )
            }
            Err(refusal) => {
                self.state = Some(BodyState::Affine(refusal.wave));
                Err(refusal.reason.into())
            }
        }
    }
    pub fn release(&mut self, id: u64) -> Result<(), NativeSessionError> {
        match self.state_mut()? {
            BodyState::Affine(wave) => {
                Ok(wave.release_coupled_prediction(&wave.pending_coupled_prediction(id)?)?)
            }
            BodyState::Constitutive(body) => Ok(body.release_prediction(id)?),
        }
    }

    pub fn rest(&self) -> Result<SavedCoupledBody, NativeSessionError> {
        self.save()
    }
    #[cfg(test)]
    pub(super) fn admit_test_contact(
        &mut self,
        member: usize,
        chart: WaveSourceReceiver,
    ) -> Result<(), NativeSessionError> {
        let BodyState::Affine(w) = self.state_mut()? else {
            return Err(invalid("affine test contact"));
        };
        Self::affine_contact(w, member, chart)?;
        Ok(())
    }
    pub fn save(&self) -> Result<SavedCoupledBody, NativeSessionError> {
        Ok(match self.state()? {
            BodyState::Affine(wave) => SavedCoupledBody::Affine(wave.rest()?),
            BodyState::Constitutive(body) => SavedCoupledBody::Constitutive(body.rest()?),
        })
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum SavedCoupledBody {
    Affine(NormalWaveRest),
    Constitutive(CoupledConstitutiveRest),
}

impl SavedCoupledBody {
    pub fn roots(&self) -> usize {
        match self {
            Self::Affine(rest) => rest.material().roots(),
            Self::Constitutive(rest) => rest.roots(),
        }
    }
    pub fn members(&self) -> usize {
        match self {
            Self::Affine(rest) => rest.coupled_members().unwrap_or(0),
            Self::Constitutive(rest) => rest.members(),
        }
    }
    pub fn epoch(&self) -> u64 {
        match self {
            Self::Affine(rest) => rest.epoch(),
            Self::Constitutive(rest) => rest.epoch(),
        }
    }
    pub fn has_prediction(&self, id: u64) -> bool {
        match self {
            Self::Affine(rest) => rest.has_coupled_prediction(id),
            Self::Constitutive(rest) => rest.has_prediction(id),
        }
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), NativeSessionError> {
        match self {
            Self::Affine(rest) => {
                out.write_all(&[0])?;
                rest.write(out)?;
            }
            Self::Constitutive(rest) => {
                out.write_all(&[1])?;
                rest.write(out)?;
            }
        }
        Ok(())
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, NativeSessionError> {
        let mut bytes = input.take(octets);
        let mut tag = [0; 1];
        bytes.read_exact(&mut tag)?;
        let count = octets
            .checked_sub(1)
            .ok_or_else(|| invalid("truncated coupled body"))?;
        match tag[0] {
            0 => Ok(Self::Affine(NormalWaveRest::read(&mut bytes, count)?)),
            1 => Ok(Self::Constitutive(CoupledConstitutiveRest::read(
                &mut bytes, count,
            )?)),
            _ => Err(invalid("unknown coupled body scope tag")),
        }
    }

    pub fn remount<'c>(
        self,
        surface: &'c ResidentSurface<'c>,
    ) -> Result<NativeCoupledBody<'c>, NativeSessionError> {
        Ok(match self {
            Self::Affine(rest) => {
                NativeCoupledBody::from_wave(rest.remount_coupled(surface, |_| {})?)
            }
            Self::Constitutive(rest) => {
                NativeCoupledBody::from_constitutive(rest.remount(surface)?)
            }
        })
    }
}
