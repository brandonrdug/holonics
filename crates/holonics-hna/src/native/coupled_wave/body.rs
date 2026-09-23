//! Move-owned adapter for affine and dependent coupled-wave bodies.
//!
//! This layer only transfers ownership and routes declared native operations.  It does not
//! select a material alternative or read device sections into host numerical state.
use super::super::NativeSessionError;
use holonic_engine::{
    native_ecology::constitutive_fibre::{
        ConstitutiveSourceRefusal, CoupledConstitutiveRest, NormalCoupledContact,
        NormalCoupledObservation, NormalFamilyBasisFace, NormalWaveBasisChart, NormalWaveCoupled,
        NormalWaveRest, ResidentConstitutiveCurrent, ResidentConstitutiveSection,
        ResidentCoupledConstitutive, ResidentNormalInput, ResidentNormalWave, WaveSourceReceiver,
    },
    resident_section::{ResidentSection, ResidentSurface},
};
use serde_json::{Value, json};
use std::io::{Read, Write};

fn invalid(message: impl ToString) -> NativeSessionError {
    NativeSessionError::Application(message.to_string())
}

mod field;
use field::FieldModel;
pub use field::formation::NativeFieldFormation;
use field::incident::IncidentFieldModel;
pub use field::incident::{
    GeneratorIncidentFieldSpec, GeneratorPhasePort, GeneratorPhaseReceiverBinding,
    GeneratorSourceBinding, GeneratorSourceContact, GeneratorSourceContactKind,
    IncidentFieldSolver, IncidentFieldSpec, IncidentParticipationChart,
    NativeGeneratorPhaseReception, NativeIncidentGenerated, NativeIncidentMaterialReturn,
    NativeIncidentModelRest, ReactionDepositRecord, ReactionLaw,
};
pub use field::{
    NativeFieldAttachRefusal, NativeFieldGeneratedSection, NativeFieldModelRest,
    NativeFieldReactionPort,
};

enum BodyState<'c> {
    Field(FieldModel<'c>),
    Incident(IncidentFieldModel<'c>),
    Affine(ResidentNormalWave<'c, NormalWaveCoupled<'c>>),
    Constitutive(ResidentCoupledConstitutive<'c>),
}

pub struct NativeCoupledBody<'c> {
    state: Option<BodyState<'c>>,
}

impl<'c> NativeCoupledBody<'c> {
    /// Supply an actual condition through the same continuing owner. It changes
    /// following generator reads while retained predictions keep their former conditions.
    pub fn receive_condition(
        &mut self,
        incoming: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<(), NativeSessionError> {
        match self.state_mut()? {
            BodyState::Field(field) => field.receive_condition(incoming),
            BodyState::Incident(_) => Err(invalid(
                "incident conditions come from the declared transported current differences",
            )),

            BodyState::Affine(w) => Ok(w.receive_condition(incoming)?),
            BodyState::Constitutive(b) => Ok(b.receive_condition(incoming)?),
        }
    }
    /// An affine body is available only while it is the actual continuing representation.
    /// The frozen substrate of a dependent generator is deliberately not exposed here.
    pub fn affine_wave(&self) -> Option<&ResidentNormalWave<'c, NormalWaveCoupled<'c>>> {
        match self.state.as_ref()? {
            BodyState::Field(_) | BodyState::Incident(_) => None,

            BodyState::Affine(w) => Some(w),
            BodyState::Constitutive(_) => None,
        }
    }
    /// The same coupled HNN owner can serve numerical sections directly, without requiring
    /// an application to first choose a symbol codec. The text session uses this constructor.
    pub fn from_wave(wave: ResidentNormalWave<'c, NormalWaveCoupled<'c>>) -> Self {
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
            BodyState::Field(field) => field.epoch(),
            BodyState::Incident(field) => field.epoch(),

            BodyState::Affine(wave) => wave.epoch(),
            BodyState::Constitutive(body) => body.epoch(),
        }
    }

    pub fn pending_coupled_predictions(&self) -> usize {
        match self.state.as_ref().expect("initialized coupled body") {
            BodyState::Field(field) => field.pending(),
            BodyState::Incident(field) => field.pending(),

            BodyState::Affine(wave) => wave.pending_coupled_predictions(),
            BodyState::Constitutive(body) => body.pending_prediction_ids().count(),
        }
    }

    pub fn scope(&self) -> &'static str {
        match self.state.as_ref().expect("initialized coupled body") {
            BodyState::Field(_) => "constituted-field-joint",
            BodyState::Incident(_) => "incident-field-joint",

            BodyState::Affine(_) => "projected-family-joint",
            BodyState::Constitutive(_) => "declared-source-section",
        }
    }

    pub fn roots(&self) -> usize {
        match self.state.as_ref().expect("initialized coupled body") {
            BodyState::Field(field) => field.roots(),
            BodyState::Incident(field) => field.roots(),

            BodyState::Affine(w) => w.normal_material().roots(),
            BodyState::Constitutive(b) => b.roots(),
        }
    }
    pub fn members(&self) -> usize {
        match self.state.as_ref().expect("initialized coupled body") {
            BodyState::Field(field) => field.members(),
            BodyState::Incident(field) => field.members(),

            BodyState::Affine(w) => w.neighborhood().members(),
            BodyState::Constitutive(b) => b.members(),
        }
    }
    pub fn passages(&self) -> u64 {
        match self.state.as_ref().expect("initialized coupled body") {
            BodyState::Field(field) => field.passages(),
            BodyState::Incident(field) => field.passages(),

            BodyState::Affine(w) => w.current().passages(),
            BodyState::Constitutive(b) => b.passages(),
        }
    }
    pub fn normal_observations(&self) -> Option<u64> {
        match self.state.as_ref().expect("initialized coupled body") {
            BodyState::Field(field) => field.observations(),
            BodyState::Incident(field) => field.observations(),

            BodyState::Affine(w) => Some(w.normal_material().observations()),
            BodyState::Constitutive(_) => None,
        }
    }

    /// Inspect the actual predictive material, including its reference error, at this body's
    /// current receiver scope. This explicit observer is not part of native hot execution.
    pub fn inspect_predictive_material(
        &mut self,
        member: usize,
    ) -> Result<Value, NativeSessionError> {
        let scope = self.scope();
        let state = match self.state_mut()? {
            BodyState::Field(field) => return field.inspect_material(),
            BodyState::Incident(field) => return field.inspect_material(member),

            BodyState::Affine(wave) => wave
                .neighborhood()
                .predictive_material(member)?
                .map(|m| m.inspect().map(|state| (m.observations(), state)))
                .transpose()?,
            BodyState::Constitutive(body) => body.inspect_predictive_material(member)?,
        };
        Ok(
            json!({"source_scope":scope,"member":member,"predictive_material":state.map(|(observations,state)|
            json!({"observations":observations,"state":state})),"coefficient_scope":"applied stored action; normal-reference bounds retained"}),
        )
    }

    /// Current numerical receiver of the same body used by subsequent transport.
    pub fn inspect_current(&mut self) -> Result<Value, NativeSessionError> {
        let scope = self.scope();
        let epoch = self.epoch();
        let (reading, relation) = match self.state_mut()? {
            BodyState::Field(field) => return field.inspect(),
            BodyState::Incident(field) => return field.inspect(),

            BodyState::Affine(wave) => (
                wave.current().read_receiver()?.inspect()?,
                wave.current().affine_relation().inspect()?,
            ),
            BodyState::Constitutive(body) => {
                let value = body.read_receiver()?;
                (
                    value.successor_section().read_receiver()?.inspect()?,
                    value.successor_section().affine_relation().inspect()?,
                )
            }
        };
        Ok(json!({"source_scope":scope,"epoch":epoch,"reading":reading,"relation":relation}))
    }

    pub fn read_basis_face(
        &mut self,
        basis: &NormalWaveBasisChart<'c>,
    ) -> Result<NormalFamilyBasisFace<'c>, NativeSessionError> {
        match self.state_mut()? {
            BodyState::Field(_) | BodyState::Incident(_) => {
                return Err(invalid(
                    "this wave operation requires a wave chart; use the field section operation",
                ));
            }

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
            BodyState::Field(_) | BodyState::Incident(_) => {
                return Err(invalid(
                    "this wave operation requires a wave chart; use the field section operation",
                ));
            }

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
            BodyState::Field(_) | BodyState::Incident(_) => {
                return Err(invalid(
                    "this wave operation requires a wave chart; use the field section operation",
                ));
            }

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
            BodyState::Field(_) | BodyState::Incident(_) => {
                return Err(invalid(
                    "this wave operation requires a wave chart; use the field section operation",
                ));
            }

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
            BodyState::Field(field) => field.pending_ids(),
            BodyState::Incident(field) => field.pending_ids(),

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
            BodyState::Field(_) | BodyState::Incident(_) => {
                return Err(invalid(
                    "this wave operation requires a wave chart; use the field section operation",
                ));
            }

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
    /// One prospective word, not repeated current projections or committed source events.
    pub fn inspect_prospective(
        &mut self,
        word: &[(usize, WaveSourceReceiver)],
        full_family: bool,
    ) -> Result<Value, NativeSessionError> {
        let epoch = self.epoch();
        let scope = self.scope();
        self.with_prospective(word, |future| {
            Self::describe_prospective(future, epoch, scope, word, full_family)
        })
    }
    pub(super) fn describe_prospective(
        future: &holonic_engine::native_ecology::constitutive_fibre::NormalWaveFamilyReceiver<
            '_,
            'c,
        >,
        epoch: u64,
        scope: &str,
        word: &[(usize, WaveSourceReceiver)],
        full_family: bool,
    ) -> Result<Value, NativeSessionError> {
        let reading = future.inspect()?;
        let states = (0..reading.state_count)
            .map(|state| {
                let part = reading.projected_state(state).map(|v| {
                    let wire = |v: &[num_rational::BigRational]| {
                        v.iter()
                            .map(super::super::RationalWire::from_rational)
                            .collect::<Vec<_>>()
                    };
                    json!({"previous":wire(&v[..v.len()/2]),"current":wire(&v[v.len()/2..])})
                });
                json!({"state":state,"projection":part})
            })
            .collect::<Vec<_>>();
        let affine = if full_family {
            Some(future.inspect_affine_relation()?)
        } else {
            None
        };
        let coverage = future
            .image()
            .map(|image| image.inspect_coverage())
            .transpose()?;
        Ok(
            json!({"source_scope":scope,"source_epoch":epoch,"word":word,
                "receiver_representation":if future.point_word().is_some(){"generated-point-word"}else{"expanded-affine-family"},
                "action_committed":false,"reading":reading,"states":states,
                "anchor":future.source().anchor().inspect()?,"affine_joint":affine,"affine_coverage":coverage,
                "receiver_scope":"one joint minimum-norm output over the nearest supported anchor; not independent marginal selections",
                "source_preservation":"the original anchor and joint source remain; futures use the expanded relation or its retained ordered generating word"}),
        )
    }
    pub(super) fn with_prospective<R>(
        &mut self,
        word: &[(usize, WaveSourceReceiver)],
        read: impl FnOnce(
            &holonic_engine::native_ecology::constitutive_fibre::NormalWaveFamilyReceiver<'_, 'c>,
        ) -> Result<R, NativeSessionError>,
    ) -> Result<R, NativeSessionError> {
        match self.state_mut()? {
            BodyState::Field(_) | BodyState::Incident(_) => {
                return Err(invalid(
                    "this wave operation requires a wave chart; use the field section operation",
                ));
            }

            BodyState::Affine(wave) => read(&wave.read_prospective_word(word)?),
            BodyState::Constitutive(body) => {
                body.with_prospective(word, None, |future| Ok(read(future)))?
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
            BodyState::Field(_) | BodyState::Incident(_) => {
                return Err(invalid(
                    "this wave operation requires a wave chart; use the field section operation",
                ));
            }

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
            BodyState::Field(_) | BodyState::Incident(_) => {
                return Err(invalid(
                    "this wave operation requires a wave chart; use the field section operation",
                ));
            }

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
                let before = b.epoch();
                b.incorporate_prediction(id, observed)?;
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
    /// Empirical normal formation at the original producing source. The return
    /// carries y-v and y-c as resident families. This does not advance wave time;
    /// a dependent body retains the same operation over its parameter generator.
    pub fn observe<'a>(
        &mut self,
        id: u64,
        observed: impl Into<ResidentNormalInput<'a, 'c>>,
    ) -> Result<NormalCoupledObservation<'c>, NativeSessionError>
    where
        'c: 'a,
    {
        let observed = observed.into();
        match self.state_mut()? {
            BodyState::Field(_) | BodyState::Incident(_) => {
                return Err(invalid(
                    "this wave operation requires a wave chart; use the field section operation",
                ));
            }

            BodyState::Affine(wave) => {
                let handle = wave.pending_coupled_prediction(id)?;
                Ok(wave.observe_coupled_prediction(&handle, observed)?)
            }
            BodyState::Constitutive(body) => Ok(body.observe_prediction(id, observed)?),
        }
    }
    pub fn release(&mut self, id: u64) -> Result<(), NativeSessionError> {
        match self.state_mut()? {
            BodyState::Field(field) => field.release(id),
            BodyState::Incident(field) => field.release(id),

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
            BodyState::Field(field) => SavedCoupledBody::Field(field.rest()?),
            BodyState::Incident(field) => SavedCoupledBody::Incident(field.rest()?),

            BodyState::Affine(wave) => SavedCoupledBody::Affine(wave.rest()?),
            BodyState::Constitutive(body) => SavedCoupledBody::Constitutive(body.rest()?),
        })
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum SavedCoupledBody {
    Field(NativeFieldModelRest),
    Incident(NativeIncidentModelRest),
    Affine(NormalWaveRest),
    Constitutive(CoupledConstitutiveRest),
}

impl SavedCoupledBody {
    pub fn roots(&self) -> usize {
        match self {
            Self::Field(rest) => rest.roots(),
            Self::Incident(rest) => rest.roots(),
            Self::Affine(rest) => rest.material().roots(),
            Self::Constitutive(rest) => rest.roots(),
        }
    }
    pub fn members(&self) -> usize {
        match self {
            Self::Field(rest) => rest.members(),
            Self::Incident(rest) => rest.members(),
            Self::Affine(rest) => rest.coupled_members().unwrap_or(0),
            Self::Constitutive(rest) => rest.members(),
        }
    }
    pub fn epoch(&self) -> u64 {
        match self {
            Self::Field(rest) => rest.epoch(),
            Self::Incident(rest) => rest.epoch(),
            Self::Affine(rest) => rest.epoch(),
            Self::Constitutive(rest) => rest.epoch(),
        }
    }
    pub fn has_prediction(&self, id: u64) -> bool {
        match self {
            Self::Field(rest) => rest.has_prediction(id),
            Self::Incident(rest) => rest.has_prediction(id),
            Self::Affine(rest) => rest.has_coupled_prediction(id),
            Self::Constitutive(rest) => rest.has_prediction(id),
        }
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), NativeSessionError> {
        match self {
            Self::Incident(rest) => {
                out.write_all(&[3])?;
                rest.write(out)?;
            }
            Self::Field(rest) => {
                out.write_all(&[2])?;
                rest.write(out)?;
            }
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
            3 => Ok(Self::Incident(NativeIncidentModelRest::read(
                &mut bytes, count,
            )?)),
            2 => Ok(Self::Field(NativeFieldModelRest::read(&mut bytes, count)?)),
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
            Self::Incident(rest) => NativeCoupledBody {
                state: Some(BodyState::Incident(rest.remount(surface)?)),
            },
            Self::Field(rest) => NativeCoupledBody {
                state: Some(BodyState::Field(rest.remount(surface)?)),
            },
            Self::Affine(rest) => {
                NativeCoupledBody::from_wave(rest.remount_coupled(surface, |_| {})?)
            }
            Self::Constitutive(rest) => {
                NativeCoupledBody::from_constitutive(rest.remount(surface)?)
            }
        })
    }
}
