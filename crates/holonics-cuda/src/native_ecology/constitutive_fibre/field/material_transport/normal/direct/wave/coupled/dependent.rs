//! **The published constitutive continuation** (plan phase 12b).
//!
//! [definition; agent-inferred] After a pending coupled prediction returns at its declared source
//! section, the continuing object is the same coupled wave Holon at its contemporary point: the
//! return deposited the section's `θ`-face operands into the member law, the condition and the
//! predictive material (the constitution), and moved the contemporary family one passage through
//! the developed law. [`ResidentCoupledConstitutive`] is that wave with the consumed root's
//! address and two counts; every motion — a source, a field, a next current, a contact advance,
//! a prediction, a further return or observation, a condition — is the wave's own motion at the
//! contemporary cut.
//!
//! [definition] Retired with the transport word (phase 9's owed joint packet): the ordered
//! operation programme that was replayed from a frozen pre-return base on every read, the
//! `θ`-dependent re-evaluation of that programme at arbitrary source sections, and the returned
//! receiver faces imposed at their producing epochs. The retained quotient is the contemporary
//! constitution and family; the dependent family `θ ↦ (h_θ, R_θ)` of a return is read before
//! publication (`ResidentNormalWave::read_coupled_constitutive_family`), not re-evaluated after it.
use super::*;

/// The coupled wave after its first published return (see the module header).
pub struct ResidentCoupledConstitutive<'c> {
    wave: ResidentNormalWave<'c, NormalWaveCoupled<'c>>,
    consumed: u64,
    material_returns: usize,
    source_passages: usize,
}

/// A comparison read at the contemporary cut of a published continuation; `root()` names the
/// consumed return the continuation descends from.
pub struct ConstitutiveComparisonSection<'c> {
    comparison: NormalCoupledComparison<'c>,
    root: Option<u64>,
}
impl<'c> ConstitutiveComparisonSection<'c> {
    pub fn comparison(&self) -> &NormalCoupledComparison<'c> {
        &self.comparison
    }
    /// The consumed root prediction of the continuation this comparison was read in.
    pub fn root(&self) -> Option<u64> {
        self.root
    }
}

/// A section of the published continuation: its contemporary family (`read_receiver`) or an
/// unpublished passage of that family through one member law (`read_proposed_member`).
pub struct ConstitutiveContinuationSection<'c> {
    current: Rc<NormalWaveFamily<'c>>,
    successor: Rc<NormalWaveFamily<'c>>,
}
impl<'c> ConstitutiveContinuationSection<'c> {
    /// The contemporary family.
    pub fn current_section(&self) -> &NormalWaveFamily<'c> {
        &self.current
    }
    /// The section read: the contemporary family itself, or its proposed passage.
    pub fn successor_section(&self) -> &NormalWaveFamily<'c> {
        &self.successor
    }
}

/// Failed ownership transfer returns the wave, the comparison and the receiver.
pub type CoupledConstitutiveRefusal<'c> = NormalRefusal<(
    ResidentNormalWave<'c, NormalWaveCoupled<'c>>,
    NormalCoupledComparison<'c>,
    ResidentSection<'c>,
)>;
/// A refused source passage returns its packet.
pub type ConstitutiveSourceRefusal<'c> = NormalRefusal<ResidentSection<'c>>;

impl<'c> ResidentNormalWave<'c, NormalWaveCoupled<'c>> {
    /// Publish the return of a comparison read at the contemporary cut at the declared receiver
    /// section `θ` and continue as the published continuation. Refusal (including a comparison
    /// read at an earlier cut) returns the unchanged wave, the comparison and the receiver.
    pub fn into_constitutive_continuation(
        mut self,
        comparison: NormalCoupledComparison<'c>,
        receiver: ResidentSection<'c>,
    ) -> Result<ResidentCoupledConstitutive<'c>, CoupledConstitutiveRefusal<'c>> {
        match self.publish_return(&comparison, Some(&receiver)) {
            Ok(()) => Ok(ResidentCoupledConstitutive {
                wave: self,
                consumed: comparison.prediction_id(),
                material_returns: 1,
                source_passages: 0,
            }),
            Err(reason) => Err(NormalRefusal::new((self, comparison, receiver), reason)),
        }
    }
}

impl<'c> ResidentCoupledConstitutive<'c> {
    /// The coupled wave this continuation is.
    pub fn wave(&self) -> &ResidentNormalWave<'c, NormalWaveCoupled<'c>> {
        &self.wave
    }
    /// Receive a known current in the shared condition chart; later motions read it.
    pub fn receive_condition(
        &mut self,
        incoming: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<(), ConstitutiveFibreError> {
        if incoming.width != self.wave.neighborhood().condition().width {
            return Err(ConstitutiveFibreError::Shape);
        }
        self.wave.receive_condition(incoming)
    }
    /// Read a pending prediction's comparison at the contemporary cut.
    pub fn compare_prediction(
        &mut self,
        id: u64,
        observed: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ConstitutiveComparisonSection<'c>, ConstitutiveFibreError> {
        Ok(ConstitutiveComparisonSection {
            comparison: self.wave.compare_coupled_prediction(id, observed)?,
            root: Some(self.consumed),
        })
    }
    /// Return a pending prediction at its source family's receiver, at the contemporary cut.
    pub fn incorporate_prediction(
        &mut self,
        id: u64,
        observed: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<(), ConstitutiveFibreError> {
        self.wave.return_coupled_prediction(id, observed, None)?;
        self.material_returns += 1;
        Ok(())
    }
    /// The empirical normal formation of a pending prediction at the contemporary cut; no wave
    /// passage is added.
    pub fn observe_prediction<'a>(
        &mut self,
        id: u64,
        observed: impl Into<ResidentNormalInput<'a, 'c>>,
    ) -> Result<NormalCoupledObservation<'c>, ConstitutiveFibreError>
    where
        'c: 'a,
    {
        let receipt = self.wave.observe_coupled_prediction(id, observed)?;
        self.material_returns += 1;
        Ok(receipt)
    }
    /// Returns and empirical observations published by this continuation, the root included.
    pub fn material_returns(&self) -> usize {
        self.material_returns
    }
    pub fn epoch(&self) -> u64 {
        self.wave.epoch()
    }
    pub fn consumed_prediction(&self) -> u64 {
        self.consumed
    }
    /// Source and field actuations published since the root return.
    pub fn source_passages(&self) -> usize {
        self.source_passages
    }
    pub fn pending_prediction_ids(&self) -> impl Iterator<Item = u64> + '_ {
        self.wave.pending_coupled_prediction_ids()
    }
    pub fn pending_prediction(&self, id: u64) -> Result<u64, ConstitutiveFibreError> {
        self.wave.pending_coupled_prediction(id)
    }
    pub fn has_prediction(&self, id: u64) -> bool {
        self.wave.has_pending_coupled_prediction(id)
    }
    pub fn release_prediction(&mut self, id: u64) -> Result<(), ConstitutiveFibreError> {
        self.wave.release_coupled_prediction(id)
    }
    /// The contemporary family: the continuation's declared section.
    pub fn read_receiver(
        &mut self,
    ) -> Result<ConstitutiveContinuationSection<'c>, ConstitutiveFibreError> {
        let current = self.wave.current_shared();
        Ok(ConstitutiveContinuationSection {
            successor: Rc::clone(&current),
            current,
        })
    }
    /// The unpublished passage of the contemporary family through one member law.
    pub fn read_proposed_member(
        &mut self,
        member: usize,
        chart: WaveSourceReceiver,
    ) -> Result<ConstitutiveContinuationSection<'c>, ConstitutiveFibreError> {
        Ok(ConstitutiveContinuationSection {
            successor: Rc::new(self.wave.read_member_passage(member, chart)?),
            current: self.wave.current_shared(),
        })
    }
    /// Read a prospective learned word from the contemporary family. `parameters` names another
    /// source section of the consumed return; a published continuation retains only its declared
    /// section, so another section refuses (read it at a pending comparison before publication).
    pub fn with_prospective<R>(
        &mut self,
        word: &[(usize, WaveSourceReceiver)],
        parameters: Option<&ResidentSection<'c>>,
        read: impl FnOnce(&NormalWaveFamilyReceiver<'_, 'c>) -> Result<R, ConstitutiveFibreError>,
    ) -> Result<R, ConstitutiveFibreError> {
        if parameters.is_some() {
            return Err(ConstitutiveFibreError::Rest(
                "a published continuation retains its declared source section only".into(),
            ));
        }
        if word.iter().any(|(member, _)| *member >= self.members()) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let future = self.wave.read_prospective_word(word)?;
        read(&future)
    }
    pub fn roots(&self) -> usize {
        self.wave.normal_material().roots()
    }
    pub fn passages(&self) -> u64 {
        self.wave.current().passages()
    }
    pub fn members(&self) -> usize {
        self.wave.neighborhood().members()
    }
    /// The member's contemporary predictive material.
    pub fn inspect_predictive_material(
        &mut self,
        member: usize,
    ) -> Result<Option<(u64, NormalConstitution)>, ConstitutiveFibreError> {
        self.wave
            .neighborhood()
            .predictive_material(member)?
            .map(|m| Ok((m.observations(), m.inspect()?)))
            .transpose()
    }
    pub fn read_basis_face(
        &mut self,
        chart: &NormalWaveBasisChart<'c>,
    ) -> Result<NormalFamilyBasisFace<'c>, ConstitutiveFibreError> {
        self.wave.read_basis_face(chart)
    }
    pub fn advance_member(
        &mut self,
        member: usize,
        chart: WaveSourceReceiver,
    ) -> Result<(), ConstitutiveFibreError> {
        self.wave.with_admitted(member, chart, |wave, contact| {
            wave.advance_contact(contact).map(|_| ())
        })
    }
    /// Advance through one member and retain its producing operands as a pending prediction.
    pub fn predict_member(
        &mut self,
        member: usize,
        chart: WaveSourceReceiver,
    ) -> Result<u64, ConstitutiveFibreError> {
        self.wave.with_admitted(member, chart, |wave, contact| {
            wave.predict_contact(contact).map(|(id, _)| id)
        })
    }
    pub fn actuate_source(
        &mut self,
        member: usize,
        chart: WaveSourceReceiver,
        source: ResidentSection<'c>,
    ) -> Result<(), ConstitutiveSourceRefusal<'c>> {
        let acted = self.wave.with_admitted(member, chart, |wave, contact| {
            wave.actuate_contact_source(contact, ResidentConstitutiveCurrent::rational(&source)?)
                .map(|_| ())
        });
        match acted {
            Ok(()) => {
                self.source_passages += 1;
                Ok(())
            }
            Err(reason) => Err(NormalRefusal::new(source, reason)),
        }
    }
    pub fn actuate_field(
        &mut self,
        member: usize,
        chart: WaveSourceReceiver,
        source: ResidentSection<'c>,
        rational: bool,
    ) -> Result<(), ConstitutiveSourceRefusal<'c>> {
        let acted = self.wave.with_admitted(member, chart, |wave, contact| {
            let section = if rational {
                ResidentConstitutiveSection::rationals(&source)?
            } else {
                ResidentConstitutiveSection::integers(&source)?
            };
            wave.actuate_contact_section(contact, section).map(|_| ())
        });
        match acted {
            Ok(()) => {
                self.source_passages += 1;
                Ok(())
            }
            Err(reason) => Err(NormalRefusal::new(source, reason)),
        }
    }
    pub fn receive_next_current(
        &mut self,
        member: usize,
        chart: WaveSourceReceiver,
        source: ResidentSection<'c>,
        rational: bool,
    ) -> Result<(), ConstitutiveSourceRefusal<'c>> {
        let acted = self.wave.with_admitted(member, chart, |wave, contact| {
            let observed = if rational {
                ResidentConstitutiveCurrent::rational(&source)?
            } else {
                ResidentConstitutiveCurrent::integers(&source)?
            };
            wave.receive_contact_next(contact, observed).map(|_| ())
        });
        acted.map_err(|reason| NormalRefusal::new(source, reason))
    }
}

mod rest;
pub use rest::CoupledConstitutiveRest;
