//! **The coupled continuation of the normal wave Holon** (plan phases 9 and 12b).
//!
//! [definition] The same wave owner continues through a neighborhood of conditional member laws.
//! Its state is the contemporary anchored family (a point of the Holon); its constitution is the
//! neighborhood (member materials and the shared condition), which only deposition changes. Its
//! fixed normal bank remains available for its own one-cut returns; it is not advanced as a
//! hidden alternative current.
//!
//! [definition; agent-inferred] **Retention (phase 12b, one cut).** A pending coupled prediction
//! retains only its producing operands: the source family it was read from, the admitted member
//! law with its source chart, and its epoch (the address). A comparison, an empirical
//! observation or a return reads that retained source through the *contemporary* member law and
//! condition and returns its residual there; a return then deposits the `θ`-face operands of
//! the source family into the contemporary constitution and moves the contemporary family one
//! passage through the updated law. No ordered relation word is kept between a prediction and
//! its return, and no earlier face is carried through the intervening maps
//! (`Foundation/Standing.lean::standingLaw_exists_iff_future_factors`; the retention audit
//! `research/records/2026-09-22_RETENTION_IS_A_QUOTIENT_NOT_A_TAPE_AND_THE_SOURCE_ENTERS_AS_PHASE_CARRIED_MOMENTS.md`).
use super::*;
pub(super) mod rest;
mod comparison;
mod dependent;
mod observation;
pub use observation::NormalCoupledObservation;
pub use dependent::{
    ConstitutiveComparisonSection, ConstitutiveContinuationSection, ConstitutiveSourceRefusal,
    CoupledConstitutiveRefusal, CoupledConstitutiveRest, ResidentCoupledConstitutive,
};
use comparison::CoupledProducingCut;
pub use comparison::{
    CompiledCoupledJoint, CoupledConstitutiveAlternative, CoupledConstitutiveFamily,
    CoupledJointEvaluation, NormalCoupledComparison,
};
use crate::native_ecology::constitutive_fibre::{
    GeneratorNeighborhoodStep, ResidentGeneratorNeighborhood, ResidentSourcePairs,
    ResidentWaveRelation, WaveSourceReceiver,
};

/// The coupled continuation state of the normal wave Holon (see the module header).
pub struct NormalWaveCoupled<'c> {
    neighborhood: ResidentGeneratorNeighborhood<'c>,
    current: Rc<NormalWaveFamily<'c>>,
    epoch: u64,
    neighborhood_base: u64,
    // Neighborhood cut whose action produced the held current. Formation alone
    // advances neighborhood standing while this source cut stays unchanged.
    current_neighborhood_epoch: u64,
    next_contact: u64,
    active_member: Option<usize>,
    bindings: BTreeMap<u64, Rc<CoupledBinding<'c>>>,
    /// Pending predictions by epoch: each retains its producing operands only.
    pending: BTreeMap<u64, Rc<CoupledProducingCut<'c>>>,
}
struct CoupledBinding<'c> {
    member: usize,
    epoch: u64,
    neighborhood_epoch: u64,
    source: Rc<NormalWaveFamily<'c>>,
    relation: Rc<ResidentWaveRelation<'c>>,
}
/// An explicitly admitted local interaction at this actual source/current and condition cut.
/// Continuation expires its authority; the handle retains its source for read-only inspection.
pub struct NormalCoupledContact<'c> {
    owner: Rc<()>,
    id: u64,
    binding: Rc<CoupledBinding<'c>>,
}
impl<'c> NormalCoupledContact<'c> {
    pub fn id(&self) -> u64 {
        self.id
    }
    pub fn member(&self) -> usize {
        self.binding.member
    }
    pub fn source(&self) -> &NormalWaveFamily<'c> {
        &self.binding.source
    }
    pub fn relation(&self) -> &ResidentWaveRelation<'c> {
        &self.binding.relation
    }
}
/// Refusal of an attachment: the wave and the neighborhood are returned.
pub type NormalCoupledAttachRefusal<'c> =
    NormalRefusal<(ResidentNormalWave<'c>, ResidentGeneratorNeighborhood<'c>)>;
/// [definition] **The one passage receipt of the coupled continuation** (plan phase 9): every
/// published coupled motion — a contact advance, a received next current, a source contact, a
/// whole source field actuated in order, a received point source that develops the member —
/// returns this receipt. It names the contact and the predecessor/successor families and, by
/// kind, the operands: the neighborhood development of a received source, and the original
/// source field with the internal source predictions of a field actuation. The former
/// `NormalCoupledReception` and `NormalCoupledSourceActuation` are this type.
pub struct NormalCoupledStep<'a, 'c> {
    pub predecessor_epoch: u64,
    pub successor_epoch: u64,
    pub contact: NormalCoupledContact<'c>,
    successor: Rc<NormalWaveFamily<'c>>,
    /// A received point source: the neighborhood development it published.
    pub neighborhood: Option<GeneratorNeighborhoodStep<'a, 'c>>,
    source: Option<ResidentSourcePairs<'a, 'c>>,
    predictions: Vec<Rc<crate::native_ecology::constitutive_fibre::ResidentConstitutiveReturn<'c>>>,
}
impl<'a, 'c> NormalCoupledStep<'a, 'c> {
    pub fn applied_relation(&self) -> &ResidentWaveRelation<'c> {
        self.successor
            .last_relation()
            .expect("completed wave passage")
    }
    /// The family the contact was admitted at (the predecessor).
    pub fn source(&self) -> &NormalWaveFamily<'c> {
        self.contact.source()
    }
    pub fn predecessor(&self) -> &NormalWaveFamily<'c> {
        self.contact.source()
    }
    pub fn successor(&self) -> &NormalWaveFamily<'c> {
        &self.successor
    }
    pub fn member(&self) -> usize {
        self.contact.member()
    }
    /// A field actuation: the original source field, borrowed.
    pub fn source_pairs(&self) -> Option<&ResidentSourcePairs<'a, 'c>> {
        self.source.as_ref()
    }
    /// A source actuation: the producing law's source predictions, in field order (one for a
    /// point source). They are this step's readings; the source maps do not retain them.
    pub fn predictions(
        &self,
    ) -> impl Iterator<Item = &crate::native_ecology::constitutive_fibre::ResidentConstitutiveReturn<'c>>
    {
        self.predictions.iter().map(Rc::as_ref)
    }
    /// A field actuation: the last internal source reaction; the complete image is successor().
    pub fn last_source_contact(
        &self,
    ) -> Option<&crate::native_ecology::constitutive_fibre::ResidentWaveSourceContact<'c>> {
        self.successor.last_relation().and_then(|v| v.source_contact())
    }
}

/// Read each actual member/receiver cut once for this prospective word. Repeated use shares
/// immutable derived maps; it does not clone a continuing ecology or store observed events.
pub(super) fn prospective_maps<'c>(
    word: &[(usize, WaveSourceReceiver)],
    mut read: impl FnMut(
        usize,
        WaveSourceReceiver,
    ) -> Result<ResidentWaveRelation<'c>, ConstitutiveFibreError>,
) -> Result<Vec<Rc<ResidentWaveRelation<'c>>>, ConstitutiveFibreError> {
    if word.is_empty() {
        return Err(ConstitutiveFibreError::Shape);
    }
    let mut retained: BTreeMap<(usize, bool), Rc<ResidentWaveRelation<'c>>> = BTreeMap::new();
    word.iter()
        .map(|&(member, chart)| {
            let key = (member, matches!(chart, WaveSourceReceiver::UnitRealSum));
            if let Some(map) = retained.get(&key) {
                return Ok(Rc::clone(map));
            }
            let map = Rc::new(read(member, chart)?);
            retained.insert(key, Rc::clone(&map));
            Ok(map)
        })
        .collect()
}

impl<'c> ResidentNormalWave<'c> {
    pub fn with_neighborhood(
        self,
        neighborhood: ResidentGeneratorNeighborhood<'c>,
    ) -> Result<ResidentNormalWave<'c, NormalWaveCoupled<'c>>, NormalCoupledAttachRefusal<'c>> {
        let checked = (|| {
            for j in 0..neighborhood.members() {
                let law = neighborhood.generator(j)?;
                if !std::ptr::eq(law.surface, self.material.surface)
                    || law.target_width != 2 * self.material.roots()
                    || !matches!(law.source_chart,ConstitutiveSourceChart::BilinearContact{source_complex,..} if source_complex==3*self.material.roots())
                {
                    return Err(ConstitutiveFibreError::Shape);
                }
            }
            self.read_family()
        })();
        match checked {
            Err(reason) => Err(NormalRefusal::new((self, neighborhood), reason)),
            Ok(current) => {
                let mode = NormalWaveCoupled {
                    epoch: self.epoch,
                    neighborhood_base: neighborhood.epoch(),
                    current_neighborhood_epoch: neighborhood.epoch(),
                    neighborhood,
                    current: Rc::new(current),
                    next_contact: 1,
                    active_member: None,
                    bindings: BTreeMap::new(),
                    pending: BTreeMap::new(),
                };
                Ok(self.with_continuation(mode))
            }
        }
    }
}
impl<'c> ResidentNormalWave<'c, NormalWaveCoupled<'c>> {
    /// Receive an actual condition without advancing the held wave. Later contacts, comparisons
    /// and returns read the new condition; pending predictions keep only their source operands.
    pub fn receive_condition(
        &mut self,
        incoming: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<(), ConstitutiveFibreError> {
        let next = self
            .continuation
            .neighborhood_base
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        self.continuation.neighborhood.receive_condition(incoming)?;
        self.continuation.neighborhood_base = next;
        self.continuation.bindings.clear();
        Ok(())
    }
    pub fn epoch(&self) -> u64 {
        self.continuation.epoch
    }
    pub fn current(&self) -> &NormalWaveFamily<'c> {
        &self.continuation.current
    }
    pub(super) fn current_shared(&self) -> Rc<NormalWaveFamily<'c>> {
        Rc::clone(&self.continuation.current)
    }
    pub fn neighborhood(&self) -> &ResidentGeneratorNeighborhood<'c> {
        &self.continuation.neighborhood
    }
    pub fn normal_material(&self) -> &ResidentNormalMaterial<'c> {
        &self.material
    }
    /// An older normal prediction of the bank returns by the one-cut pullback at the bank's
    /// contemporary constitution. It does not deposit into the local conditional law or change
    /// the current family.
    pub fn pullback<'a>(
        &mut self,
        id: u64,
        observed: ResidentConstitutiveCurrent<'a, 'c>,
    ) -> Result<NormalWavePassage<'a, 'c>, ConstitutiveFibreError> {
        self.neighborhood().require_usable()?;
        self.pull_back_pending(id, observed)
    }
    /// Native projected action; the face retains this complete source family.
    pub fn read_basis_face(
        &self,
        chart: &NormalWaveBasisChart<'c>,
    ) -> Result<NormalFamilyBasisFace<'c>, ConstitutiveFibreError> {
        chart.read_family(Rc::clone(&self.continuation.current), self.epoch())
    }
    pub fn normal_source_epoch(&self) -> u64 {
        self.epoch
    }
    /// Prospective compound conduct through the current learned members and condition.
    /// No actual contact, epoch, current, pending handle or material is published here.
    pub fn read_prospective_word(
        &self,
        word: &[(usize, WaveSourceReceiver)],
    ) -> Result<NormalWaveFamilyReceiver<'_, 'c>, ConstitutiveFibreError> {
        self.current().check_prospective_shape(word.len())?;
        let maps = prospective_maps(word, |member, chart| {
            self.neighborhood().read_wave_relation_in_chart(
                member,
                self.normal_material().roots(),
                chart,
                None,
            )
        })?;
        self.current().read_prospective(maps)
    }
    /// The unpublished passage of the contemporary family through one member law at the
    /// contemporary cut. No contact is admitted and nothing is published.
    pub fn read_member_passage(
        &self,
        member: usize,
        chart: WaveSourceReceiver,
    ) -> Result<NormalWaveFamily<'c>, ConstitutiveFibreError> {
        let relation = self.neighborhood().read_wave_relation_in_chart(
            member,
            self.material.roots(),
            chart,
            None,
        )?;
        self.current().read_through(Rc::new(relation))
    }
    /// Admission is a declared interaction, not automatic contact between every co-present law.
    pub fn admit_contact(
        &mut self,
        member: usize,
    ) -> Result<NormalCoupledContact<'c>, ConstitutiveFibreError> {
        self.admit_contact_in_chart(member, WaveSourceReceiver::Direct)
    }
    /// Read the local law in its declared source chart, retaining the raw residual state.
    pub fn admit_contact_in_chart(
        &mut self,
        member: usize,
        receiver: WaveSourceReceiver,
    ) -> Result<NormalCoupledContact<'c>, ConstitutiveFibreError> {
        let mode = &mut self.continuation;
        let id = mode.next_contact;
        let next = id.checked_add(1).ok_or(ConstitutiveFibreError::Shape)?;
        let relation = mode.neighborhood.read_wave_relation_in_chart(
            member,
            self.material.roots(),
            receiver,
            None,
        )?;
        let binding = Rc::new(CoupledBinding {
            member,
            epoch: mode.epoch,
            neighborhood_epoch: mode.neighborhood.epoch(),
            source: Rc::clone(&mode.current),
            relation: Rc::new(relation),
        });
        mode.bindings.insert(id, Rc::clone(&binding));
        mode.next_contact = next;
        Ok(NormalCoupledContact {
            owner: Rc::clone(&self.owner),
            id,
            binding,
        })
    }
    /// Admit one contact for one motion. A refused motion withdraws the admission, so the
    /// owner (including its rest) is unchanged by the refusal.
    pub(super) fn with_admitted<R>(
        &mut self,
        member: usize,
        chart: WaveSourceReceiver,
        act: impl FnOnce(&mut Self, &NormalCoupledContact<'c>) -> Result<R, ConstitutiveFibreError>,
    ) -> Result<R, ConstitutiveFibreError> {
        let next_contact = self.continuation.next_contact;
        let contact = self.admit_contact_in_chart(member, chart)?;
        match act(self, &contact) {
            Ok(value) => Ok(value),
            Err(error) => {
                self.continuation.bindings.remove(&contact.id);
                self.continuation.next_contact = next_contact;
                Err(error)
            }
        }
    }
    pub fn contact(&self, id: u64) -> Result<NormalCoupledContact<'c>, ConstitutiveFibreError> {
        let binding = self
            .continuation
            .bindings
            .get(&id)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        Ok(NormalCoupledContact {
            owner: Rc::clone(&self.owner),
            id,
            binding: Rc::clone(binding),
        })
    }
    pub fn contact_ids(&self) -> impl Iterator<Item = u64> + '_ {
        self.continuation.bindings.keys().copied()
    }
    pub fn pending_contacts(&self) -> usize {
        self.continuation.bindings.len()
    }
    fn check_contact(
        &self,
        contact: &NormalCoupledContact<'c>,
    ) -> Result<(), ConstitutiveFibreError> {
        let mode = &self.continuation;
        if !Rc::ptr_eq(&contact.owner, &self.owner)
            || contact.binding.epoch != mode.epoch
            || contact.binding.neighborhood_epoch != mode.neighborhood.epoch()
            || !Rc::ptr_eq(&contact.binding.source, &mode.current)
            || !mode
                .bindings
                .get(&contact.id)
                .is_some_and(|b| Rc::ptr_eq(b, &contact.binding))
        {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        Ok(())
    }
    pub fn release_contact(
        &mut self,
        contact: &NormalCoupledContact<'c>,
    ) -> Result<(), ConstitutiveFibreError> {
        self.check_contact(contact)?;
        self.continuation.bindings.remove(&contact.id);
        Ok(())
    }
    /// Inspect the proposed complete family, including an unsupported source domain, without
    /// publishing it. No selected point enters this operation.
    pub fn read_contact(
        &self,
        contact: &NormalCoupledContact<'c>,
    ) -> Result<NormalWaveFamily<'c>, ConstitutiveFibreError> {
        self.check_contact(contact)?;
        self.current()
            .read_through(Rc::clone(&contact.binding.relation))
    }
    /// The actual offered source meets its whole learned arrival family by unit-admittance
    /// contact. That reaction founds a passive union acting on this complete held family.
    /// This is source actuation, not an observation deposited into either learned body.
    pub fn read_source_contact(
        &self,
        contact: &NormalCoupledContact<'c>,
        source: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<NormalWaveFamily<'c>, ConstitutiveFibreError> {
        Ok(self.read_source_passage(contact, source)?.0)
    }
    /// The source passage with the producing law's prediction at the relation's cut (a reading
    /// of this passage, not retained on its map).
    fn read_source_passage(
        &self,
        contact: &NormalCoupledContact<'c>,
        source: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<
        (
            NormalWaveFamily<'c>,
            crate::native_ecology::constitutive_fibre::ResidentConstitutiveReturn<'c>,
        ),
        ConstitutiveFibreError,
    > {
        self.check_contact(contact)?;
        let passage = contact
            .binding
            .relation
            .read_source_passage(self.neighborhood().action(contact.member())?, source)?;
        Ok((
            contact.binding.source.read_through(Rc::new(passage.relation))?,
            passage.prediction,
        ))
    }
    pub fn actuate_contact_source<'a>(
        &mut self,
        contact: &NormalCoupledContact<'c>,
        source: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<NormalCoupledStep<'a, 'c>, ConstitutiveFibreError> {
        self.check_contact(contact)?;
        let next = self
            .epoch()
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        if !self
            .neighborhood()
            .can_publish_wave_read(contact.binding.neighborhood_epoch)
        {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let (successor, prediction) = self.read_source_passage(contact, source)?;
        let successor = Rc::new(successor);
        // The checked source graph is total and copies the anchor. The current family is
        // already admitted, so its image retains support without a new nearest-point solve.
        self.continuation
            .neighborhood
            .publish_wave_read(contact.binding.neighborhood_epoch);
        let mut step = self.publish_coupled(contact, next, successor);
        step.predictions = vec![Rc::new(prediction)];
        Ok(step)
    }
    /// Stage the complete supplied field in order, then publish one source occurrence. Local
    /// learned material/condition are read at the admitted cut throughout this unpaired input.
    pub fn actuate_contact_section<'a>(
        &mut self,
        contact: &NormalCoupledContact<'c>,
        source: ResidentConstitutiveSection<'a, 'c>,
    ) -> Result<NormalCoupledStep<'a, 'c>, ConstitutiveFibreError> {
        self.actuate_contact_section_with_progress(contact, source, |_| {})
    }
    /// The callback reports completed internal source factors. It cannot observe or choose a
    /// numerical state, and publication still occurs only after the entire field succeeds.
    pub fn actuate_contact_section_with_progress<'a>(
        &mut self,
        contact: &NormalCoupledContact<'c>,
        source: ResidentConstitutiveSection<'a, 'c>,
        mut progress: impl FnMut(usize),
    ) -> Result<NormalCoupledStep<'a, 'c>, ConstitutiveFibreError> {
        self.check_contact(contact)?;
        if source.components() != 2 * self.material.roots() {
            return Err(ConstitutiveFibreError::Shape);
        }
        let next = self
            .epoch()
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        if !self
            .neighborhood()
            .can_publish_wave_read(contact.binding.neighborhood_epoch)
        {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let pairs = source.source_pairs(self.material.surface)?;
        let passage = contact
            .binding
            .source
            .passages()
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let mut successor = Rc::clone(&contact.binding.source);
        let mut predictions = Vec::new();
        for row in 0..pairs.source().rows() {
            let (next, prediction) = (|| {
                let passage_readings = contact.binding.relation.read_source_passage(
                    self.neighborhood().action(contact.member())?,
                    pairs.source().row(row)?,
                )?;
                let map = passage_readings.relation.with_source_row(row);
                let mut prediction = passage_readings.prediction;
                prediction.qualify_field_source(row);
                let prediction = Rc::new(prediction);
                Ok::<_, ConstitutiveFibreError>((
                    successor.read_through_at(Rc::new(map), passage)?,
                    prediction,
                ))
            })()
            .map_err(|source| ConstitutiveFibreError::SourcePassage {
                row,
                source: Box::new(source),
            })?;
            successor = Rc::new(next);
            predictions.push(prediction);
            progress(row + 1);
        }
        self.continuation
            .neighborhood
            .publish_wave_read(contact.binding.neighborhood_epoch);
        let mut step = self.publish_coupled(contact, next, successor);
        step.source = Some(pairs);
        step.predictions = predictions;
        Ok(step)
    }
    /// Join an actual next-current observation with the entire preceding c family.
    /// This is the declared (p,c)->(c,v) receiver, distinct from a delayed material correction.
    /// Both original source and observation remain on the return; no source member is selected
    /// and neither local nor normal material is deposited by this current-only passage.
    pub fn receive_contact_next<'a>(
        &mut self,
        contact: &NormalCoupledContact<'c>,
        observed: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<NormalCoupledStep<'a, 'c>, ConstitutiveFibreError> {
        self.check_contact(contact)?;
        let next = self
            .epoch()
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        if !self
            .neighborhood()
            .can_publish_wave_read(contact.binding.neighborhood_epoch)
        {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let relation = contact.binding.relation.read_observed_next(observed)?;
        let successor = Rc::new(contact.binding.source.read_through(Rc::new(relation))?);
        // This checked total map preserves the admitted anchor domain of the predecessor.
        self.continuation
            .neighborhood
            .publish_wave_read(contact.binding.neighborhood_epoch);
        Ok(self.publish_coupled(contact, next, successor))
    }
    pub fn advance_contact<'a>(
        &mut self,
        contact: &NormalCoupledContact<'c>,
    ) -> Result<NormalCoupledStep<'a, 'c>, ConstitutiveFibreError> {
        self.check_contact(contact)?;
        let next = self
            .epoch()
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        if !self
            .neighborhood()
            .can_publish_wave_read(contact.binding.neighborhood_epoch)
        {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let successor = Rc::new(self.read_contact(contact)?);
        successor.read_receiver()?.require_supported()?;
        self.continuation
            .neighborhood
            .publish_wave_read(contact.binding.neighborhood_epoch);
        Ok(self.publish_coupled(contact, next, successor))
    }
    /// An actual external point occurrence in the declared source plane develops its local law
    /// and condition, then acts on this continuing family. These supplied comparands are not a
    /// receiver-selected centre or an assertion that the latent family has one member.
    pub fn receive_contact_source<'i>(
        &mut self,
        contact: &NormalCoupledContact<'c>,
        source: ResidentConstitutiveCurrent<'i, 'c>,
        observed_difference: ResidentConstitutiveCurrent<'i, 'c>,
    ) -> Result<NormalCoupledStep<'i, 'c>, ConstitutiveFibreError> {
        self.check_contact(contact)?;
        let next = self
            .epoch()
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let s = self.material.surface;
        let out = s.fresh_section(1, 1, ResidentGrain(0))?;
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_normal_source_plane(
                &lane,
                source,
                self.material.roots(),
                contact.binding.relation.source_receiver(),
                &out,
            )?;
        }
        passage.close(0, &out, 64)?;
        let received = passage.finish()?.launch()?;
        if !received.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "observed source plane: {:?}",
                received.obstruction
            )));
        }
        self.develop_contact_source(contact, next, source, observed_difference)
    }
    /// Develop a point source pair at the contemporary material and condition cut.
    fn develop_contact_source<'i>(
        &mut self,
        contact: &NormalCoupledContact<'c>,
        next: u64,
        source: ResidentConstitutiveCurrent<'i, 'c>,
        observed_difference: ResidentConstitutiveCurrent<'i, 'c>,
    ) -> Result<NormalCoupledStep<'i, 'c>, ConstitutiveFibreError> {
        let prepared = self.continuation.neighborhood.prepare_consequence(
            contact.member(),
            source,
            Some(observed_difference),
        )?;
        let relation = self.neighborhood().read_wave_relation_in_chart(
            contact.member(),
            self.material.roots(),
            contact.binding.relation.source_receiver(),
            Some(&prepared),
        )?;
        let successor = Rc::new(self.current().read_through(Rc::new(relation))?);
        successor.read_receiver()?.require_supported()?;
        if !self.neighborhood().can_commit_consequence(&prepared) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let neighborhood = self.continuation.neighborhood.publish_consequence(
            prepared,
            source,
            Some(observed_difference),
        );
        let mut step = self.publish_coupled(contact, next, successor);
        step.neighborhood = Some(neighborhood);
        Ok(step)
    }
    fn publish_coupled<'a>(
        &mut self,
        contact: &NormalCoupledContact<'c>,
        next: u64,
        successor: Rc<NormalWaveFamily<'c>>,
    ) -> NormalCoupledStep<'a, 'c> {
        let predecessor_epoch = self.continuation.epoch;
        self.continuation.epoch = next;
        self.continuation.active_member = Some(contact.member());
        self.continuation.current = Rc::clone(&successor);
        self.continuation.current_neighborhood_epoch = self.continuation.neighborhood.epoch();
        // Admissions name one source occurrence. External receipts retain their old source,
        // but no admission can silently act again at a different continuation.
        self.continuation.bindings.clear();
        NormalCoupledStep {
            predecessor_epoch,
            successor_epoch: next,
            successor,
            contact: NormalCoupledContact {
                owner: Rc::clone(&self.owner),
                id: contact.id,
                binding: Rc::clone(&contact.binding),
            },
            neighborhood: None,
            source: None,
            predictions: Vec::new(),
        }
    }
}
#[cfg(test)]
mod tests;

#[cfg(test)]
mod return_tests;
