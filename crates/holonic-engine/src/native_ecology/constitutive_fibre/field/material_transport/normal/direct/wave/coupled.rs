use super::*;
pub(super) mod rest;
mod comparison;
mod continuation;
mod dependent;
mod observation;
pub use observation::NormalCoupledObservation;
pub use dependent::{ConstitutiveComparisonSection, ConstitutiveSourceFrame, ResidentCoupledConstitutive, CoupledConstitutiveRefusal, ConstitutiveSourceRefusal, CoupledConstitutiveRest};
pub use continuation::{NormalCoupledContinuation, NormalContinuationPullback, NormalContinuationJoin};
use comparison::CoupledProducingCut;
pub use comparison::{CoupledConstitutiveFamily, CoupledConstitutiveAlternative, CompiledCoupledJoint, CoupledJointEvaluation, NormalCoupledComparison};
use crate::native_ecology::constitutive_fibre::{
    GeneratorNeighborhoodStep, ResidentGeneratorNeighborhood, ResidentSourcePairs,
    ResidentWaveRelation, WaveSourceReceiver,
};

/// The same wave owner continuing through a conditional family. Its fixed normal bank remains
/// available for its old comparisons; it is not advanced as a hidden alternative current.
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
    pending: BTreeMap<u64,Rc<CoupledProducingCut<'c>>>,
    // One shared ordered word, rooted at the oldest still-pending producing source.
    transport: BTreeMap<u64, Vec<Rc<ResidentWaveRelation<'c>>>>,
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
    /// A field actuation: the internal source predictions, in field order.
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
                    transport: BTreeMap::new(),
                };
                Ok(self.with_continuation(mode))
            }
        }
    }
}
impl<'c> ResidentNormalWave<'c, NormalWaveCoupled<'c>> {
    /// Receive an actual condition without advancing the held wave. Its original
    /// map remains retained, and later contact reads the new condition.
    pub fn receive_condition(&mut self,incoming:ResidentConstitutiveCurrent<'_, 'c>)
        ->Result<(),ConstitutiveFibreError>{
        let next=self.continuation.neighborhood_base.checked_add(1).ok_or(ConstitutiveFibreError::Shape)?;
        self.continuation.neighborhood.receive_condition(incoming)?;
        self.continuation.neighborhood_base=next;self.continuation.bindings.clear();Ok(())
    }
    pub fn epoch(&self) -> u64 {
        self.continuation.epoch
    }
    pub fn current(&self) -> &NormalWaveFamily<'c> {
        &self.continuation.current
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
    pub fn read_basis_face(&self,chart:&NormalWaveBasisChart<'c>)->Result<NormalFamilyBasisFace<'c>,ConstitutiveFibreError>{
        chart.read_family(Rc::clone(&self.continuation.current),self.epoch())
    }
    pub fn normal_source_epoch(&self) -> u64 {
        self.epoch
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
        self.check_contact(contact)?;
        let map = contact
            .binding
            .relation
            .read_source_contact(self.neighborhood().action(contact.member())?, source)?;
        contact.binding.source.read_through(Rc::new(map))
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
        let successor = Rc::new(self.read_source_contact(contact, source)?);
        // The checked source graph is total and copies the anchor. The current family is
        // already admitted, so its image retains support without a new nearest-point solve.
        self.continuation
            .neighborhood
            .publish_wave_read(contact.binding.neighborhood_epoch);
        Ok(self.publish_coupled(contact, next, successor))
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
        let mut factors = Vec::new();
        let retain_factors = !self.continuation.pending.is_empty();
        for row in 0..pairs.source().rows() {
            let (next, prediction, map) = (|| {
                let map = contact
                    .binding
                    .relation
                    .read_source_contact(
                        self.neighborhood().action(contact.member())?,
                        pairs.source().row(row)?,
                    )?
                    .with_source_row(row);
                let prediction = map
                    .source_contact()
                    .expect("source map")
                    .retained_prediction();
                let map = Rc::new(map);
                Ok::<_, ConstitutiveFibreError>((
                    successor.read_through_at(Rc::clone(&map), passage)?,
                    prediction,
                    map,
                ))
            })()
            .map_err(|source| ConstitutiveFibreError::SourcePassage {
                row,
                source: Box::new(source),
            })?;
            successor = Rc::new(next);
            predictions.push(prediction);
            if retain_factors { factors.push(map); }
            progress(row + 1);
        }
        self.continuation
            .neighborhood
            .publish_wave_read(contact.binding.neighborhood_epoch);
        let mut step = self.publish_coupled_factors(contact, next, successor, factors);
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
        let next = self.epoch().checked_add(1).ok_or(ConstitutiveFibreError::Shape)?;
        if !self.neighborhood().can_publish_wave_read(contact.binding.neighborhood_epoch) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let relation = contact.binding.relation.read_observed_next(observed)?;
        let successor = Rc::new(contact.binding.source.read_through(Rc::new(relation))?);
        // This checked total map preserves the admitted anchor domain of the predecessor.
        self.continuation.neighborhood.publish_wave_read(contact.binding.neighborhood_epoch);
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
        let prepared = self.continuation.neighborhood.prepare_advance(
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
        if !self.neighborhood().can_commit_advance(&prepared) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let neighborhood = self.continuation.neighborhood.publish_advance(prepared);
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
        let factors = vec![successor.last_relation_shared().expect("completed coupled passage")];
        self.publish_coupled_factors(contact, next, successor, factors)
    }
    fn publish_coupled_factors<'a>(
        &mut self,
        contact: &NormalCoupledContact<'c>,
        next: u64,
        successor: Rc<NormalWaveFamily<'c>>,
        factors: Vec<Rc<ResidentWaveRelation<'c>>>,
    ) -> NormalCoupledStep<'a, 'c> {
        let predecessor_epoch = self.continuation.epoch;
        if !self.continuation.pending.is_empty() {
            self.continuation.transport.insert(next, factors);
        }
        self.continuation.epoch = next;
        self.continuation.active_member = Some(contact.member());
        self.continuation.current = Rc::clone(&successor);
        self.continuation.current_neighborhood_epoch=self.continuation.neighborhood.epoch();
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
mod continuation_tests;
