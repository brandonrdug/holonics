//! One continuing field shared explicitly by local conditional generators. Relevance follows
//! their actual learned dependence on that field; co-membership does not add a coefficient.
//! No source codec, input history, token lookup or alternative learning law lives here.
use super::*;
use std::rc::Rc;
use crate::native_ecology::constitutive_fibre::{NormalRefusal, ResidentNormalMaterial};

pub mod field_reaction;
mod rest;
pub use rest::{GeneratorNeighborhoodRest, NeighborhoodEvidenceRest};

pub struct ResidentGeneratorNeighborhood<'c> {
    laws: Vec<GeneratorMaterial<'c>>,
    condition: ResidentConditionCurrent<'c>,
    epoch: u64,
    evidence: Option<NeighborhoodEvidence<'c>>,
    owner: Rc<()>,
    usable: bool,
}

/// Compatibility and empirical prediction are two readings of one local material owner.
/// The normal action is derived from the retained moments, never supplied as a target router.
pub(crate) struct GeneratorMaterial<'c> {
    pub(crate) law: ResidentConstitutiveFibre<'c>,
    pub(crate) predictive: Option<PredictiveMaterial<'c>>,
}
pub(crate) struct PredictiveMaterial<'c> {
    pub(crate) material: ResidentNormalMaterial<'c>,
    pub(crate) action: ResidentConstitutiveFibre<'c>,
}
impl<'c> PredictiveMaterial<'c> {
    pub(crate) fn stage_enclosed(&self,source:ResidentNormalEnclosureView<'_, 'c>,
        producing_condition:ResidentConstitutiveCurrent<'_, 'c>,observed:ResidentNormalEnclosureView<'_, 'c>)
        ->Result<Self,ConstitutiveFibreError>{
        let next=match self.material.source_chart(){
            NormalSourceChart::Wave{..}=>self.material.stage_source_observation(source,observed)?,
            NormalSourceChart::Features{..}=>{
                let features=source.bilinear_features(producing_condition)?;
                self.material.stage_source_observation(features.view(),observed)?
            },
        };
        Self::new(next,&self.action)
    }
    fn action_for(material: &ResidentNormalMaterial<'c>, law: &ResidentConstitutiveFibre<'c>)
        -> Result<ResidentConstitutiveFibre<'c>, ConstitutiveFibreError> {
        let ConstitutiveSourceChart::BilinearContact {source_complex, condition_complex} = law.source_chart
            else { return Err(ConstitutiveFibreError::Shape); };
        if 2 * material.targets() != law.target_width { return Err(ConstitutiveFibreError::Shape); }
        let action = material.read_applied_bilinear_relation(source_complex, condition_complex)?;
        if !std::ptr::eq(action.surface, law.surface) { return Err(ConstitutiveFibreError::Shape); }
        Ok(action)
    }
    pub(crate) fn new(material: ResidentNormalMaterial<'c>, law: &ResidentConstitutiveFibre<'c>)
        -> Result<Self, ConstitutiveFibreError> {
        let action = Self::action_for(&material, law)?;
        Ok(Self {material, action})
    }
    fn stage(&self, source: ResidentConstitutiveCurrent<'_, 'c>,
        prior_condition: ResidentConstitutiveCurrent<'_, 'c>, observed: ResidentConstitutiveCurrent<'_, 'c>)
        -> Result<Self, ConstitutiveFibreError> {
        let next=match self.material.source_chart() {
            NormalSourceChart::Features {..}=>self.material.stage_bilinear_observation(source, prior_condition, observed)?,
            NormalSourceChart::Wave {..}=>self.material.stage_source_observation(source,observed)?,
        };
        Self::new(next, &self.action)
    }
}
impl<'c> GeneratorMaterial<'c> {
    pub(crate) fn action(&self) -> &ResidentConstitutiveFibre<'c> {
        self.predictive.as_ref().map_or(&self.law, |v| &v.action)
    }
    fn stage_prediction(&self, source: ResidentConstitutiveCurrent<'_, 'c>,
        prior_condition: ResidentConstitutiveCurrent<'_, 'c>, observed: ResidentConstitutiveCurrent<'_, 'c>)
        -> Result<Option<PredictiveMaterial<'c>>, ConstitutiveFibreError> {
        self.predictive.as_ref().map(|v| v.stage(source, prior_condition, observed)).transpose()
    }
}

/// The latest received fibre at its producing local-law cut. It is not a cumulative
/// world-belief assertion or an archive; a later observation replaces this single entry.
pub struct NeighborhoodEvidence<'c> {
    pub member: usize,
    pub epoch: u64,
    pub family: ResidentConditionPreimage<'c>,
}

/// The actual source and observation remain borrowed during inspection of this complete
/// passage. Its prediction is a receiver family, not a selected response or an inferred cause.
pub struct GeneratorNeighborhoodStep<'input, 'c> {
    owner: Rc<()>,
    pub member: usize,
    pub predecessor_epoch: u64,
    pub successor_epoch: u64,
    pub prediction: ResidentConstitutiveReturn<'c>,
    pub prior_condition: ResidentConditionCurrent<'c>,
    pub contact: Option<ResidentConditionContact<'c>>,
    pub formation: Option<ResidentConstitutiveReturn<'c>>,
    source: ResidentConstitutiveCurrent<'input, 'c>,
    observed: Option<ResidentConstitutiveCurrent<'input, 'c>>,
}

/// Source-independent storage for the consequence of a specified pair of operands, held before
/// publication (the wave coordinator can retain it while preparing its own successor; dropping
/// it leaves both live predecessors). The publishing call supplies the same operands (phase 11
/// merged the former `PreparedNeighborhoodAdvance`, which only borrowed them beside this). A
/// dependent family evaluator owns its operand sections separately and retains their common
/// parameter; it must not publish one evaluated alternative as the actual neighborhood successor.
pub(crate) struct PreparedNeighborhoodConsequence<'c> {
    owner: Rc<()>,
    member: usize,
    predecessor_epoch: u64,
    successor_epoch: u64,
    prediction: ResidentConstitutiveReturn<'c>,
    prior_condition: ResidentConditionCurrent<'c>,
    condition: Option<PreparedConditionContact<'c>>,
    formation: Option<PreparedConstitutiveFormation<'c>>,
    predictive: Option<PredictiveMaterial<'c>>,
}
/// Where a consequence's prediction and formation read the condition.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ConsequenceCondition {
    /// The prediction reads the contemporary standing; the formation reads the contact successor.
    Contemporary,
    /// Both read the supplied producing condition (an actual source operand of the passage).
    Producing,
}
pub(crate) struct ResidentNeighborhoodAlternative<'c> {
    pub(crate) prediction:ResidentConstitutiveReturn<'c>,
    pub(crate) condition:PreparedConditionContact<'c>,
    pub(crate) formation:ResidentConstitutiveReturn<'c>,
    pub(crate) material:GeneratorMaterial<'c>,
}
impl<'c> ResidentNeighborhoodAlternative<'c> {
    /// The next source-conditional return uses the material and condition produced by the
    /// previous one. The supplied law is the actual affected conditional member, not a row
    /// witness or an independently sampled alternative.
    pub(crate) fn prepare_following(
        material:&mut GeneratorMaterial<'c>,
        prior:&ResidentConditionCurrent<'c>,
        source:ResidentConstitutiveCurrent<'_, 'c>,
        observed:ResidentConstitutiveCurrent<'_, 'c>,
        producing_condition:ResidentConstitutiveCurrent<'_, 'c>,
        predictive_override:Option<&PredictiveMaterial<'c>>,
    )->Result<Self,ConstitutiveFibreError>{
        let predictive_source=predictive_override.or(material.predictive.as_ref());
        let action=predictive_source.map_or(&material.law,|p|&p.action);
        let prediction=action.read_bilinear(source,prior.current())?;
        let predictive=predictive_source.map(|p|p.stage(source,producing_condition,observed)).transpose()?;
        let family=material.law.read_condition_preimage(source,observed)?;
        let condition=prior.prepare_contact(&family)?;
        let staged=material.law.prepare_bilinear_contact(source,condition.successor(),Some(observed))?;
        let (law,formation)=staged.into_alternative();
        let material=GeneratorMaterial {law,predictive};
        Ok(Self {prediction,condition,formation,material})
    }
}
impl<'c> PreparedNeighborhoodConsequence<'c> {
    pub(crate) fn into_alternative(self)->Result<ResidentNeighborhoodAlternative<'c>,ConstitutiveFibreError>{
        let condition=self.condition.ok_or(ConstitutiveFibreError::Shape)?;
        let (law,formation)=self.formation.ok_or(ConstitutiveFibreError::Shape)?.into_alternative();
        let material=GeneratorMaterial {law,predictive:self.predictive};
        Ok(ResidentNeighborhoodAlternative {prediction:self.prediction,condition,formation,material})
    }
}
impl<'input, 'c> GeneratorNeighborhoodStep<'input, 'c> {
    pub fn source(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        self.source
    }
    pub fn observed(&self) -> Option<ResidentConstitutiveCurrent<'_, 'c>> {
        self.observed
    }
    pub fn belongs_to(&self, body: &ResidentGeneratorNeighborhood<'c>) -> bool {
        Rc::ptr_eq(&self.owner, &body.owner)
    }
}

impl<'c> ResidentGeneratorNeighborhood<'c> {
    /// The caller declares a common condition chart for these already-founded generators.
    /// This binds actual shared standing; it does not infer a connection from equal output.
    pub fn with_shared_condition(
        laws: Vec<ResidentConstitutiveFibre<'c>>,
        initial: ResidentConstitutiveCurrent<'_, 'c>,
        metric: ConditionContactMetric,
    ) -> Result<Self, ConstitutiveFibreError> {
        let first = laws.first().ok_or(ConstitutiveFibreError::Shape)?;
        if !matches!(
            first.source_chart,
            ConstitutiveSourceChart::BilinearContact { .. }
        ) || laws.iter().any(|law| {
            !law.usable
                || law.source_chart != first.source_chart
                || !std::ptr::eq(law.surface, first.surface)
        }) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let condition = first.retain_condition_current(initial, metric)?;
        Ok(Self {
            laws: laws.into_iter().map(|law| GeneratorMaterial {law,predictive:None}).collect(),
            condition,
            epoch: 0,
            evidence: None,
            owner: Rc::new(()),
            usable: true,
        })
    }
    pub(crate) fn require_usable(&self) -> Result<(), ConstitutiveFibreError> {
        if self.usable {
            Ok(())
        } else {
            Err(ConstitutiveFibreError::Uncertain)
        }
    }
    pub fn members(&self) -> usize {
        self.laws.len()
    }
    pub fn epoch(&self) -> u64 {
        self.epoch
    }
    pub fn last_received_evidence(&self) -> Option<&NeighborhoodEvidence<'c>> {
        self.evidence.as_ref()
    }
    pub fn condition(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        self.condition.current()
    }
    /// An actual supplied condition in this neighborhood's declared chart.
    /// Pending producers retain their former condition; only later reads use this input.
    pub fn receive_condition(&mut self,incoming:ResidentConstitutiveCurrent<'_, 'c>)
        ->Result<ResidentConditionCurrent<'c>,ConstitutiveFibreError>{
        self.require_usable()?;
        let next=self.epoch.checked_add(1).ok_or(ConstitutiveFibreError::Shape)?;
        let prior=self.condition.receive_current(incoming)?;self.epoch=next;Ok(prior)
    }
    pub(crate) fn material_for_staging(
        &mut self, member:usize,
    )->Result<&mut GeneratorMaterial<'c>,ConstitutiveFibreError>{
        self.require_usable()?;
        self.laws.get_mut(member).ok_or(ConstitutiveFibreError::Shape)
    }
    /// Compatibility law used for condition contact and relation formation. Predictions use
    /// the attached normal action when present; `predictive_material` exposes that material.
    pub fn generator(
        &self,
        member: usize,
    ) -> Result<&ResidentConstitutiveFibre<'c>, ConstitutiveFibreError> {
        if !self.usable {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        Ok(&self.material(member)?.law)
    }
    pub(crate) fn material(&self, member: usize) -> Result<&GeneratorMaterial<'c>, ConstitutiveFibreError> {
        self.require_usable()?;
        self.laws.get(member).ok_or(ConstitutiveFibreError::Shape)
    }
    pub(crate) fn action(&self, member: usize) -> Result<&ResidentConstitutiveFibre<'c>, ConstitutiveFibreError> {
        Ok(self.material(member)?.action())
    }
    /// Attach already-formed normal material to this existing local generator and condition.
    /// Subsequent observations derive their features from the actual prior condition here.
    /// Refusal returns the supplied material and leaves this neighborhood unchanged.
    /// A refusal is the one normal refusal ([`NormalRefusal`]): it returns the material.
    pub fn attach_normal_prediction(&mut self, member: usize, material: ResidentNormalMaterial<'c>)
        -> Result<(), NormalRefusal<ResidentNormalMaterial<'c>>> {
        let prepared = (|| {
            let local = self.material(member)?;
            if local.predictive.is_some() { return Err(ConstitutiveFibreError::Shape); }
            let next = self.epoch.checked_add(1).ok_or(ConstitutiveFibreError::Shape)?;
            Ok((PredictiveMaterial::action_for(&material, &local.law)?, next))
        })();
        match prepared {
            Ok((action, next)) => {
                self.laws[member].predictive = Some(PredictiveMaterial {material,action});
                self.epoch = next;
                Ok(())
            }
            Err(error) => Err(NormalRefusal::new(material, error)),
        }
    }
    pub fn predictive_material(&self, member: usize) -> Result<Option<&ResidentNormalMaterial<'c>>, ConstitutiveFibreError> {
        Ok(self.material(member)?.predictive.as_ref().map(|v| &v.material))
    }
    pub(crate) fn publish_predictive(&mut self,member:usize,epoch:u64,next:PredictiveMaterial<'c>){
        debug_assert!(self.usable&&self.epoch==epoch&&self.laws[member].predictive.is_some());
        self.laws[member].predictive=Some(next);
        self.epoch=epoch.checked_add(1).expect("staged material epoch");
    }

    pub(crate) fn read_wave_relation_in_chart(
        &self,
        member: usize,
        roots: usize,
        receiver: WaveSourceReceiver,
        proposed: Option<&PreparedNeighborhoodConsequence<'c>>,
    ) -> Result<ResidentWaveRelation<'c>, ConstitutiveFibreError> {
        if let Some(p) = proposed {
            if !self.can_commit_consequence(p) {
                return Err(ConstitutiveFibreError::ForeignOccurrence);
            }
            let condition = p
                .condition
                .as_ref()
                .map_or_else(|| self.condition.current(), |v| v.successor());
            if p.member == member {
                if let Some(predictive) = &p.predictive {
                    return predictive.action.read_wave_relation_in_chart(condition, roots, receiver);
                }
                if let Some(formation) = &p.formation {
                    return formation.read_wave_relation(condition, roots, receiver);
                }
            }
            self.action(member)?
                .read_wave_relation_in_chart(condition, roots, receiver)
        } else {
            self.action(member)?.read_wave_relation_in_chart(
                self.condition.current(),
                roots,
                receiver,
            )
        }
    }
    pub(crate) fn can_publish_wave_read(&self, epoch: u64) -> bool {
        self.usable && self.epoch == epoch && self.epoch.checked_add(1).is_some()
    }
    pub(crate) fn publish_wave_read(&mut self, epoch: u64) {
        debug_assert!(self.can_publish_wave_read(epoch));
        self.epoch = epoch + 1;
    }
    pub fn read(
        &self,
        member: usize,
        source: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ResidentConstitutiveReturn<'c>, ConstitutiveFibreError> {
        self.action(member)?
            .read_bilinear(source, self.condition.current())
    }
    /// Ordinary occurrence. A received current first meets the old compatible condition
    /// family through the existing contact law. The proposed condition then participates in
    /// the existing observation-founded local relation return. Both complete before commit.
    /// With no received current, this reads conduct and advances the neighborhood epoch only.
    pub fn advance<'i>(
        &mut self,
        member: usize,
        source: ResidentConstitutiveCurrent<'i, 'c>,
        observed: Option<ResidentConstitutiveCurrent<'i, 'c>>,
    ) -> Result<GeneratorNeighborhoodStep<'i, 'c>, ConstitutiveFibreError> {
        let prepared = self.prepare_consequence(member, source, observed)?;
        Ok(self.publish_consequence(prepared, source, observed))
    }

    /// The same condition-contact and formation law used by ordinary point occurrences.
    /// A caller lifting this operation over a source family retains the dependent alternatives;
    /// this method itself neither publishes nor decides which alternative is actual.
    pub(crate) fn prepare_consequence(
        &mut self,
        member: usize,
        source: ResidentConstitutiveCurrent<'_, 'c>,
        observed: Option<ResidentConstitutiveCurrent<'_, 'c>>,
    ) -> Result<PreparedNeighborhoodConsequence<'c>, ConstitutiveFibreError> {
        self.prepare_consequence_at(member, source, observed, None)
    }
    /// A delayed empirical observation uses its producing condition for the normal moments;
    /// condition contact itself still reacts through the contemporary standing field.
    pub(crate) fn prepare_consequence_at(
        &mut self,
        member: usize,
        source: ResidentConstitutiveCurrent<'_, 'c>,
        observed: Option<ResidentConstitutiveCurrent<'_, 'c>>,
        producing_condition: Option<ResidentConstitutiveCurrent<'_, 'c>>,
    ) -> Result<PreparedNeighborhoodConsequence<'c>, ConstitutiveFibreError> {
        self.prepare_consequence_with(
            member,
            source,
            observed,
            producing_condition,
            ConsequenceCondition::Contemporary,
        )
    }

    /// The one consequence law of an occurrence (plan phase 11: the reaction-observation
    /// passage is this law at [`ConsequenceCondition::Producing`], not a second copy of it).
    /// The prediction reads the declared condition; the normal moments read the producing
    /// condition when supplied; the received current meets the contemporary standing through
    /// the contact law, whose successor is the formation condition unless the passage declares
    /// its producing condition as the formation condition. Nothing is published here.
    pub(crate) fn prepare_consequence_with(
        &mut self,
        member: usize,
        source: ResidentConstitutiveCurrent<'_, 'c>,
        observed: Option<ResidentConstitutiveCurrent<'_, 'c>>,
        producing_condition: Option<ResidentConstitutiveCurrent<'_, 'c>>,
        at: ConsequenceCondition,
    ) -> Result<PreparedNeighborhoodConsequence<'c>, ConstitutiveFibreError> {
        if !self.usable {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let producing = match (at, producing_condition) {
            (ConsequenceCondition::Producing, None) => return Err(ConstitutiveFibreError::Shape),
            (_, producing) => producing,
        };
        let next = self
            .epoch
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let material = self
            .laws
            .get_mut(member)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let prior_condition = self.condition.standing();
        let prediction_condition = match (at, producing) {
            (ConsequenceCondition::Producing, Some(condition)) => condition,
            _ => prior_condition.current(),
        };
        let prediction = material.action().read_bilinear(source, prediction_condition)?;
        let predictive = observed
            .map(|value| {
                material.stage_prediction(
                    source,
                    producing.unwrap_or(prior_condition.current()),
                    value,
                )
            })
            .transpose()?
            .flatten();
        let law = &mut material.law;
        let (condition, formation) = if let Some(observed) = observed {
            let family = law.read_condition_preimage(source, observed)?;
            let proposed = self.condition.prepare_contact(&family)?;
            if !self.condition.can_commit(&proposed) {
                return Err(ConstitutiveFibreError::ForeignOccurrence);
            }
            let formation_condition = match (at, producing) {
                (ConsequenceCondition::Producing, Some(condition)) => condition,
                _ => proposed.successor(),
            };
            self.usable = false;
            let prepared =
                match law.prepare_bilinear_contact(source, formation_condition, Some(observed)) {
                    Ok(value) => value,
                    Err(error) => {
                        self.usable = law.usable;
                        return Err(error);
                    }
                };
            if !law.can_commit_formation(&prepared) {
                self.usable = true;
                return Err(ConstitutiveFibreError::ForeignOccurrence);
            }
            self.usable = true;
            (Some(proposed), Some(prepared))
        } else {
            (None, None)
        };
        Ok(PreparedNeighborhoodConsequence {
            owner: Rc::clone(&self.owner),
            member,
            predecessor_epoch: self.epoch,
            successor_epoch: next,
            prediction,
            prior_condition,
            condition,
            formation,
            predictive,
        })
    }

    pub(crate) fn can_commit_consequence(
        &self,
        prepared: &PreparedNeighborhoodConsequence<'c>,
    ) -> bool {
        self.usable
            && Rc::ptr_eq(&self.owner, &prepared.owner)
            && self.epoch == prepared.predecessor_epoch
            && prepared
                .condition
                .as_ref()
                .map_or(true, |c| self.condition.can_commit(c))
            && prepared
                .formation
                .as_ref()
                .map_or(true, |f| self.laws[prepared.member].law.can_commit_formation(f))
    }

    /// Publish a prepared consequence with the operands it was prepared from.
    pub(crate) fn publish_consequence<'i>(
        &mut self,
        prepared: PreparedNeighborhoodConsequence<'c>,
        source: ResidentConstitutiveCurrent<'i, 'c>,
        observed: Option<ResidentConstitutiveCurrent<'i, 'c>>,
    ) -> GeneratorNeighborhoodStep<'i, 'c> {
        debug_assert!(self.can_commit_consequence(&prepared));
        let contact = prepared
            .condition
            .map(|c| self.condition.publish_prepared(c));
        let formation = prepared
            .formation
            .map(|f| self.laws[prepared.member].law.publish_formation(f));
        if let Some(predictive) = prepared.predictive {
            self.laws[prepared.member].predictive = Some(predictive);
        }
        self.usable = true;
        if let Some(contact) = &contact {
            self.evidence = Some(NeighborhoodEvidence {
                member: prepared.member,
                epoch: prepared.successor_epoch,
                family: ResidentConditionPreimage {
                    inner: Rc::clone(&contact.family().inner),
                },
            });
        }
        self.epoch = prepared.successor_epoch;
        GeneratorNeighborhoodStep {
            owner: Rc::clone(&self.owner),
            member: prepared.member,
            predecessor_epoch: prepared.predecessor_epoch,
            successor_epoch: prepared.successor_epoch,
            prediction: prepared.prediction,
            prior_condition: prepared.prior_condition,
            contact,
            formation,
            source,
            observed,
        }
    }
}
