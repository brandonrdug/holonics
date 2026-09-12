//! Owned executable continuation of a dependent constitutive return. The full generator,
//! original domain and historical joins are the state; a receiver assignment is only its chart.
use super::*;

/// One owner of the complete family-valued successor. The prior wave is moved into immutable
/// generator substrate; it is not exposed as a competing continuing ecology. Evaluation stages
/// only conditional material, using the existing native contact/formation law.
pub struct ResidentCoupledConstitutive<'c> {
    base: ResidentNormalWave<'c, NormalWaveCoupled<'c>>,
    comparison: NormalCoupledComparison<'c>,
    receiver: ResidentSection<'c>,
    operations: Vec<ConstitutiveSourcePassage<'c>>,
    epoch: u64,
    pending: BTreeMap<u64, ConstitutiveProducingCut>,
    released: std::collections::BTreeSet<u64>,
}
struct ConstitutiveSourcePassage<'c> {
    member: usize,
    chart: WaveSourceReceiver,
    kind: ConstitutivePassageKind,
    source: Option<ResidentSection<'c>>,
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(rename_all = "kebab-case")]
enum ConstitutivePassageKind {
    #[default]
    Source,
    FieldInteger,
    FieldRational,
    ObserveInteger,
    ObserveRational,
    Advance,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
struct ConstitutiveProducingCut {
    prefix: usize,
    member: usize,
    chart: WaveSourceReceiver,
}

/// The inner affine comparison is a section of a dependent producing family when root()
/// is present. The complete root generator and its receiver remain borrowed alongside it.
pub struct ConstitutiveComparisonSection<'a, 'c> {
    comparison: NormalCoupledComparison<'c>,
    root: Option<&'a NormalCoupledComparison<'c>>,
    receiver: Option<&'a ResidentSection<'c>>,
}
impl<'a, 'c> ConstitutiveComparisonSection<'a, 'c> {
    pub fn comparison(&self) -> &NormalCoupledComparison<'c> {
        &self.comparison
    }
    pub fn root(&self) -> Option<&NormalCoupledComparison<'c>> {
        self.root
    }
    pub fn receiver(&self) -> Option<&ResidentSection<'c>> {
        self.receiver
    }
}

/// Failed ownership transfer returns every supplied owner and packet recoverably.
pub struct CoupledConstitutiveRefusal<'c> {
    pub wave: ResidentNormalWave<'c, NormalWaveCoupled<'c>>,
    pub comparison: NormalCoupledComparison<'c>,
    pub receiver: ResidentSection<'c>,
    pub reason: ConstitutiveFibreError,
}
impl std::fmt::Debug for CoupledConstitutiveRefusal<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.reason.fmt(f)
    }
}
pub struct ConstitutiveSourceRefusal<'c> {
    pub source: ResidentSection<'c>,
    pub reason: ConstitutiveFibreError,
}
impl std::fmt::Debug for ConstitutiveSourceRefusal<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.reason.fmt(f)
    }
}

impl<'c> ResidentNormalWave<'c, NormalWaveCoupled<'c>> {
    /// Publish the entire executable return family by ownership transfer. No theta-dependent
    /// condition or material matrix is installed as a common value. The caller explicitly names
    /// a receiver section; its supported (possibly plural) output witnesses this scoped admission.
    /// Other source assignments remain executable through evaluate().
    pub fn into_constitutive_continuation(
        mut self,
        comparison: NormalCoupledComparison<'c>,
        receiver: ResidentSection<'c>,
    ) -> Result<ResidentCoupledConstitutive<'c>, CoupledConstitutiveRefusal<'c>> {
        let prepared = (|| {
            let next = self
                .epoch()
                .checked_add(1)
                .ok_or(ConstitutiveFibreError::Shape)?;
            let mut family = self.read_coupled_constitutive_family(&comparison)?;
            let proposed = family.evaluate(&receiver)?;
            proposed
                .successor_section()
                .read_receiver()?
                .require_supported()?;
            Ok::<_, ConstitutiveFibreError>(next)
        })();
        match prepared {
            Ok(epoch) => Ok(ResidentCoupledConstitutive {
                base: self,
                comparison,
                receiver,
                operations: Vec::new(),
                epoch,
                pending: BTreeMap::new(),
                released: std::collections::BTreeSet::new(),
            }),
            Err(reason) => Err(CoupledConstitutiveRefusal {
                wave: self,
                comparison,
                receiver,
                reason,
            }),
        }
    }
}

impl<'c> ResidentCoupledConstitutive<'c> {
    pub fn compare_prediction(
        &mut self,
        id: u64,
        observed: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ConstitutiveComparisonSection<'_, 'c>, ConstitutiveFibreError> {
        if !self.has_prediction(id) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        if let Some(cut) = self.pending.get(&id) {
            let mut value = Self::evaluate_parts(
                &mut self.base,
                &self.comparison,
                &self.operations[..cut.prefix],
                &self.receiver,
            )?;
            let operation = &self.operations[cut.prefix];
            let other = if cut.member == self.comparison.member() {
                None
            } else {
                Some(self.base.neighborhood().generator(cut.member)?)
            };
            Self::apply_operation(&mut value, operation, other)?;
            let conditional = Rc::new(CoupledProducingCut {
                member: cut.member,
                source: value.retained_current(),
                produced: value.retained_successor(),
            });
            let comparison = NormalCoupledComparison::from_cut(id, conditional, observed)?;
            Ok(ConstitutiveComparisonSection {
                comparison,
                root: Some(&self.comparison),
                receiver: Some(&self.receiver),
            })
        } else {
            let handle = self.base.pending_coupled_prediction(id)?;
            let comparison = self.base.compare_coupled_prediction(&handle, observed)?;
            Ok(ConstitutiveComparisonSection {
                comparison,
                root: None,
                receiver: None,
            })
        }
    }
    pub fn epoch(&self) -> u64 {
        self.epoch
    }
    pub fn consumed_prediction(&self) -> u64 {
        self.comparison.prediction_id()
    }
    pub fn source_parameters(&self) -> usize {
        self.comparison.parameter_rows() - 1
    }
    pub fn source_passages(&self) -> usize {
        self.operations
            .iter()
            .filter(|p| {
                matches!(
                    p.kind,
                    ConstitutivePassageKind::Source
                        | ConstitutivePassageKind::FieldInteger
                        | ConstitutivePassageKind::FieldRational
                )
            })
            .count()
    }
    pub fn receiver(&self) -> &ResidentSection<'c> {
        &self.receiver
    }
    pub fn producing_comparison(&self) -> &NormalCoupledComparison<'c> {
        &self.comparison
    }
    /// The consumed cut remains a causal witness inside the generator's frozen substrate, not
    /// an active pending return. There is no operation that remounts that substrate as this owner.
    pub fn pending_prediction_ids(&self) -> impl Iterator<Item = u64> + '_ {
        self.base
            .pending_coupled_prediction_ids()
            .filter(|id| *id != self.consumed_prediction() && !self.released.contains(id))
            .chain(self.pending.keys().copied())
    }
    pub fn pending_prediction(
        &self,
        id: u64,
    ) -> Result<NormalCoupledProducingHandle, ConstitutiveFibreError> {
        if id == self.consumed_prediction() || self.released.contains(&id) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        self.base.pending_coupled_prediction(id)
    }
    fn evaluate_parts<'p, 'j>(
        base: &mut ResidentNormalWave<'c, NormalWaveCoupled<'c>>,
        comparison: &'j NormalCoupledComparison<'c>,
        sources: &[ConstitutiveSourcePassage<'c>],
        parameters: &'p ResidentSection<'c>,
    ) -> Result<CoupledConstitutiveAlternative<'p, 'j, 'c>, ConstitutiveFibreError> {
        let mut value = base
            .read_coupled_constitutive_family(comparison)?
            .evaluate(parameters)?;
        for passage in sources {
            let other = if passage.member == comparison.member() {
                None
            } else {
                Some(base.neighborhood().generator(passage.member)?)
            };
            Self::apply_operation(&mut value, passage, other)?;
        }
        Ok(value)
    }
    pub fn evaluate<'p, 'j>(
        &'j mut self,
        parameters: &'p ResidentSection<'c>,
    ) -> Result<CoupledConstitutiveAlternative<'p, 'j, 'c>, ConstitutiveFibreError> {
        Self::evaluate_parts(
            &mut self.base,
            &self.comparison,
            &self.operations,
            parameters,
        )
    }
    /// A declared source-section receiver of this complete generator. This is not asserted to
    /// equal a minimum-norm projection over its entire non-affine source/condition graph.
    pub fn read_receiver(
        &mut self,
    ) -> Result<CoupledConstitutiveAlternative<'_, '_, 'c>, ConstitutiveFibreError> {
        Self::evaluate_parts(
            &mut self.base,
            &self.comparison,
            &self.operations,
            &self.receiver,
        )
    }
    pub fn roots(&self) -> usize {
        self.base.normal_material().roots
    }
    pub fn passages(&self) -> u64 {
        self.base.current().passages() + 1 + self.operations.len() as u64
    }
    pub fn members(&self) -> usize {
        self.base.neighborhood().members()
    }
    pub fn has_prediction(&self, id: u64) -> bool {
        self.pending_prediction_ids().any(|p| p == id)
    }
    pub fn release_prediction(&mut self, id: u64) -> Result<(), ConstitutiveFibreError> {
        if !self.has_prediction(id) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        if self.pending.remove(&id).is_none() {
            self.released.insert(id);
        }
        Ok(())
    }
    pub fn read_basis_face(
        &mut self,
        chart: &NormalWaveBasisChart<'c>,
    ) -> Result<NormalFamilyBasisFace<'c>, ConstitutiveFibreError> {
        let epoch = self.epoch;
        let source = self.read_receiver()?.retained_successor();
        chart.read_family(source, epoch)
    }
    fn apply_operation(
        value: &mut CoupledConstitutiveAlternative<'_, '_, 'c>,
        passage: &ConstitutiveSourcePassage<'c>,
        other: Option<&ResidentConstitutiveFibre<'c>>,
    ) -> Result<(), ConstitutiveFibreError> {
        let next = value
            .successor_section()
            .passages()
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        match passage.kind {
            ConstitutivePassageKind::Source => value.actuate_source(
                passage.member,
                other,
                passage.chart,
                ResidentConstitutiveCurrent::rational(
                    passage
                        .source
                        .as_ref()
                        .ok_or(ConstitutiveFibreError::Shape)?,
                )?,
            ),
            ConstitutivePassageKind::Advance => {
                let map = value.member_relation(passage.member, other, passage.chart)?;
                value.apply_map(Rc::new(map), next)
            }
            ConstitutivePassageKind::ObserveInteger | ConstitutivePassageKind::ObserveRational => {
                let packet = passage
                    .source
                    .as_ref()
                    .ok_or(ConstitutiveFibreError::Shape)?;
                let current = if passage.kind == ConstitutivePassageKind::ObserveInteger {
                    ResidentConstitutiveCurrent::integers(packet)?
                } else {
                    ResidentConstitutiveCurrent::rational(packet)?
                };
                let map = value
                    .member_relation(passage.member, other, passage.chart)?
                    .read_observed_next(current)?;
                value.apply_map(Rc::new(map), next)
            }
            ConstitutivePassageKind::FieldInteger | ConstitutivePassageKind::FieldRational => {
                let packet = passage
                    .source
                    .as_ref()
                    .ok_or(ConstitutiveFibreError::Shape)?;
                let section = if passage.kind == ConstitutivePassageKind::FieldInteger {
                    ResidentConstitutiveSection::integers(packet)?
                } else {
                    ResidentConstitutiveSection::rationals(packet)?
                };
                let s = value.comparison().source().origin().fibre().surface;
                let pairs = section.source_pairs(s)?;
                for row in 0..pairs.source().rows() {
                    value.actuate_source_at(
                        passage.member,
                        other,
                        passage.chart,
                        pairs.source().row(row)?,
                        next,
                    )?;
                }
                Ok(())
            }
        }
    }
    fn append_operation(
        &mut self,
        operation: ConstitutiveSourcePassage<'c>,
        retain: bool,
    ) -> Result<(), (ConstitutiveSourcePassage<'c>, ConstitutiveFibreError)> {
        let prepared = (|| {
            let next = self
                .epoch
                .checked_add(1)
                .ok_or(ConstitutiveFibreError::Shape)?;
            self.operations
                .try_reserve(1)
                .map_err(|_| ConstitutiveFibreError::Shape)?;
            let mut value = Self::evaluate_parts(
                &mut self.base,
                &self.comparison,
                &self.operations,
                &self.receiver,
            )?;
            let other = if operation.member == self.comparison.member() {
                None
            } else {
                Some(self.base.neighborhood().generator(operation.member)?)
            };
            Self::apply_operation(&mut value, &operation, other)?;
            value
                .successor_section()
                .read_receiver()?
                .require_supported()?;
            Ok::<_, ConstitutiveFibreError>(next)
        })();
        match prepared {
            Ok(next) => {
                if retain {
                    self.pending.insert(
                        next,
                        ConstitutiveProducingCut {
                            prefix: self.operations.len(),
                            member: operation.member,
                            chart: operation.chart,
                        },
                    );
                }
                self.operations.push(operation);
                self.epoch = next;
                Ok(())
            }
            Err(error) => Err((operation, error)),
        }
    }
    pub fn advance_member(
        &mut self,
        member: usize,
        chart: WaveSourceReceiver,
    ) -> Result<(), ConstitutiveFibreError> {
        self.append_operation(
            ConstitutiveSourcePassage {
                member,
                chart,
                kind: ConstitutivePassageKind::Advance,
                source: None,
            },
            false,
        )
        .map_err(|(_, e)| e)
    }
    pub fn predict_member(
        &mut self,
        member: usize,
        chart: WaveSourceReceiver,
    ) -> Result<u64, ConstitutiveFibreError> {
        self.append_operation(
            ConstitutiveSourcePassage {
                member,
                chart,
                kind: ConstitutivePassageKind::Advance,
                source: None,
            },
            true,
        )
        .map_err(|(_, e)| e)?;
        Ok(self.epoch)
    }
    pub fn read_proposed_member(
        &mut self,
        member: usize,
        chart: WaveSourceReceiver,
    ) -> Result<CoupledConstitutiveAlternative<'_, '_, 'c>, ConstitutiveFibreError> {
        let mut value = Self::evaluate_parts(
            &mut self.base,
            &self.comparison,
            &self.operations,
            &self.receiver,
        )?;
        let other = if member == self.comparison.member() {
            None
        } else {
            Some(self.base.neighborhood().generator(member)?)
        };
        Self::apply_operation(
            &mut value,
            &ConstitutiveSourcePassage {
                member,
                chart,
                kind: ConstitutivePassageKind::Advance,
                source: None,
            },
            other,
        )?;
        Ok(value)
    }
    fn append_packet(
        &mut self,
        member: usize,
        chart: WaveSourceReceiver,
        kind: ConstitutivePassageKind,
        source: ResidentSection<'c>,
    ) -> Result<(), ConstitutiveSourceRefusal<'c>> {
        self.append_operation(
            ConstitutiveSourcePassage {
                member,
                chart,
                kind,
                source: Some(source),
            },
            false,
        )
        .map_err(|(p, reason)| ConstitutiveSourceRefusal {
            source: p.source.expect("packet operation"),
            reason,
        })
    }
    pub fn actuate_source(
        &mut self,
        member: usize,
        chart: WaveSourceReceiver,
        source: ResidentSection<'c>,
    ) -> Result<(), ConstitutiveSourceRefusal<'c>> {
        self.append_packet(member, chart, ConstitutivePassageKind::Source, source)
    }
    pub fn actuate_field(
        &mut self,
        member: usize,
        chart: WaveSourceReceiver,
        source: ResidentSection<'c>,
        rational: bool,
    ) -> Result<(), ConstitutiveSourceRefusal<'c>> {
        self.append_packet(
            member,
            chart,
            if rational {
                ConstitutivePassageKind::FieldRational
            } else {
                ConstitutivePassageKind::FieldInteger
            },
            source,
        )
    }
    pub fn receive_next_current(
        &mut self,
        member: usize,
        chart: WaveSourceReceiver,
        source: ResidentSection<'c>,
        rational: bool,
    ) -> Result<(), ConstitutiveSourceRefusal<'c>> {
        self.append_packet(
            member,
            chart,
            if rational {
                ConstitutivePassageKind::ObserveRational
            } else {
                ConstitutivePassageKind::ObserveInteger
            },
            source,
        )
    }
}

mod rest;
pub use rest::CoupledConstitutiveRest;
#[cfg(test)]
mod tests;
