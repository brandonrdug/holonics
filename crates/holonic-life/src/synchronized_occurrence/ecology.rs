use super::*;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SynchronizedAssociationLineage {
    pub candidate_occurrences: BTreeMap<u64, u64>,
    pub ride_occurrences: BTreeMap<u64, u64>,
    pub found_occurrences: BTreeMap<u64, u64>,
    pub open_occurrences: BTreeMap<u64, u64>,
}

impl SynchronizedAssociationLineage {
    pub fn established(&self) -> bool {
        !self.ride_occurrences.is_empty()
    }

    pub fn obstructed(&self) -> bool {
        !self.open_occurrences.is_empty()
    }
}

/// Sparse observation atlas over receiver-caused Swing outcomes.
///
/// It is not an alternative association law. Every row is admitted from an
/// immediate `SynchronizedContactRadiation` emitted by the production
/// machine, and every occurrence multiplicity remains inspectable.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct SynchronizedAssociationAtlas {
    pub relations: BTreeMap<SynchronizedAssociationSignature, SynchronizedAssociationLineage>,
}

impl SynchronizedAssociationAtlas {
    /// Prove that every possible exact outcome for these already-derived contacts can enter the
    /// rebuildable observation atlas before the causal machine commits. Ride, found, and open are
    /// all checked because the direct return, not this observer, selects which occurred.
    pub fn preflight_contacts(
        &self,
        occurrence: u64,
        contacts: &[SynchronizedContactOccurrence],
    ) -> Result<(), SynchronizedOccurrenceError> {
        let mut multiplicities = BTreeMap::<SynchronizedAssociationSignature, u64>::new();
        for contact in contacts {
            let multiplicity = multiplicities.entry(contact.signature.clone()).or_default();
            *multiplicity = multiplicity
                .checked_add(1)
                .ok_or(SynchronizedOccurrenceError::CarrierOverflow)?;
        }
        for (signature, multiplicity) in multiplicities {
            let Some(lineage) = self.relations.get(&signature) else {
                continue;
            };
            preflight_occurrence_increment(
                &lineage.candidate_occurrences,
                occurrence,
                multiplicity,
            )?;
            preflight_occurrence_increment(&lineage.ride_occurrences, occurrence, multiplicity)?;
            preflight_occurrence_increment(&lineage.found_occurrences, occurrence, multiplicity)?;
            preflight_occurrence_increment(&lineage.open_occurrences, occurrence, multiplicity)?;
        }
        Ok(())
    }

    pub fn observe(
        &mut self,
        radiation: &SynchronizedOccurrenceRadiation,
    ) -> Result<(), SynchronizedOccurrenceError> {
        for contact in &radiation.contacts {
            let lineage = self
                .relations
                .entry(contact.contact.signature.clone())
                .or_default();
            increment_occurrence(&mut lineage.candidate_occurrences, radiation.occurrence)?;
            if contact.formed_ride {
                increment_occurrence(&mut lineage.ride_occurrences, radiation.occurrence)?;
            }
            if contact.formed_found {
                increment_occurrence(&mut lineage.found_occurrences, radiation.occurrence)?;
            }
            if contact.open {
                increment_occurrence(&mut lineage.open_occurrences, radiation.occurrence)?;
            }
        }
        Ok(())
    }

    pub fn lineage(
        &self,
        signature: &SynchronizedAssociationSignature,
    ) -> Option<&SynchronizedAssociationLineage> {
        self.relations.get(signature)
    }
}

fn increment_occurrence(
    population: &mut BTreeMap<u64, u64>,
    occurrence: u64,
) -> Result<(), SynchronizedOccurrenceError> {
    let next = population
        .get(&occurrence)
        .copied()
        .unwrap_or(0)
        .checked_add(1)
        .ok_or(SynchronizedOccurrenceError::CarrierOverflow)?;
    population.insert(occurrence, next);
    Ok(())
}

fn preflight_occurrence_increment(
    population: &BTreeMap<u64, u64>,
    occurrence: u64,
    additional: u64,
) -> Result<(), SynchronizedOccurrenceError> {
    population
        .get(&occurrence)
        .copied()
        .unwrap_or(0)
        .checked_add(additional)
        .ok_or(SynchronizedOccurrenceError::CarrierOverflow)?;
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SynchronizedEvidenceAddress {
    pub context_receiver: SynchronizedReceiverId,
    pub context_cells: Vec<SynchronizedCellId>,
    pub context_face: SynchronizedSectionFace,
    pub target_receiver: SynchronizedReceiverId,
    pub target_charts: Vec<(u64, u32)>,
    pub interval_begin: ExactOccurrenceTime,
    pub interval_end: ExactOccurrenceTime,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SynchronizedRelationStanding {
    Established,
    Open,
    Candidate,
    Unseen,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SynchronizedCandidatePrediction {
    pub candidate: SynchronizedCandidateId,
    pub evidence: BTreeMap<SynchronizedEvidenceAddress, SynchronizedRelationStanding>,
    pub established_support: BTreeSet<SynchronizedEvidenceAddress>,
    pub open_support: BTreeSet<SynchronizedEvidenceAddress>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SynchronizedPrediction {
    pub ecology_revision: u64,
    pub target_receiver: SynchronizedReceiverId,
    pub candidates: BTreeMap<SynchronizedCandidateId, SynchronizedCandidatePrediction>,
    pub maximal_fiber: BTreeSet<SynchronizedCandidateId>,
    pub invariant: Option<SynchronizedCandidateId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SynchronizedPredictionAlternative {
    pub candidate: SynchronizedCandidateId,
    pub occurrence: ExactSynchronizedOccurrence,
}

impl SynchronizedAssociationAtlas {
    pub fn predict(
        &self,
        ecology_revision: u64,
        target_receiver: SynchronizedReceiverId,
        alternatives: &[SynchronizedPredictionAlternative],
    ) -> Result<SynchronizedPrediction, SynchronizedOccurrenceError> {
        if alternatives.is_empty() {
            return Err(SynchronizedOccurrenceError::EmptyPredictionFiber);
        }
        let chart = SynchronizedOccurrenceChart::new();
        let mut candidates = BTreeMap::new();
        let mut common_evidence = None::<BTreeSet<SynchronizedEvidenceAddress>>;
        for alternative in alternatives {
            if candidates.contains_key(&alternative.candidate) {
                return Err(SynchronizedOccurrenceError::DuplicateCandidate(
                    alternative.candidate,
                ));
            }
            let contacts = chart.contacts(&alternative.occurrence)?;
            let mut evidence = BTreeMap::new();
            for contact in contacts {
                let signature = &contact.signature;
                let target_is_left = signature.left_receiver == target_receiver;
                let target_is_right = signature.right_receiver == target_receiver;
                if target_is_left == target_is_right {
                    continue;
                }
                let (context_receiver, context_cells, context_face, target_face) = if target_is_left
                {
                    (
                        signature.right_receiver,
                        contact.right_cells.clone(),
                        signature.right_face.clone(),
                        &signature.left_face,
                    )
                } else {
                    (
                        signature.left_receiver,
                        contact.left_cells.clone(),
                        signature.left_face.clone(),
                        &signature.right_face,
                    )
                };
                let mut target_charts = target_face
                    .0
                    .iter()
                    .map(|facet| (facet.chart, facet.stage))
                    .collect::<Vec<_>>();
                target_charts.sort();
                let address = SynchronizedEvidenceAddress {
                    context_receiver,
                    context_cells,
                    context_face,
                    target_receiver,
                    target_charts,
                    interval_begin: contact.interval_begin,
                    interval_end: contact.interval_end,
                };
                let standing = match self.lineage(signature) {
                    Some(lineage) if lineage.established() => {
                        SynchronizedRelationStanding::Established
                    }
                    Some(lineage) if lineage.obstructed() => SynchronizedRelationStanding::Open,
                    Some(_) => SynchronizedRelationStanding::Candidate,
                    None => SynchronizedRelationStanding::Unseen,
                };
                evidence.insert(address, standing);
            }
            if evidence.is_empty() {
                return Err(SynchronizedOccurrenceError::TargetHasNoCrossContact(
                    target_receiver,
                ));
            }
            let evidence_keys = evidence.keys().cloned().collect::<BTreeSet<_>>();
            if let Some(common) = &common_evidence {
                if common != &evidence_keys {
                    return Err(SynchronizedOccurrenceError::IncomparableCandidateCharts);
                }
            } else {
                common_evidence = Some(evidence_keys);
            }
            let established_support = evidence
                .iter()
                .filter_map(|(address, standing)| {
                    (*standing == SynchronizedRelationStanding::Established)
                        .then_some(address.clone())
                })
                .collect();
            let open_support = evidence
                .iter()
                .filter_map(|(address, standing)| {
                    (*standing == SynchronizedRelationStanding::Open).then_some(address.clone())
                })
                .collect();
            candidates.insert(
                alternative.candidate,
                SynchronizedCandidatePrediction {
                    candidate: alternative.candidate,
                    evidence,
                    established_support,
                    open_support,
                },
            );
        }

        let mut maximal_fiber = candidates.keys().copied().collect::<BTreeSet<_>>();
        for (left_id, left) in &candidates {
            for (right_id, right) in &candidates {
                if left_id != right_id && candidate_dominates(right, left) {
                    maximal_fiber.remove(left_id);
                    break;
                }
            }
        }
        let invariant = if maximal_fiber.len() == 1 {
            maximal_fiber.iter().next().copied()
        } else {
            None
        };
        Ok(SynchronizedPrediction {
            ecology_revision,
            target_receiver,
            candidates,
            maximal_fiber,
            invariant,
        })
    }
}

fn candidate_dominates(
    candidate: &SynchronizedCandidatePrediction,
    other: &SynchronizedCandidatePrediction,
) -> bool {
    candidate
        .established_support
        .is_superset(&other.established_support)
        && candidate.open_support.is_subset(&other.open_support)
        && (candidate.established_support != other.established_support
            || candidate.open_support != other.open_support)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SynchronizedReturnGrade {
    pub ecology_revision: u64,
    pub returned: SynchronizedCandidateId,
    pub admitted_by_fiber: bool,
    pub exact_invariant: bool,
    pub predicted_fiber: BTreeSet<SynchronizedCandidateId>,
    pub returned_established_support: BTreeSet<SynchronizedEvidenceAddress>,
    pub returned_open_support: BTreeSet<SynchronizedEvidenceAddress>,
    pub dominating_alternatives: BTreeSet<SynchronizedCandidateId>,
}

impl SynchronizedPrediction {
    pub fn grade(
        &self,
        returned: SynchronizedCandidateId,
    ) -> Result<SynchronizedReturnGrade, SynchronizedOccurrenceError> {
        let returned_body = self.candidates.get(&returned).ok_or(
            SynchronizedOccurrenceError::UnknownReturnedCandidate(returned),
        )?;
        let dominating_alternatives = self
            .candidates
            .iter()
            .filter_map(|(candidate, body)| {
                (*candidate != returned && candidate_dominates(body, returned_body))
                    .then_some(*candidate)
            })
            .collect();
        Ok(SynchronizedReturnGrade {
            ecology_revision: self.ecology_revision,
            returned,
            admitted_by_fiber: self.maximal_fiber.contains(&returned),
            exact_invariant: self.invariant == Some(returned),
            predicted_fiber: self.maximal_fiber.clone(),
            returned_established_support: returned_body.established_support.clone(),
            returned_open_support: returned_body.open_support.clone(),
            dominating_alternatives,
        })
    }
}

/// Exact synchronized training ecology. The live-current machine remains the
/// causal authority; the association atlas is its sparse observation index.
pub struct SynchronizedEcology {
    machine: LiveCurrentMachine,
    chart: SynchronizedOccurrenceChart,
    atlas: SynchronizedAssociationAtlas,
    revision: u64,
}

#[derive(Debug, PartialEq, Eq)]
pub struct SynchronizedEcologyRestImage {
    machine: LiveCurrentRestImage,
    chart: SynchronizedOccurrenceChart,
    atlas: SynchronizedAssociationAtlas,
    revision: u64,
}

/// A failed ownership-transfer rest. The contemporary ecology remains recoverable and no
/// partially formed rest image becomes standing.
pub struct SynchronizedEcologyRestRefusal {
    ecology: SynchronizedEcology,
    error: SynchronizedOccurrenceError,
}

impl std::fmt::Debug for SynchronizedEcologyRestRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("SynchronizedEcologyRestRefusal")
            .field("error", &self.error)
            .field("revision", &self.ecology.revision)
            .finish_non_exhaustive()
    }
}

impl SynchronizedEcologyRestRefusal {
    pub const fn error(&self) -> &SynchronizedOccurrenceError {
        &self.error
    }

    pub fn recover(self) -> SynchronizedEcology {
        self.ecology
    }
}

impl SynchronizedEcology {
    pub fn new(machine: LiveCurrentMachine) -> Self {
        Self {
            machine,
            chart: SynchronizedOccurrenceChart::new(),
            atlas: SynchronizedAssociationAtlas::default(),
            revision: 0,
        }
    }

    pub fn machine(&self) -> &LiveCurrentMachine {
        &self.machine
    }

    pub fn atlas(&self) -> &SynchronizedAssociationAtlas {
        &self.atlas
    }

    pub const fn revision(&self) -> u64 {
        self.revision
    }

    pub fn receive(
        &mut self,
        occurrence: &ExactSynchronizedOccurrence,
        action: ActionCurrent,
    ) -> Result<SynchronizedOccurrenceRadiation, SynchronizedOccurrenceError> {
        let next_revision = self
            .revision
            .checked_add(1)
            .ok_or(SynchronizedOccurrenceError::CarrierOverflow)?;
        let anticipated = self.chart.contacts(occurrence)?;
        self.atlas
            .preflight_contacts(occurrence.occurrence, &anticipated)?;
        let radiation = self.chart.observe(&mut self.machine, occurrence, action)?;
        self.atlas
            .observe(&radiation)
            .expect("the complete observer increment was preflighted before live commit");
        self.revision = next_revision;
        Ok(radiation)
    }

    pub fn receive_with(
        &mut self,
        executor: &mut dyn LiveCurrentExecutor,
        occurrence: &ExactSynchronizedOccurrence,
        action: ActionCurrent,
    ) -> Result<SynchronizedOccurrenceRadiation, SynchronizedOccurrenceError> {
        let next_revision = self
            .revision
            .checked_add(1)
            .ok_or(SynchronizedOccurrenceError::CarrierOverflow)?;
        let anticipated = self.chart.contacts(occurrence)?;
        self.atlas
            .preflight_contacts(occurrence.occurrence, &anticipated)?;
        let radiation = self
            .chart
            .observe_with(&mut self.machine, executor, occurrence, action)?;
        self.atlas
            .observe(&radiation)
            .expect("the complete observer increment was preflighted before live commit");
        self.revision = next_revision;
        Ok(radiation)
    }

    pub fn predict(
        &self,
        target_receiver: SynchronizedReceiverId,
        alternatives: &[SynchronizedPredictionAlternative],
    ) -> Result<SynchronizedPrediction, SynchronizedOccurrenceError> {
        self.atlas
            .predict(self.revision, target_receiver, alternatives)
    }

    /// Grade against the untouched contemporary ecology, then admit the
    /// actual returned occurrence and let it condition later conduct.
    pub fn grade_then_receive(
        &mut self,
        prediction: &SynchronizedPrediction,
        returned: SynchronizedCandidateId,
        returned_occurrence: &ExactSynchronizedOccurrence,
        action: ActionCurrent,
    ) -> Result<
        (SynchronizedReturnGrade, SynchronizedOccurrenceRadiation),
        SynchronizedOccurrenceError,
    > {
        if prediction.ecology_revision != self.revision {
            return Err(SynchronizedOccurrenceError::PredictionEcologyChanged {
                predicted: prediction.ecology_revision,
                contemporary: self.revision,
            });
        }
        let grade = prediction.grade(returned)?;
        let radiation = self.receive(returned_occurrence, action)?;
        Ok((grade, radiation))
    }

    /// Suspend the complete ecology by ownership transfer. The chart and association atlas move
    /// into the rest body; no second live observation owner survives beside it.
    pub fn into_rest_image(
        self,
    ) -> Result<SynchronizedEcologyRestImage, SynchronizedEcologyRestRefusal> {
        let machine = match self.machine.rest_image() {
            Ok(machine) => machine,
            Err(error) => {
                return Err(SynchronizedEcologyRestRefusal {
                    ecology: self,
                    error: error.into(),
                });
            }
        };
        let Self {
            machine: _,
            chart,
            atlas,
            revision,
        } = self;
        Ok(SynchronizedEcologyRestImage {
            machine,
            chart,
            atlas,
            revision,
        })
    }

    pub fn from_rest_image(
        image: SynchronizedEcologyRestImage,
    ) -> Result<Self, SynchronizedOccurrenceError> {
        Ok(Self {
            machine: LiveCurrentMachine::from_rest_image(image.machine)?,
            chart: image.chart,
            atlas: image.atlas,
            revision: image.revision,
        })
    }
}
