//! Exact consequence-path cultivation for bounded application worlds.
//!
//! A training occurrence supplies co-present, locally addressed source faces, a receiver face,
//! and the consequence which actually followed.  The ecology derives causal paths through that
//! occurrence itself: a path either RIDEs one complete supplied face into the consequence or
//! FOUNDS an exact consequence span.  Recurring path forms become addressable and may later be
//! rebound to nonidentical source material.
//!
//! This carrier deliberately does not infer a hidden implementation from input/output examples.
//! If an interpreter, compiler, sensor, or other transducer exposes a deeper execution path, that
//! path is additional lawful source material.  The object here is the medium-neutral relation
//! actually observable at the boundary:
//!
//! ```text
//! co-present antecedent faces + receiver face -> complete returned consequence
//! ```

use std::collections::{BTreeMap, BTreeSet};

use holonic_structure::GrowingKeyAtlas;

/// A source-local address.  It is a binding axis inside one declared ecology, not a semantic
/// identity, global token id, hash, or claim that two equal byte faces have the same lineage.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FaceAddress {
    pub axis: String,
    pub ordinal: u64,
}

impl FaceAddress {
    pub fn new(axis: impl Into<String>, ordinal: u64) -> Self {
        Self {
            axis: axis.into(),
            ordinal,
        }
    }
}

/// One co-present face made available by the current world occurrence.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SourceFace {
    pub address: FaceAddress,
    pub value: Vec<u8>,
}

/// One receiver cut through the same co-present occurrence.
///
/// Several views may receive one consequence at once without turning them into a chronology.
/// This is useful when a world exposes nested grains or several simultaneous receivers.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TrainingView {
    pub faces: Vec<SourceFace>,
    pub parameters: BTreeMap<String, String>,
}

impl SourceFace {
    pub fn new(address: FaceAddress, value: impl Into<Vec<u8>>) -> Self {
        Self {
            address,
            value: value.into(),
        }
    }
}

/// One edge in the exact consequence-boundary complex of an observed occurrence.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConsequenceEdge {
    /// An existing complete face occurs at this oriented consequence interval.
    Copy {
        from: usize,
        to: usize,
        face: FaceAddress,
    },
    /// This elementary interval is not attributed to a supplied face by this edge.
    Found {
        from: usize,
        to: usize,
        value: Vec<u8>,
    },
}

/// The finite acyclic complex whose vertices are exact consequence boundaries.
///
/// Unit FOUND edges ensure that every finite consequence has at least one complete route.  COPY
/// edges add every exact occurrence of every supplied face.  A route is therefore never guessed:
/// it is one compositional reading of the observed event.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConsequenceComplex {
    pub extent: usize,
    pub edges: Vec<ConsequenceEdge>,
}

/// One reusable step after occurrence-local values have been factored out.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TemplateStep {
    /// Rebind the complete face at this local address.
    Copy { face: FaceAddress },
    /// Retain an exact founded interval.
    Found { value: Vec<u8> },
}

/// One complete source-to-consequence route.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TransductionTemplate {
    pub steps: Vec<TemplateStep>,
}

/// Receiver-relative recurrence of one complete route form.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TransductionFiber {
    pub template: TransductionTemplate,
    pub parameters: Vec<(String, String)>,
}

/// A concrete path after a later occurrence has rebound every copied face.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PathStep {
    Copy { face: FaceAddress, value: Vec<u8> },
    Found { value: Vec<u8> },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TransductionPath {
    pub steps: Vec<PathStep>,
    pub consequence: Vec<u8>,
}

impl TransductionPath {
    pub fn validate(&self) -> Result<(), String> {
        if self.steps.is_empty() {
            return Err("a transduction path has no causal step".to_owned());
        }
        let mut consequence = Vec::<u8>::new();
        for step in &self.steps {
            let value = match step {
                PathStep::Copy { face, value } => {
                    validate_address(face)?;
                    if value.is_empty() {
                        return Err("a COPY step carries an empty source face".to_owned());
                    }
                    value
                }
                PathStep::Found { value } => {
                    if value.is_empty() {
                        return Err("a FOUND step carries an empty interval".to_owned());
                    }
                    value
                }
            };
            consequence.extend(value);
        }
        if consequence != self.consequence {
            return Err("a transduction path does not compose its consequence".to_owned());
        }
        Ok(())
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct TrainingEcology {
    pub generation: u64,
    pub minimum_recurrence: u64,
    /// A physical refusal boundary.  Derivation returns OPEN with an error before losing routes;
    /// it never truncates or ranks them.
    pub maximum_templates_per_occurrence: usize,
    pub fibers: GrowingKeyAtlas<TransductionFiber, u64>,
}

#[derive(Debug, PartialEq, Eq)]
struct TrainingFiberUpdate {
    fiber: TransductionFiber,
    prior_recurrence: u64,
    next_recurrence: u64,
}

/// One fully derived, still-uncommitted training occurrence.
///
/// It contains only the caused difference from the contemporary ecology. The complete ecology is
/// neither cloned nor temporarily replaced. A proposal is bound to the generation which derived
/// it and is refused intact if another return has changed that generation before commitment.
#[derive(Debug, PartialEq, Eq)]
pub struct TrainingCultivationProposal {
    expected_generation: u64,
    next_generation: u64,
    active_templates_before: usize,
    active_templates_after: usize,
    updates: Box<[TrainingFiberUpdate]>,
    observations: Box<[ObservedTransduction]>,
}

impl TrainingCultivationProposal {
    pub fn observations(&self) -> &[ObservedTransduction] {
        &self.observations
    }

    pub const fn active_templates_before(&self) -> usize {
        self.active_templates_before
    }

    pub const fn active_templates_after(&self) -> usize {
        self.active_templates_after
    }

    pub const fn next_generation(&self) -> u64 {
        self.next_generation
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct TrainingCommitRefusal {
    pub error: String,
    pub proposal: TrainingCultivationProposal,
}

impl TrainingEcology {
    pub fn new(
        minimum_recurrence: u64,
        maximum_templates_per_occurrence: usize,
    ) -> Result<Self, String> {
        if minimum_recurrence < 2 {
            return Err("a transduction template requires at least two occurrences".to_owned());
        }
        if maximum_templates_per_occurrence == 0 {
            return Err("the exact route aperture cannot be zero".to_owned());
        }
        Ok(Self {
            generation: 0,
            minimum_recurrence,
            maximum_templates_per_occurrence,
            fibers: GrowingKeyAtlas::new(),
        })
    }

    /// Observe one complete occurrence and retain every exact route through it.
    ///
    /// A template is counted at most once per occurrence even when repeated equal source faces
    /// give it several occurrence-local placements.  Recurrence therefore means recurrence
    /// across events, not multiplication by one event's internal symmetry.
    pub fn cultivate(
        &mut self,
        faces: &[SourceFace],
        parameters: &BTreeMap<String, String>,
        consequence: &[u8],
    ) -> Result<ObservedTransduction, String> {
        let mut observed = self.cultivate_views(
            &[TrainingView {
                faces: faces.to_vec(),
                parameters: parameters.clone(),
            }],
            consequence,
        )?;
        Ok(observed.remove(0))
    }

    /// Receive several simultaneous cuts through one actual consequence.
    ///
    /// All complexes, paths, predictions, and residuals are derived before mutation.  The
    /// generation advances once, and duplicate views are refused, so a family of receiver cuts
    /// cannot manufacture recurrence by repeating one face.
    pub fn cultivate_views(
        &mut self,
        views: &[TrainingView],
        consequence: &[u8],
    ) -> Result<Vec<ObservedTransduction>, String> {
        let proposal = self.propose_views(views, consequence)?;
        self.commit_views(proposal)
            .map(|observations| observations.into_vec())
            .map_err(|refusal| refusal.error)
    }

    /// Derive the complete changed fiber population without changing standing.
    pub fn propose_views(
        &self,
        views: &[TrainingView],
        consequence: &[u8],
    ) -> Result<TrainingCultivationProposal, String> {
        self.validate()?;
        if views.is_empty() {
            return Err("a training occurrence exposes no receiver view".to_owned());
        }
        let mut unique = BTreeSet::new();
        let mut pending_fibers = BTreeSet::new();
        let mut derived = Vec::with_capacity(views.len());
        for view in views {
            if !unique.insert(view.clone()) {
                return Err("one occurrence repeats an identical receiver view".to_owned());
            }
            let complex = consequence_complex(&view.faces, consequence)?;
            let templates = derive_templates(&complex, self.maximum_templates_per_occurrence)?;
            let prior = self.predict(&view.faces, &view.parameters)?;
            let relation = prior.relation_to(consequence);
            let receiver = view
                .parameters
                .iter()
                .map(|(name, value)| (name.clone(), value.clone()))
                .collect::<Vec<_>>();
            if receiver.iter().any(|(name, _)| name.is_empty()) {
                return Err("a training receiver has an empty axis".to_owned());
            }
            for template in &templates {
                pending_fibers.insert(TransductionFiber {
                    template: template.clone(),
                    parameters: receiver.clone(),
                });
            }
            derived.push(ObservedTransduction {
                complex,
                templates,
                prior,
                relation,
            });
        }

        let next_generation = self
            .generation
            .checked_add(1)
            .ok_or_else(|| "training ecology generation overflowed".to_owned())?;
        let mut updates = vec![];
        updates
            .try_reserve(pending_fibers.len())
            .map_err(|_| "training proposal could not reserve its changed fibers".to_owned())?;
        for fiber in pending_fibers {
            let prior_recurrence = self.fibers.get(&fiber).copied().unwrap_or(0);
            let next_recurrence = prior_recurrence
                .checked_add(1)
                .ok_or_else(|| "transduction recurrence overflowed".to_owned())?;
            updates.push(TrainingFiberUpdate {
                fiber,
                prior_recurrence,
                next_recurrence,
            });
        }
        let active_templates_before = self.active_template_count();
        let newly_active = updates
            .iter()
            .filter(|update| {
                update.prior_recurrence < self.minimum_recurrence
                    && update.next_recurrence >= self.minimum_recurrence
            })
            .count();
        let active_templates_after = active_templates_before
            .checked_add(newly_active)
            .ok_or_else(|| "active transduction population overflowed".to_owned())?;
        Ok(TrainingCultivationProposal {
            expected_generation: self.generation,
            next_generation,
            active_templates_before,
            active_templates_after,
            updates: updates.into_boxed_slice(),
            observations: derived.into_boxed_slice(),
        })
    }

    /// Atomically accept one previously derived occurrence or return that proposal intact.
    pub fn commit_views(
        &mut self,
        proposal: TrainingCultivationProposal,
    ) -> Result<Box<[ObservedTransduction]>, TrainingCommitRefusal> {
        if self.generation != proposal.expected_generation {
            return Err(TrainingCommitRefusal {
                error: "the training ecology changed before the proposed return committed"
                    .to_owned(),
                proposal,
            });
        }
        for update in &proposal.updates {
            if self.fibers.get(&update.fiber).copied().unwrap_or(0) != update.prior_recurrence {
                return Err(TrainingCommitRefusal {
                    error: "a proposed training fiber changed before commitment".to_owned(),
                    proposal,
                });
            }
        }
        let new_fibers = proposal
            .updates
            .iter()
            .filter(|update| !self.fibers.contains(&update.fiber))
            .count();
        if self.fibers.try_reserve_new_keys(new_fibers).is_err() {
            return Err(TrainingCommitRefusal {
                error: "the training fiber atlas could not reserve the proposed return".to_owned(),
                proposal,
            });
        }
        let TrainingCultivationProposal {
            next_generation,
            updates,
            observations,
            ..
        } = proposal;
        for update in updates {
            self.fibers
                .try_insert(update.fiber, update.next_recurrence)
                .expect("the preflighted training fiber batch remains admissible");
        }
        self.generation = next_generation;
        debug_assert!(self.validate().is_ok());
        Ok(observations)
    }

    pub fn validate(&self) -> Result<(), String> {
        if self.minimum_recurrence < 2 || self.maximum_templates_per_occurrence == 0 {
            return Err("training ecology has an invalid recurrence or route aperture".to_owned());
        }
        for (fiber, recurrence) in &self.fibers {
            if *recurrence == 0 {
                return Err("training ecology contains an unobserved fiber".to_owned());
            }
            validate_template(&fiber.template)?;
            for (name, _) in &fiber.parameters {
                if name.is_empty() {
                    return Err("training ecology contains an empty receiver axis".to_owned());
                }
            }
        }
        Ok(())
    }

    pub fn active_templates(&self) -> Vec<ActiveTransduction> {
        self.fibers
            .iter()
            .filter(|(_, recurrence)| **recurrence >= self.minimum_recurrence)
            .map(|(fiber, recurrence)| ActiveTransduction {
                template: fiber.template.clone(),
                parameters: fiber.parameters.clone(),
                recurrence: *recurrence,
            })
            .collect()
    }

    pub fn active_template_count(&self) -> usize {
        self.fibers
            .values()
            .filter(|recurrence| **recurrence >= self.minimum_recurrence)
            .count()
    }

    /// Deterministic exact rest image for this application-owned ecology.
    ///
    /// The encoding carries only the current recurrent route population and its local receiver
    /// faces.  It contains no source occurrence, consequence log, prediction cache, hash identity,
    /// or wall-clock field.
    pub fn encode_native_bytes(&self) -> Result<Vec<u8>, String> {
        self.validate()?;
        let mut bytes = Vec::new();
        bytes.extend_from_slice(b"HTEC\0\0\0\x01");
        put_u64(&mut bytes, self.generation);
        put_u64(&mut bytes, self.minimum_recurrence);
        put_u64(
            &mut bytes,
            u64::try_from(self.maximum_templates_per_occurrence)
                .map_err(|_| "route aperture does not fit the exact rest carrier".to_owned())?,
        );
        put_u64(
            &mut bytes,
            u64::try_from(self.fibers.len())
                .map_err(|_| "fiber population does not fit the exact rest carrier".to_owned())?,
        );
        for (fiber, recurrence) in &self.fibers {
            put_u64(
                &mut bytes,
                u64::try_from(fiber.parameters.len()).map_err(|_| {
                    "receiver-axis population does not fit the exact rest carrier".to_owned()
                })?,
            );
            for (name, value) in &fiber.parameters {
                put_bytes(&mut bytes, name.as_bytes())?;
                put_bytes(&mut bytes, value.as_bytes())?;
            }
            put_u64(
                &mut bytes,
                u64::try_from(fiber.template.steps.len()).map_err(|_| {
                    "template extent does not fit the exact rest carrier".to_owned()
                })?,
            );
            for step in &fiber.template.steps {
                match step {
                    TemplateStep::Copy { face } => {
                        bytes.push(1);
                        put_bytes(&mut bytes, face.axis.as_bytes())?;
                        put_u64(&mut bytes, face.ordinal);
                    }
                    TemplateStep::Found { value } => {
                        bytes.push(2);
                        put_bytes(&mut bytes, value)?;
                    }
                }
            }
            put_u64(&mut bytes, *recurrence);
        }
        Ok(bytes)
    }

    pub fn decode_native_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut cursor = ByteCursor::new(bytes);
        if cursor.take(8)? != b"HTEC\0\0\0\x01" {
            return Err("training ecology rest schema changed".to_owned());
        }
        let generation = cursor.u64()?;
        let minimum_recurrence = cursor.u64()?;
        let maximum_templates_per_occurrence = usize::try_from(cursor.u64()?)
            .map_err(|_| "route aperture exceeds usize".to_owned())?;
        let fiber_count =
            usize::try_from(cursor.u64()?).map_err(|_| "fiber count exceeds usize".to_owned())?;
        let mut fibers = GrowingKeyAtlas::new();
        fibers
            .try_reserve_new_keys(fiber_count)
            .map_err(|_| "training ecology rest cannot reserve its fiber atlas".to_owned())?;
        for _ in 0..fiber_count {
            let parameter_count = usize::try_from(cursor.u64()?)
                .map_err(|_| "parameter count exceeds usize".to_owned())?;
            let mut parameters = Vec::with_capacity(parameter_count);
            for _ in 0..parameter_count {
                parameters.push((
                    cursor.utf8("receiver axis")?,
                    cursor.utf8("receiver value")?,
                ));
            }
            if parameters.windows(2).any(|pair| pair[0] >= pair[1]) {
                return Err(
                    "training ecology rest has repeated or noncanonical receiver axes".to_owned(),
                );
            }
            let step_count = usize::try_from(cursor.u64()?)
                .map_err(|_| "template step count exceeds usize".to_owned())?;
            let mut steps = Vec::with_capacity(step_count);
            for _ in 0..step_count {
                steps.push(match cursor.byte()? {
                    1 => TemplateStep::Copy {
                        face: FaceAddress {
                            axis: cursor.utf8("face axis")?,
                            ordinal: cursor.u64()?,
                        },
                    },
                    2 => TemplateStep::Found {
                        value: cursor.bytes()?,
                    },
                    tag => return Err(format!("unknown transduction step tag {tag}")),
                });
            }
            let recurrence = cursor.u64()?;
            let fiber = TransductionFiber {
                template: TransductionTemplate { steps },
                parameters,
            };
            if fibers
                .try_insert(fiber, recurrence)
                .map_err(|_| "training ecology rest cannot found its fiber atlas".to_owned())?
                .is_some()
            {
                return Err("training ecology rest repeats one exact fiber".to_owned());
            }
        }
        if !cursor.is_finished() {
            return Err("training ecology rest has trailing material".to_owned());
        }
        let ecology = Self {
            generation,
            minimum_recurrence,
            maximum_templates_per_occurrence,
            fibers,
        };
        ecology.validate()?;
        Ok(ecology)
    }

    /// Rebind every active route afforded by the contemporary face population.
    ///
    /// Receiver parameters do not assign a scalar score.  Every route at the maximal exact
    /// parameter-incidence rank remains present, including path-distinct routes with equal
    /// consequences.
    pub fn predict(
        &self,
        faces: &[SourceFace],
        parameters: &BTreeMap<String, String>,
    ) -> Result<TrainingPrediction, String> {
        let bindings = face_bindings(faces)?;
        let mut afforded = Vec::new();
        for (fiber, recurrence) in self
            .fibers
            .iter()
            .filter(|(_, recurrence)| **recurrence >= self.minimum_recurrence)
        {
            let Ok(path) = instantiate(&fiber.template, &bindings) else {
                continue;
            };
            let equal_axes = fiber
                .parameters
                .iter()
                .filter(|(name, value)| parameters.get(name) == Some(value))
                .map(|(name, _)| name.clone())
                .collect::<BTreeSet<_>>();
            afforded.push((fiber, *recurrence, equal_axes, path));
        }
        let Some(agreement_rank) = afforded
            .iter()
            .map(|(_, _, equal_axes, _)| equal_axes.len())
            .max()
        else {
            return Ok(TrainingPrediction::default());
        };

        let mut candidates = BTreeMap::<TransductionPath, CandidateTransduction>::new();
        for (fiber, recurrence, equal_axes, path) in afforded
            .into_iter()
            .filter(|(_, _, equal_axes, _)| equal_axes.len() == agreement_rank)
        {
            candidates
                .entry(path.clone())
                .or_insert_with(|| CandidateTransduction {
                    path,
                    support: Vec::new(),
                })
                .support
                .push(TransductionSupport {
                    template: fiber.template.clone(),
                    parameters: fiber.parameters.clone(),
                    equal_axes,
                    recurrence,
                });
        }
        Ok(TrainingPrediction {
            agreement_rank: Some(agreement_rank),
            candidates: candidates.into_values().collect(),
        })
    }

    /// Recruit only fibers carried by this exact receiver face.
    ///
    /// Unlike [`Self::predict`], this does not relax a conflicting axis by comparing agreement
    /// ranks.  Worlds with a lawful nested restriction order can call exact faces in that order
    /// and stop at the first nonempty one.
    pub fn predict_exact(
        &self,
        faces: &[SourceFace],
        parameters: &BTreeMap<String, String>,
    ) -> Result<TrainingPrediction, String> {
        self.predict_exact_with_minimum(faces, parameters, self.minimum_recurrence)
    }

    /// Exact receiver recruitment at a caller-declared recurrence aperture.
    ///
    /// This permits a higher ecology to found a receiver context by its total recurrence while
    /// retaining every once-observed consequence path inside that already-recurrent context.
    pub fn predict_exact_with_minimum(
        &self,
        faces: &[SourceFace],
        parameters: &BTreeMap<String, String>,
        minimum_recurrence: u64,
    ) -> Result<TrainingPrediction, String> {
        if minimum_recurrence == 0 {
            return Err("an exact receiver aperture cannot be zero".to_owned());
        }
        let bindings = face_bindings(faces)?;
        let receiver = parameters
            .iter()
            .map(|(name, value)| (name.clone(), value.clone()))
            .collect::<Vec<_>>();
        let mut candidates = BTreeMap::<TransductionPath, CandidateTransduction>::new();
        for (fiber, recurrence) in self.fibers.iter().filter(|(fiber, recurrence)| {
            **recurrence >= minimum_recurrence && fiber.parameters == receiver
        }) {
            let Ok(path) = instantiate(&fiber.template, &bindings) else {
                continue;
            };
            candidates
                .entry(path.clone())
                .or_insert_with(|| CandidateTransduction {
                    path,
                    support: Vec::new(),
                })
                .support
                .push(TransductionSupport {
                    template: fiber.template.clone(),
                    parameters: fiber.parameters.clone(),
                    equal_axes: fiber
                        .parameters
                        .iter()
                        .map(|(name, _)| name.clone())
                        .collect(),
                    recurrence: *recurrence,
                });
        }
        if candidates.is_empty() {
            Ok(TrainingPrediction::default())
        } else {
            Ok(TrainingPrediction {
                agreement_rank: Some(receiver.len()),
                candidates: candidates.into_values().collect(),
            })
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObservedTransduction {
    pub complex: ConsequenceComplex,
    pub templates: Vec<TransductionTemplate>,
    pub prior: TrainingPrediction,
    pub relation: ConsequenceRelation,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConsequenceRelation {
    /// No active route spoke at this receiver.
    None,
    /// Every afforded complete path returned the observed consequence.
    Ride,
    /// The observed consequence was one member of a plural afforded field.
    OpenIncluded,
    /// Active routes spoke, but none returned the observed consequence.
    OpenResidual,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActiveTransduction {
    pub template: TransductionTemplate,
    pub parameters: Vec<(String, String)>,
    pub recurrence: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransductionSupport {
    /// The exact recurrent route form which instantiated this candidate. Keeping the template on
    /// the returned support lets a higher ecology recover the particular training occurrences
    /// which founded the route instead of attributing every path at the same receiver to every
    /// occurrence.
    pub template: TransductionTemplate,
    pub parameters: Vec<(String, String)>,
    pub equal_axes: BTreeSet<String>,
    pub recurrence: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CandidateTransduction {
    pub path: TransductionPath,
    pub support: Vec<TransductionSupport>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TrainingPrediction {
    pub agreement_rank: Option<usize>,
    pub candidates: Vec<CandidateTransduction>,
}

impl TrainingPrediction {
    pub fn consequences(&self) -> BTreeSet<Vec<u8>> {
        self.candidates
            .iter()
            .map(|candidate| candidate.path.consequence.clone())
            .collect()
    }

    /// Exact path-population support.  Equal consequences reached by distinct paths remain
    /// distinct contributors instead of being averaged before observation.
    pub fn consequence_population(&self) -> Result<BTreeMap<Vec<u8>, u64>, String> {
        let mut population = BTreeMap::new();
        for candidate in &self.candidates {
            let support = candidate.support.iter().try_fold(0u64, |total, face| {
                total
                    .checked_add(face.recurrence)
                    .ok_or_else(|| "candidate support population overflowed".to_owned())
            })?;
            let total = population
                .entry(candidate.path.consequence.clone())
                .or_insert(0u64);
            *total = total
                .checked_add(support)
                .ok_or_else(|| "consequence path population overflowed".to_owned())?;
        }
        Ok(population)
    }

    pub fn relation_to(&self, actual: &[u8]) -> ConsequenceRelation {
        if self.candidates.is_empty() {
            return ConsequenceRelation::None;
        }
        let matching = self
            .candidates
            .iter()
            .filter(|candidate| candidate.path.consequence == actual)
            .count();
        match matching {
            0 => ConsequenceRelation::OpenResidual,
            count if count == self.candidates.len() => ConsequenceRelation::Ride,
            _ => ConsequenceRelation::OpenIncluded,
        }
    }
}

pub fn consequence_complex(
    faces: &[SourceFace],
    consequence: &[u8],
) -> Result<ConsequenceComplex, String> {
    if consequence.is_empty() {
        return Err("an empty consequence cannot found a transduction path".to_owned());
    }
    let bindings = face_bindings(faces)?;
    let mut edges = Vec::new();
    for at in 0..consequence.len() {
        edges.push(ConsequenceEdge::Found {
            from: at,
            to: at + 1,
            value: consequence[at..at + 1].to_vec(),
        });
    }
    for (address, value) in bindings {
        if value.len() > consequence.len() {
            continue;
        }
        for at in 0..=consequence.len() - value.len() {
            if consequence[at..].starts_with(&value) {
                edges.push(ConsequenceEdge::Copy {
                    from: at,
                    to: at + value.len(),
                    face: address.clone(),
                });
            }
        }
    }
    edges.sort();
    Ok(ConsequenceComplex {
        extent: consequence.len(),
        edges,
    })
}

/// Derive every complete path in a finite consequence complex.
///
/// FOUND unit edges are merged into maximal adjacent founded spans in the returned template.
/// When the physical aperture is exceeded the event refuses before mutation; no prefix of the
/// route population is retained as if it were complete.
pub fn derive_templates(
    complex: &ConsequenceComplex,
    maximum_templates: usize,
) -> Result<Vec<TransductionTemplate>, String> {
    if complex.extent == 0 || maximum_templates == 0 {
        return Err("the consequence complex or route aperture is empty".to_owned());
    }
    let mut outgoing = vec![Vec::<ConsequenceEdge>::new(); complex.extent + 1];
    for edge in &complex.edges {
        let (from, to) = edge_interval(edge);
        if from >= to || to > complex.extent {
            return Err("a consequence edge has an invalid orientation".to_owned());
        }
        outgoing[from].push(edge.clone());
    }
    for edges in &mut outgoing {
        edges.sort();
    }
    let mut templates = BTreeSet::new();
    derive_from(
        0,
        complex.extent,
        &outgoing,
        &mut Vec::new(),
        &mut templates,
        maximum_templates,
    )?;
    if templates.is_empty() {
        return Err("the consequence complex has no complete path".to_owned());
    }
    Ok(templates.into_iter().collect())
}

fn derive_from(
    at: usize,
    extent: usize,
    outgoing: &[Vec<ConsequenceEdge>],
    steps: &mut Vec<TemplateStep>,
    templates: &mut BTreeSet<TransductionTemplate>,
    maximum_templates: usize,
) -> Result<(), String> {
    if at == extent {
        let template = TransductionTemplate {
            steps: normalize_steps(steps),
        };
        validate_template(&template)?;
        templates.insert(template);
        if templates.len() > maximum_templates {
            return Err(format!(
                "the exact route population exceeded the declared physical aperture {maximum_templates}"
            ));
        }
        return Ok(());
    }
    for edge in &outgoing[at] {
        let (_, to) = edge_interval(edge);
        let step = match edge {
            ConsequenceEdge::Copy { face, .. } => TemplateStep::Copy { face: face.clone() },
            ConsequenceEdge::Found { value, .. } => TemplateStep::Found {
                value: value.clone(),
            },
        };
        steps.push(step);
        derive_from(to, extent, outgoing, steps, templates, maximum_templates)?;
        steps.pop();
    }
    Ok(())
}

pub fn instantiate(
    template: &TransductionTemplate,
    bindings: &BTreeMap<FaceAddress, Vec<u8>>,
) -> Result<TransductionPath, String> {
    validate_template(template)?;
    let mut steps = Vec::with_capacity(template.steps.len());
    let mut consequence = Vec::new();
    for step in &template.steps {
        match step {
            TemplateStep::Copy { face } => {
                let value = bindings
                    .get(face)
                    .ok_or_else(|| {
                        format!(
                            "the contemporary occurrence does not expose {}:{}",
                            face.axis, face.ordinal
                        )
                    })?
                    .clone();
                if value.is_empty() {
                    return Err("a rebound source face is empty".to_owned());
                }
                consequence.extend(&value);
                steps.push(PathStep::Copy {
                    face: face.clone(),
                    value,
                });
            }
            TemplateStep::Found { value } => {
                consequence.extend(value);
                steps.push(PathStep::Found {
                    value: value.clone(),
                });
            }
        }
    }
    let path = TransductionPath { steps, consequence };
    path.validate()?;
    Ok(path)
}

fn face_bindings(faces: &[SourceFace]) -> Result<BTreeMap<FaceAddress, Vec<u8>>, String> {
    let mut bindings = BTreeMap::new();
    for face in faces {
        validate_address(&face.address)?;
        if face.value.is_empty() {
            return Err("a source face is empty".to_owned());
        }
        if bindings
            .insert(face.address.clone(), face.value.clone())
            .is_some()
        {
            return Err(format!(
                "one occurrence repeats the local face address {}:{}",
                face.address.axis, face.address.ordinal
            ));
        }
    }
    Ok(bindings)
}

fn validate_address(address: &FaceAddress) -> Result<(), String> {
    if address.axis.is_empty() {
        Err("a face address has an empty local axis".to_owned())
    } else {
        Ok(())
    }
}

fn validate_template(template: &TransductionTemplate) -> Result<(), String> {
    if template.steps.is_empty() {
        return Err("a transduction template has no step".to_owned());
    }
    for step in &template.steps {
        match step {
            TemplateStep::Copy { face } => validate_address(face)?,
            TemplateStep::Found { value } if value.is_empty() => {
                return Err("a transduction template has an empty FOUND span".to_owned());
            }
            TemplateStep::Found { .. } => {}
        }
    }
    Ok(())
}

fn edge_interval(edge: &ConsequenceEdge) -> (usize, usize) {
    match edge {
        ConsequenceEdge::Copy { from, to, .. } | ConsequenceEdge::Found { from, to, .. } => {
            (*from, *to)
        }
    }
}

fn normalize_steps(steps: &[TemplateStep]) -> Vec<TemplateStep> {
    let mut normalized = Vec::<TemplateStep>::new();
    for step in steps {
        match step {
            TemplateStep::Found { value } => match normalized.last_mut() {
                Some(TemplateStep::Found { value: prior }) => prior.extend(value),
                _ => normalized.push(step.clone()),
            },
            TemplateStep::Copy { .. } => normalized.push(step.clone()),
        }
    }
    normalized
}

fn put_u64(bytes: &mut Vec<u8>, value: u64) {
    bytes.extend_from_slice(&value.to_le_bytes());
}

fn put_bytes(bytes: &mut Vec<u8>, value: &[u8]) -> Result<(), String> {
    put_u64(
        bytes,
        u64::try_from(value.len())
            .map_err(|_| "byte face does not fit the exact rest carrier".to_owned())?,
    );
    bytes.extend_from_slice(value);
    Ok(())
}

struct ByteCursor<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> ByteCursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, at: 0 }
    }

    fn take(&mut self, length: usize) -> Result<&'a [u8], String> {
        let end = self
            .at
            .checked_add(length)
            .ok_or_else(|| "training ecology rest cursor overflowed".to_owned())?;
        let value = self
            .bytes
            .get(self.at..end)
            .ok_or_else(|| "training ecology rest ended inside a field".to_owned())?;
        self.at = end;
        Ok(value)
    }

    fn byte(&mut self) -> Result<u8, String> {
        Ok(self.take(1)?[0])
    }

    fn u64(&mut self) -> Result<u64, String> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }

    fn bytes(&mut self) -> Result<Vec<u8>, String> {
        let length = usize::try_from(self.u64()?)
            .map_err(|_| "byte face length exceeds usize".to_owned())?;
        Ok(self.take(length)?.to_vec())
    }

    fn utf8(&mut self, field: &str) -> Result<String, String> {
        String::from_utf8(self.bytes()?)
            .map_err(|error| format!("training ecology {field} is not UTF-8: {error}"))
    }

    fn is_finished(&self) -> bool {
        self.at == self.bytes.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn face(axis: &str, value: &str) -> SourceFace {
        SourceFace::new(FaceAddress::new(axis, 0), value.as_bytes().to_vec())
    }

    fn parameters(pairs: &[(&str, &str)]) -> BTreeMap<String, String> {
        pairs
            .iter()
            .map(|(name, value)| ((*name).to_owned(), (*value).to_owned()))
            .collect()
    }

    #[test]
    fn ordinary_consequences_cultivate_text_and_code_paths_without_teacher_dags() {
        let mut ecology = TrainingEcology::new(2, 4_096).unwrap();
        for name in ["Ada", "Lin"] {
            ecology
                .cultivate(
                    &[face("subject", name)],
                    &parameters(&[("medium", "text"), ("objective", "greet")]),
                    format!("Hello, {name}!").as_bytes(),
                )
                .unwrap();
            ecology
                .cultivate(
                    &[face("subject", name)],
                    &parameters(&[
                        ("language", "python"),
                        ("medium", "code"),
                        ("objective", "emit"),
                    ]),
                    format!("print(\"{name}\")").as_bytes(),
                )
                .unwrap();
        }

        let text = ecology
            .predict(
                &[face("subject", "Mira")],
                &parameters(&[("medium", "text"), ("objective", "greet")]),
            )
            .unwrap();
        assert_eq!(
            text.consequences(),
            BTreeSet::from([b"Hello, Mira!".to_vec()])
        );

        let code = ecology
            .predict(
                &[face("subject", "Mira")],
                &parameters(&[
                    ("language", "python"),
                    ("medium", "code"),
                    ("objective", "emit"),
                ]),
            )
            .unwrap();
        assert_eq!(
            code.consequences(),
            BTreeSet::from([b"print(\"Mira\")".to_vec()])
        );
        assert!(code.candidates.iter().all(|candidate| {
            candidate
                .path
                .steps
                .iter()
                .any(|step| matches!(step, PathStep::Copy { face, .. } if face.axis == "subject"))
        }));
    }

    #[test]
    fn missing_context_preserves_complete_alternative_paths_and_exact_residual() {
        let mut ecology = TrainingEcology::new(2, 4_096).unwrap();
        for name in ["Ada", "Lin"] {
            ecology
                .cultivate(
                    &[face("subject", name)],
                    &parameters(&[("medium", "text"), ("objective", "greet")]),
                    format!("Hello, {name}!").as_bytes(),
                )
                .unwrap();
            ecology
                .cultivate(
                    &[face("subject", name)],
                    &parameters(&[("medium", "text"), ("objective", "name")]),
                    name.as_bytes(),
                )
                .unwrap();
        }
        let partial = ecology
            .predict(
                &[face("subject", "Mira")],
                &parameters(&[("medium", "text")]),
            )
            .unwrap();
        assert_eq!(partial.agreement_rank, Some(1));
        assert_eq!(
            partial.consequences(),
            BTreeSet::from([b"Hello, Mira!".to_vec(), b"Mira".to_vec()])
        );
        assert_eq!(
            partial.relation_to(b"Mira"),
            ConsequenceRelation::OpenIncluded
        );
        assert_eq!(
            partial.relation_to(b"Goodbye, Mira!"),
            ConsequenceRelation::OpenResidual
        );
    }

    #[test]
    fn cultivated_paths_compose_across_text_and_code_after_teachers_depart() {
        let mut ecology = TrainingEcology::new(2, 4_096).unwrap();
        for name in ["Ada", "Lin"] {
            let utterance = format!("Hello, {name}!");
            ecology
                .cultivate(
                    &[face("subject", name)],
                    &parameters(&[("stage", "utterance")]),
                    utterance.as_bytes(),
                )
                .unwrap();
            ecology
                .cultivate(
                    &[face("utterance", &utterance)],
                    &parameters(&[("stage", "python_emit")]),
                    format!("emit({utterance:?})").as_bytes(),
                )
                .unwrap();
        }

        let utterance = ecology
            .predict(
                &[face("subject", "Mira")],
                &parameters(&[("stage", "utterance")]),
            )
            .unwrap();
        assert_eq!(utterance.candidates.len(), 1);
        let returned = String::from_utf8(utterance.candidates[0].path.consequence.clone()).unwrap();

        let code = ecology
            .predict(
                &[face("utterance", &returned)],
                &parameters(&[("stage", "python_emit")]),
            )
            .unwrap();
        assert_eq!(
            code.consequences(),
            BTreeSet::from([b"emit(\"Hello, Mira!\")".to_vec()])
        );
    }

    #[test]
    fn path_distinct_equal_consequences_remain_plural() {
        let mut ecology = TrainingEcology::new(2, 4_096).unwrap();
        let faces = [face("left", "same"), face("right", "same")];
        ecology
            .cultivate(&faces, &parameters(&[("objective", "echo")]), b"same")
            .unwrap();
        ecology
            .cultivate(&faces, &parameters(&[("objective", "echo")]), b"same")
            .unwrap();
        let prediction = ecology
            .predict(&faces, &parameters(&[("objective", "echo")]))
            .unwrap();
        let equal = prediction
            .candidates
            .iter()
            .filter(|candidate| candidate.path.consequence == b"same")
            .count();
        assert_eq!(equal, 3);
        assert_eq!(prediction.relation_to(b"same"), ConsequenceRelation::Ride);
    }

    #[test]
    fn route_aperture_refuses_without_truncating_the_event() {
        let mut ecology = TrainingEcology::new(2, 1).unwrap();
        let before = ecology.encode_native_bytes().unwrap();
        let error = ecology
            .cultivate(
                &[face("left", "x"), face("right", "x")],
                &BTreeMap::new(),
                b"x",
            )
            .unwrap_err();
        assert!(error.contains("physical aperture"));
        assert_eq!(ecology.encode_native_bytes().unwrap(), before);
    }

    #[test]
    fn exact_rest_carries_only_the_current_route_population() {
        let mut ecology = TrainingEcology::new(2, 4_096).unwrap();
        for name in ["Ada", "Lin"] {
            ecology
                .cultivate(
                    &[face("subject", name)],
                    &parameters(&[("objective", "greet")]),
                    format!("Hello, {name}!").as_bytes(),
                )
                .unwrap();
        }
        let bytes = ecology.encode_native_bytes().unwrap();
        let remounted = TrainingEcology::decode_native_bytes(&bytes).unwrap();
        assert_eq!(remounted, ecology);
        assert_eq!(remounted.encode_native_bytes().unwrap(), bytes);
        assert_eq!(
            remounted
                .predict(
                    &[face("subject", "Mira")],
                    &parameters(&[("objective", "greet")]),
                )
                .unwrap()
                .consequences(),
            BTreeSet::from([b"Hello, Mira!".to_vec()])
        );
    }

    #[test]
    fn co_present_receiver_views_advance_one_generation_and_do_not_relax_exact_axes() {
        let mut ecology = TrainingEcology::new(2, 4_096).unwrap();
        let views = |value: &str| {
            vec![
                TrainingView {
                    faces: vec![face("prior", value)],
                    parameters: parameters(&[("horizon", "1"), ("suffix", value)]),
                },
                TrainingView {
                    faces: Vec::new(),
                    parameters: parameters(&[("horizon", "0"), ("suffix", "")]),
                },
            ]
        };
        ecology.cultivate_views(&views("red"), b"fox").unwrap();
        ecology.cultivate_views(&views("blue"), b"fox").unwrap();
        assert_eq!(ecology.generation, 2);

        let exact_red = ecology
            .predict_exact(
                &[face("prior", "red")],
                &parameters(&[("horizon", "1"), ("suffix", "red")]),
            )
            .unwrap();
        assert!(exact_red.candidates.is_empty());

        let exact_zero = ecology
            .predict_exact(&[], &parameters(&[("horizon", "0"), ("suffix", "")]))
            .unwrap();
        assert_eq!(exact_zero.consequences(), BTreeSet::from([b"fox".to_vec()]));
    }

    #[test]
    fn duplicate_co_present_view_refuses_before_mutation() {
        let mut ecology = TrainingEcology::new(2, 4_096).unwrap();
        let view = TrainingView {
            faces: vec![face("prior", "x")],
            parameters: parameters(&[("horizon", "1")]),
        };
        let before = ecology.encode_native_bytes().unwrap();
        assert!(ecology
            .cultivate_views(&[view.clone(), view], b"x")
            .is_err());
        assert_eq!(ecology.encode_native_bytes().unwrap(), before);
    }

    #[test]
    fn a_stale_training_delta_is_returned_intact_without_changing_standing() {
        let mut ecology = TrainingEcology::new(2, 4_096).unwrap();
        let proposal = ecology
            .propose_views(
                &[TrainingView {
                    faces: vec![face("prior", "Ada")],
                    parameters: parameters(&[("horizon", "1")]),
                }],
                b"Hello, Ada!",
            )
            .unwrap();
        ecology
            .cultivate(
                &[face("prior", "Lin")],
                &parameters(&[("horizon", "1")]),
                b"Hello, Lin!",
            )
            .unwrap();
        let standing = ecology.encode_native_bytes().unwrap();

        let refusal = ecology.commit_views(proposal).unwrap_err();
        assert!(refusal.error.contains("changed before"));
        assert_eq!(refusal.proposal.observations().len(), 1);
        assert_eq!(ecology.encode_native_bytes().unwrap(), standing);
    }

    #[test]
    fn distinct_co_present_views_cannot_multiply_one_equal_receiver_fiber() {
        let mut ecology = TrainingEcology::new(2, 4_096).unwrap();
        let parameters = parameters(&[("horizon", "1")]);
        ecology
            .cultivate_views(
                &[
                    TrainingView {
                        faces: vec![face("prior", "x")],
                        parameters: parameters.clone(),
                    },
                    TrainingView {
                        faces: vec![face("prior", "y")],
                        parameters,
                    },
                ],
                b"z",
            )
            .unwrap();
        assert_eq!(ecology.generation, 1);
        assert_eq!(ecology.fibers.len(), 1);
        assert_eq!(ecology.fibers.values().copied().collect::<Vec<_>>(), [1]);
    }
}
