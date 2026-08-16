use super::*;
use super::{codec::*, transport::*, types::*};

/// A bounded inherited English clause transducer plus the exact relation cells it received.
pub struct ExactRelationalLanguageEcology {
    pub(super) clauses: LocalSequence<RelationalClause>,
    /// Stable causal-incidence neighborhood. New returned clauses compare only with standing
    /// clauses; a later question traverses the carried topology rather than rescanning all pairs.
    pub(super) adjacency: LocalSequence<LocalSet<usize>>,
    /// Persistent local aperture from an exact constituent face to the clauses which physically
    /// carry it. Query current enters through this aperture instead of scanning every clause.
    pub(super) face_incidence: LocalRelations<String, LocalSet<usize>>,
    /// Complete nominal faces and caused output faces restrict structural contact before any
    /// occurrence pair is inspected. Constituent-token incidence remains query-only.
    pub(super) entity_incidence: LocalRelations<BTreeSet<String>, LocalSet<usize>>,
    pub(super) output_incidence: LocalRelations<BTreeSet<String>, LocalSet<usize>>,
    pub(super) relation_incidence: LocalRelations<String, LocalSet<usize>>,
    pub(super) passage_incidence: LocalRelations<String, LocalSet<usize>>,
    pub(super) junction_phases: LocalRelations<(usize, usize), RelationalJunctionPhase>,
    /// Exact occurrence-bound return for each structural pair. Equal phases never widen one
    /// returned conduct witness across another candidate edge.
    pub(super) junction_returns: LocalRelations<(usize, usize), ResonanceOccurrenceRead>,
    /// One continuing production Swing organ carries every receiver-local junction current.
    /// A phase identifies a current fiber inside this organ; it never owns another live world.
    pub(super) association: ResonanceEcology,
    pub(super) next_association_order: u64,
    pub(super) pending_junctions: LocalQueue<PendingRelationalJunction>,
    pub(super) pending_morphology_capacity: LocalSet<RelationalClauseMorphology>,
    pub(super) open_passage: Option<OpenRelationalPassage>,
    pub(super) requested_worker_threads: usize,
    /// Shared exact population-current owner. The language ecology supplies caused sites,
    /// passages, and recurrent capacities; it does not privately redefine traversal.
    pub(super) receiver_current: ExactReceiverCurrentLaw,
    pub(super) current_passages: LocalRelations<(usize, usize), [ReceiverCurrentPassageId; 2]>,
    pub(super) pending_current_passages: LocalRelations<(usize, usize), PendingReceiverCurrentPair>,
    pub(super) next_current_passage: u64,
    pub(super) morphology_sites: LocalRelations<RelationalClauseMorphology, LocalSet<usize>>,
    pub(super) parse_fibers: LocalSequence<RelationalParseFiber>,
    pub(super) inherited_surfaces: LocalSequence<Vec<String>>,
    pub(super) predicate_lexicon: LocalSet<String>,
    pub(super) passage_identities: GrowingKeyAtlas<String, RelationalPassageStanding>,
    pub(super) next_passage_order: u64,
    /// Which term plays a promoted clause pair's characteristic delay. `Uniform` is the frame every
    /// reading before 2026-08-10 was taken in, and it stays the default so no standing reading
    /// silently moves; `SourceContinuity` is the second frame that makes any of them falsifiable.
    pub(super) characteristic_delay_law: ClausePairDelayLaw,
}

/// What plays a promoted clause pair's positive characteristic delay.
///
/// This exists because `characteristic_delay: 1` was pinned at both promotion sites, and a level
/// pinned by its only caller rather than by its law is `CLAUDE.md` §8's authored level: *"we are
/// not the ones meant to be pinning levels to minimums and maximums."* Two frames is the minimum
/// at which a delay reading can be checked at all.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub enum ClausePairDelayLaw {
    /// Every promoted pair carries delay one.
    #[default]
    Uniform,
    /// One plus the separation between the two clauses' serial positions on their source's clause
    /// strand; across sources, one plus the extent of the strand being left.
    SourceContinuity,
}

impl fmt::Debug for ExactRelationalLanguageEcology {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ExactRelationalLanguageEcology")
            .field("clauses", &self.clauses.len())
            .field("conducting_channels", &self.current_passages.len())
            .field("returned_junctions", &self.junction_returns.len())
            .field("association_memory", &self.association.machine().memory())
            .field("pending_junctions", &self.pending_junctions.len())
            .field("parse_fibers", &self.parse_fibers.len())
            .finish_non_exhaustive()
    }
}

impl ExactRelationalLanguageEcology {
    pub fn condition(
        passages: &[MorphologicalLanguagePassage],
    ) -> Result<Self, RelationalLanguageError> {
        Self::condition_with_workers(passages, 1)
    }

    /// Condition one plural-current relation organ.
    ///
    /// `worker_threads` is an apparatus aperture, not a declaration that semantic currents
    /// commute. The shared Swing successor retains its owner-native order; unproved independence
    /// remains open.
    pub fn condition_with_workers(
        passages: &[MorphologicalLanguagePassage],
        worker_threads: usize,
    ) -> Result<Self, RelationalLanguageError> {
        let mut host = ParallelHostLiveCurrentExecutor::new(worker_threads.max(1));
        Self::condition_with_executor(passages, worker_threads, &mut host)
    }

    /// Condition one organ under a declared clause-pair delay law.
    ///
    /// Pairs are promoted **during** conditioning, and a promoted pair refuses a conflicting
    /// re-founding, so the law has to be declared before the material arrives. This is the
    /// constructor a caller comparing two frames uses; there is no way to move a standing organ
    /// from one frame to the other, and there should not be.
    pub fn condition_with_delay_law(
        passages: &[MorphologicalLanguagePassage],
        worker_threads: usize,
        law: ClausePairDelayLaw,
    ) -> Result<Self, RelationalLanguageError> {
        if passages.is_empty() {
            return Err(RelationalLanguageError::EmptyEcology);
        }
        let mut host = ParallelHostLiveCurrentExecutor::new(worker_threads.max(1));
        let mut ecology = Self::empty(worker_threads)?;
        ecology.characteristic_delay_law = law;
        ecology.receive_with_executor(passages, worker_threads, &mut host)?;
        Ok(ecology)
    }

    /// Condition one same-predecessor passage front. Administrative member order remains stable;
    /// plurality here makes no claim of complete-successor commutation.
    pub fn condition_copresent_with_workers(
        passages: &[MorphologicalLanguagePassage],
        worker_threads: usize,
    ) -> Result<Self, RelationalLanguageError> {
        if passages.is_empty() {
            return Err(RelationalLanguageError::EmptyEcology);
        }
        let mut host = ParallelHostLiveCurrentExecutor::new(worker_threads.max(1));
        let mut ecology = Self::empty(worker_threads)?;
        ecology.receive_copresent_with_executor(passages, worker_threads, &mut host)?;
        Ok(ecology)
    }

    /// Condition through one caller-retained physical executor. The executor crosses every Swing
    /// event in this organ; selecting a card at the outer language boundary cannot silently
    /// construct a private host executor here.
    pub fn condition_with_executor(
        passages: &[MorphologicalLanguagePassage],
        worker_threads: usize,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<Self, RelationalLanguageError> {
        if passages.is_empty() {
            return Err(RelationalLanguageError::EmptyEcology);
        }
        let mut ecology = Self::empty(worker_threads)?;
        ecology.receive_with_executor(passages, worker_threads, executor)?;
        Ok(ecology)
    }

    fn empty(worker_threads: usize) -> Result<Self, RelationalLanguageError> {
        Ok(Self {
            clauses: LocalSequence::new(),
            adjacency: LocalSequence::new(),
            face_incidence: LocalRelations::new(),
            entity_incidence: LocalRelations::new(),
            output_incidence: LocalRelations::new(),
            relation_incidence: LocalRelations::new(),
            passage_incidence: LocalRelations::new(),
            junction_phases: LocalRelations::new(),
            junction_returns: LocalRelations::new(),
            association: empty_relational_association()?,
            next_association_order: 1,
            pending_junctions: LocalQueue::new(),
            pending_morphology_capacity: LocalSet::new(),
            open_passage: None,
            requested_worker_threads: worker_threads.max(1),
            receiver_current: ExactReceiverCurrentLaw::new(),
            current_passages: LocalRelations::new(),
            pending_current_passages: LocalRelations::new(),
            next_current_passage: 1,
            morphology_sites: LocalRelations::new(),
            parse_fibers: LocalSequence::new(),
            inherited_surfaces: LocalSequence::new(),
            predicate_lexicon: inherited_predicate_lexicon(),
            passage_identities: GrowingKeyAtlas::new(),
            next_passage_order: 0,
            characteristic_delay_law: ClausePairDelayLaw::default(),
        })
    }

    /// Condition the already-mounted relational body with later caused passages.
    ///
    /// Passage identity is causal identity.  Re-receiving the same occurrence is an exact no-op;
    /// a later occurrence with a different identity remains a distinct recurrence even when its
    /// visible sentence happens to be equal.
    pub fn receive(
        &mut self,
        passages: &[MorphologicalLanguagePassage],
    ) -> Result<usize, RelationalLanguageError> {
        self.receive_with_workers(passages, 1)
    }

    pub fn receive_with_workers(
        &mut self,
        passages: &[MorphologicalLanguagePassage],
        worker_threads: usize,
    ) -> Result<usize, RelationalLanguageError> {
        let mut host = ParallelHostLiveCurrentExecutor::new(worker_threads.max(1));
        self.receive_with_executor(passages, worker_threads, &mut host)
    }

    pub fn receive_copresent_with_workers(
        &mut self,
        passages: &[MorphologicalLanguagePassage],
        worker_threads: usize,
    ) -> Result<usize, RelationalLanguageError> {
        let mut host = ParallelHostLiveCurrentExecutor::new(worker_threads.max(1));
        self.receive_copresent_with_executor(passages, worker_threads, &mut host)
    }

    /// Receive passages in their supplied causal order and cross every junction through the
    /// caller's physical executor. A failed junction remains the open front of the already-caused
    /// passage; it is resumed before any later passage is admitted and is never replayed after a
    /// successful Swing return.
    pub fn receive_with_executor(
        &mut self,
        passages: &[MorphologicalLanguagePassage],
        worker_threads: usize,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<usize, RelationalLanguageError> {
        self.requested_worker_threads = worker_threads.max(1);
        self.return_open_passage(executor)?;

        // Parsing is exposure against immutable delivered occurrences. Every proposal can be
        // formed on its own CPU thread before ordered commits begin; malformed or duplicate
        // members are still interpreted in supplied chronology below and never partly enter
        // standing. The continuing relation morphology itself remains singularly owned.
        let proposal_executor = self.thought_cpu_executor();
        let (proposals, proposal_execution) = proposal_executor
            .execute_indexed(passages, |_passage_at, passage| {
                Ok::<_, RelationalLanguageError>(propose_relational_passage(passage))
            })
            .map_err(relational_cpu_error)?;
        if std::env::var_os("EROS_TRACE").is_some() {
            eprintln!(
                "eros-trace relational exposure tasks={} workers={} batches={} joins={}",
                proposal_execution.tasks,
                proposal_execution.workers_used,
                proposal_execution.batches,
                proposal_execution.joins
            );
        }

        for (passage, proposal) in passages.iter().zip(proposals) {
            if self.passage_identities.contains(&passage.identity) {
                continue;
            }
            let proposal = proposal?;
            let delivery_order = self.next_passage_order;
            let next_delivery_order = delivery_order
                .checked_add(1)
                .ok_or(RelationalLanguageError::CarrierExtent)?;
            self.open_passage = Some(OpenRelationalPassage {
                identity: Some(passage.identity.to_owned()),
                delivery_order,
                proposal: Some(proposal),
                first_new_clause: None,
                next_current_site: 0,
                candidates: None,
                junctions_queued: false,
                defer_junctions: false,
            });
            self.next_passage_order = next_delivery_order;
            self.return_open_passage(executor)?;
        }

        self.acknowledge_completed_passages(passages)
    }

    /// Receive one same-predecessor passage front. Parsing and structural ingress preserve the
    /// stable source identity, but no member is acknowledged before the complete front has crossed
    /// the typed-incidence Swing return. A refusal retains incomplete passage standings, assigned
    /// front chronologies, and the exact pending junction front for retry.
    pub fn receive_copresent_with_executor(
        &mut self,
        passages: &[MorphologicalLanguagePassage],
        worker_threads: usize,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<usize, RelationalLanguageError> {
        self.requested_worker_threads = worker_threads.max(1);
        self.return_open_passage(executor)?;
        self.return_pending_junctions(executor)?;
        self.complete_deferred_passages(passages)?;

        // A co-present slice has no administrative chronology. Canonical source occurrence
        // identity addresses parsing and later structural ingress, so reversing the caller's
        // slice cannot rewrite clause or Swing lineage.
        let mut passage_order = LocalSequence::from_iter(0..passages.len());
        passage_order
            .sort_by(|left, right| passages[*left].identity.cmp(&passages[*right].identity));
        let proposal_executor = self.thought_cpu_executor();
        let (proposals, proposal_execution) = proposal_executor
            .execute_indexed(&passage_order, |_passage_at, source_at| {
                Ok::<_, RelationalLanguageError>(propose_relational_passage(&passages[*source_at]))
            })
            .map_err(relational_cpu_error)?;
        if std::env::var_os("EROS_TRACE").is_some() {
            eprintln!(
                "eros-trace relational co-present exposure tasks={} workers={} batches={} joins={}",
                proposal_execution.tasks,
                proposal_execution.workers_used,
                proposal_execution.batches,
                proposal_execution.joins
            );
        }

        for (source_at, proposal) in passage_order.iter().zip(proposals) {
            let passage = &passages[*source_at];
            if self.passage_identities.contains(&passage.identity) {
                continue;
            }
            let proposal = proposal?;
            let delivery_order = self.next_passage_order;
            let next_delivery_order = delivery_order
                .checked_add(1)
                .ok_or(RelationalLanguageError::CarrierExtent)?;
            self.open_passage = Some(OpenRelationalPassage {
                identity: Some(passage.identity.to_owned()),
                delivery_order,
                proposal: Some(proposal),
                first_new_clause: None,
                next_current_site: 0,
                candidates: None,
                junctions_queued: false,
                defer_junctions: true,
            });
            self.next_passage_order = next_delivery_order;
            self.return_open_passage(executor)?;
        }

        self.return_pending_junctions(executor)?;
        self.complete_deferred_passages(passages)?;
        self.acknowledge_completed_passages(passages)
    }

    /// Resume the single caused passage currently crossing this relation body.
    ///
    /// The open owner is moved out while it advances and restored on every recoverable refusal.
    /// Successful clause, site, incidence, queue, direct-contact, and Swing stages therefore stay
    /// in standing and are not reconstructed from source on retry.
    fn return_open_passage(
        &mut self,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<(), RelationalLanguageError> {
        let Some(mut open) = self.open_passage.take() else {
            return self.return_pending_junctions(executor);
        };
        if let Err(error) = self.advance_open_passage(&mut open, executor) {
            self.open_passage = Some(open);
            return Err(error);
        }

        let Some(identity) = open.identity.take() else {
            self.open_passage = Some(open);
            return Err(RelationalLanguageError::CarrierExtent);
        };
        if self.passage_identities.contains(&identity) {
            open.identity = Some(identity);
            self.open_passage = Some(open);
            return Err(RelationalLanguageError::CarrierExtent);
        }
        let standing = RelationalPassageStanding {
            delivery_order: open.delivery_order,
            complete: !open.defer_junctions,
            acknowledged: false,
        };
        match self
            .passage_identities
            .try_insert_recover(identity, standing)
        {
            Ok(None) => Ok(()),
            Ok(Some(_)) => unreachable!("a uniquely checked passage identity cannot replace"),
            Err((_, identity, _)) => {
                open.identity = Some(identity);
                self.open_passage = Some(open);
                Err(RelationalLanguageError::CarrierExtent)
            }
        }
    }

    fn advance_open_passage(
        &mut self,
        open: &mut OpenRelationalPassage,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<(), RelationalLanguageError> {
        if open.first_new_clause.is_none() {
            let proposal = open
                .proposal
                .take()
                .ok_or(RelationalLanguageError::CarrierExtent)?;
            let first_new_clause = self.clauses.len();
            self.inherited_surfaces.extend(proposal.surfaces);
            self.predicate_lexicon.extend(proposal.predicates);
            self.clauses.extend(proposal.clauses);
            self.parse_fibers.extend(proposal.parse_fibers);
            open.first_new_clause = Some(first_new_clause);
            open.next_current_site = first_new_clause;
        }

        while open.next_current_site < self.clauses.len() {
            self.found_receiver_current_site(open.next_current_site, open.defer_junctions)?;
            open.next_current_site = open
                .next_current_site
                .checked_add(1)
                .ok_or(RelationalLanguageError::CarrierExtent)?;
        }

        if !open.junctions_queued && open.candidates.is_none() {
            let first_new_clause = open
                .first_new_clause
                .ok_or(RelationalLanguageError::CarrierExtent)?;
            open.candidates = Some(extend_relation_incidence(
                &self.clauses,
                &mut self.adjacency,
                &mut self.face_incidence,
                &mut self.entity_incidence,
                &mut self.output_incidence,
                &mut self.relation_incidence,
                &mut self.passage_incidence,
                &mut self.junction_phases,
                first_new_clause,
            ));
        }

        if !open.junctions_queued {
            let candidates = open
                .candidates
                .as_ref()
                .ok_or(RelationalLanguageError::CarrierExtent)?;
            self.pending_junctions
                .try_reserve_additional(candidates.len())
                .map_err(|_| RelationalLanguageError::CarrierExtent)?;
            let candidates = open
                .candidates
                .take()
                .ok_or(RelationalLanguageError::CarrierExtent)?;
            for candidate in candidates {
                self.pending_junctions.push_back(PendingRelationalJunction {
                    candidate,
                    direct_contact_returned: false,
                    swing_returned: None,
                });
            }
            open.junctions_queued = true;
        }

        if open.defer_junctions {
            Ok(())
        } else {
            self.return_pending_junctions(executor)
        }
    }

    fn complete_deferred_passages(
        &mut self,
        passages: &[MorphologicalLanguagePassage],
    ) -> Result<(), RelationalLanguageError> {
        if !self.pending_junctions.is_empty() || !self.pending_morphology_capacity.is_empty() {
            return Err(RelationalLanguageError::OpenPassage);
        }
        for passage in passages {
            if let Some(standing) = self.passage_identities.get_mut(&passage.identity) {
                standing.complete = true;
            }
        }
        Ok(())
    }

    /// Found or finish one receiver-current site without replaying a site which crossed before a
    /// later capacity update was refused.
    fn found_receiver_current_site(
        &mut self,
        clause_at: usize,
        defer_capacity: bool,
    ) -> Result<(), RelationalLanguageError> {
        let site_id = clause_site(clause_at)?;
        if self.receiver_current.site(site_id).is_none() {
            self.receiver_current
                .found_site(site_id, BigUint::from(1_u8))?;
        }
        let morphology = relational_clause_morphology(&self.clauses[clause_at]);
        if self.morphology_sites.get(&morphology).is_none() {
            self.morphology_sites
                .insert(morphology.to_owned(), LocalSet::new());
        }
        let sites = self
            .morphology_sites
            .get_mut(&morphology)
            .expect("the morphology site family was founded above");
        sites.insert(clause_at);
        if defer_capacity {
            self.pending_morphology_capacity.insert(morphology);
            return Ok(());
        }
        let capacity = BigUint::from(sites.len());
        for site in sites.iter().copied() {
            self.receiver_current
                .set_site_capacity(clause_site(site)?, capacity.clone())?;
        }
        Ok(())
    }

    fn settle_pending_morphology_capacities(&mut self) -> Result<(), RelationalLanguageError> {
        let morphologies = core::mem::take(&mut self.pending_morphology_capacity);
        let settled = (|| -> Result<(), RelationalLanguageError> {
            for morphology in &morphologies {
                let sites = self
                    .morphology_sites
                    .get(morphology)
                    .ok_or(RelationalLanguageError::CarrierExtent)?;
                let capacity = BigUint::from(sites.len());
                for site in sites.iter().copied() {
                    self.receiver_current
                        .set_site_capacity(clause_site(site)?, capacity.to_owned())?;
                }
            }
            Ok(())
        })();
        if let Err(error) = settled {
            self.pending_morphology_capacity.extend(morphologies);
            return Err(error);
        }
        Ok(())
    }

    fn return_pending_junctions(
        &mut self,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<(), RelationalLanguageError> {
        let action =
            ActionCurrent::new(Cog::lit(1)).ok_or(RelationalLanguageError::CarrierExtent)?;
        let mut pending = LocalSequence::with_capacity(self.pending_junctions.len());
        while let Some(member) = self.pending_junctions.pop_front() {
            pending.push(member);
        }
        if pending.is_empty() {
            self.settle_pending_morphology_capacities()?;
            return Ok(());
        }

        let returned = (|| -> Result<(), RelationalLanguageError> {
            for member in &mut pending {
                if !member.direct_contact_returned
                    && (self.clauses[member.candidate.left].passage
                        == self.clauses[member.candidate.right].passage
                        || clauses_have_exact_caused_contact(
                            &self.clauses[member.candidate.left],
                            &self.clauses[member.candidate.right],
                        ))
                {
                    self.promote_conducting_pair(member.candidate.left, member.candidate.right)?;
                }
                member.direct_contact_returned = true;
            }

            let configuration_order = self.next_association_order;
            let mut occurrences = LocalSequence::<ResonanceOccurrence>::new();
            let mut expected_returns = LocalSequence::new();
            for (member_at, member) in pending.iter().enumerate() {
                if member.swing_returned.is_none() {
                    let occurrence = relational_junction_candidate_occurrence(
                        &member.candidate,
                        &self.clauses,
                        configuration_order,
                    )?;
                    let identity = occurrence
                        .identity()
                        .cloned()
                        .ok_or(RelationalLanguageError::CarrierExtent)?;
                    expected_returns.push((member_at, identity));
                    occurrences.push(occurrence);
                }
            }
            crate::laboratory_language::eros_trace(
                "junctions.drain",
                &format_args!(
                    "pending {} occurrences {} clauses {}",
                    pending.len(),
                    occurrences.len(),
                    self.clauses.len()
                ),
            );
            let drain_began = std::time::Instant::now();
            if !occurrences.is_empty() {
                let next_association_order = configuration_order
                    .checked_add(RELATIONAL_SWING_OCCURRENCE_SPAN)
                    .ok_or(RelationalLanguageError::CarrierExtent)?;
                self.junction_returns
                    .try_reserve_additional(expected_returns.len())
                    .map_err(|_| RelationalLanguageError::CarrierExtent)?;
                let radiation =
                    self.association
                        .receive_configuration_with(&occurrences, action, executor)?;
                assert_eq!(
                    radiation.reads().len(),
                    expected_returns.len(),
                    "the admitted Swing configuration must return every candidate occurrence"
                );
                for (member_at, identity) in expected_returns {
                    let returned = radiation
                        .reads()
                        .iter()
                        .find(|returned| returned.occurrence() == Some(&identity))
                        .cloned()
                        .expect("the lower owner binds every return to its exact occurrence");
                    let key = ordered_clause_pair(
                        pending[member_at].candidate.left,
                        pending[member_at].candidate.right,
                    );
                    self.junction_returns
                        .try_insert(key, returned.clone())
                        .expect("the exact pair-return population was pre-reserved");
                    pending[member_at].swing_returned = Some(returned);
                }
                self.next_association_order = next_association_order;
                crate::laboratory_language::eros_trace(
                    "junctions.swing",
                    &format_args!("in {} ms", drain_began.elapsed().as_millis()),
                );
            }

            for member in &pending {
                if !matches!(
                    member
                        .swing_returned
                        .as_ref()
                        .map(ResonanceOccurrenceRead::conduct),
                    Some(ResonanceOccurrenceConduct::Complete { .. })
                ) {
                    continue;
                }
                self.promote_conducting_pair(member.candidate.left, member.candidate.right)?;
            }
            crate::laboratory_language::eros_trace(
                "junctions.promoted",
                &format_args!("in {} ms", drain_began.elapsed().as_millis()),
            );
            self.settle_pending_morphology_capacities()?;
            crate::laboratory_language::eros_trace(
                "junctions.settled",
                &format_args!("in {} ms", drain_began.elapsed().as_millis()),
            );
            Ok(())
        })();
        if let Err(error) = returned {
            for member in pending {
                self.pending_junctions.push_back(member);
            }
            return Err(error);
        }
        Ok(())
    }

    fn acknowledge_completed_passages(
        &mut self,
        passages: &[MorphologicalLanguagePassage],
    ) -> Result<usize, RelationalLanguageError> {
        let mut received = 0usize;
        for passage in passages {
            let Some(standing) = self.passage_identities.get_mut(&passage.identity) else {
                continue;
            };
            if standing.complete && !standing.acknowledged {
                standing.acknowledged = true;
                received = received
                    .checked_add(1)
                    .ok_or(RelationalLanguageError::CarrierExtent)?;
            }
        }
        Ok(received)
    }

    /// What plays a promoted clause pair's positive characteristic delay.
    ///
    /// `ExactReceiverCurrentLaw` accepts any positive `u64` and refuses zero; this ecology — its
    /// only caller — pinned **1** on both directions of every promoted pair, so every reading ever
    /// taken through `receiver_current` was taken in the uniform frame and no other frame existed
    /// to compare it against.
    ///
    /// `derivation_capacitance::CharacteristicDelayLaw::SourceContinuity` supplies the engine-side
    /// term, but it separates *deposited source lines*, and a clause pair has no lines. The
    /// clause's own continuity coordinate is `source_local_step`: its serial position on its
    /// source's clause strand, which the transducer already retains and which no receiver assigned.
    pub const fn characteristic_delay_law(&self) -> ClausePairDelayLaw {
        self.characteristic_delay_law
    }

    /// Declare which term plays the characteristic delay of pairs promoted after this call.
    ///
    /// Existing passages are left standing: a promoted pair is founded once and refuses a
    /// conflicting re-founding, so changing the law cannot silently rewrite conducted history.
    /// A caller comparing two frames promotes under each from its own ecology.
    pub fn set_characteristic_delay_law(&mut self, law: ClausePairDelayLaw) {
        self.characteristic_delay_law = law;
    }

    /// The delay this pair carries under the declared law, in the declared direction.
    ///
    /// Under [`ClausePairDelayLaw::SourceContinuity`] two clauses on the same source strand are
    /// separated by their own serial positions, so a pair the source states adjacently conducts
    /// faster than a pair it states far apart. Two clauses from **different** sources have no
    /// separation defined in the material at all — nothing in either source measures the distance
    /// to the other — so they are typed as discontinuous and carry the strand's own extent rather
    /// than an authored penalty: crossing sources costs at least as much as traversing the whole
    /// strand you are leaving.
    pub(super) fn pair_characteristic_delay(
        &self,
        from: usize,
        to: usize,
    ) -> Result<u64, RelationalLanguageError> {
        match self.characteristic_delay_law {
            ClausePairDelayLaw::Uniform => Ok(1),
            ClausePairDelayLaw::SourceContinuity => {
                let departing = self
                    .clauses
                    .get(from)
                    .ok_or(RelationalLanguageError::CarrierExtent)?;
                let arriving = self
                    .clauses
                    .get(to)
                    .ok_or(RelationalLanguageError::CarrierExtent)?;
                let separation = if departing.source == arriving.source {
                    departing
                        .source_local_step
                        .abs_diff(arriving.source_local_step)
                } else {
                    // The extent of the strand being left, read off the material.
                    self.clauses
                        .iter()
                        .filter(|clause| clause.source == departing.source)
                        .map(|clause| clause.source_local_step)
                        .max()
                        .unwrap_or(0)
                };
                separation
                    .checked_add(1)
                    .ok_or(RelationalLanguageError::CarrierExtent)
            }
        }
    }

    pub(super) fn promote_conducting_pair(
        &mut self,
        left: usize,
        right: usize,
    ) -> Result<(), RelationalLanguageError> {
        let key = ordered_clause_pair(left, right);
        if self.current_passages.contains(&key) {
            return Ok(());
        }
        let [forward, reverse] = self.prepare_current_pair(key)?;
        let left_site = clause_site(left)?;
        let right_site = clause_site(right)?;
        let forward_passage = ExactReceiverCurrentPassage {
            id: forward,
            from: left_site,
            to: right_site,
            characteristic_delay: self.pair_characteristic_delay(left, right)?,
        };
        match self.receiver_current.passage(forward) {
            Some(standing) if standing != &forward_passage => {
                return Err(RelationalLanguageError::CarrierExtent);
            }
            Some(_) => {}
            None => self.receiver_current.found_passage(forward_passage)?,
        }
        let reverse_passage = ExactReceiverCurrentPassage {
            id: reverse,
            from: right_site,
            to: left_site,
            // Computed in the reverse direction rather than copied. Under source continuity within
            // one strand the separation is symmetric, but across strands it is NOT: the extent of
            // the strand you leave is not the extent of the one you leave from the other side.
            characteristic_delay: self.pair_characteristic_delay(right, left)?,
        };
        match self.receiver_current.passage(reverse) {
            Some(standing) if standing != &reverse_passage => {
                return Err(RelationalLanguageError::CarrierExtent);
            }
            Some(_) => {}
            None => self.receiver_current.found_passage(reverse_passage)?,
        }
        self.current_passages.insert(key, [forward, reverse]);
        self.pending_current_passages.remove(&key);
        Ok(())
    }

    /// Allocate one paired receiver-current identity exactly once. If one direction returns and
    /// the other is refused, the pair remains here and retry reuses the same causal letters.
    pub(super) fn prepare_current_pair(
        &mut self,
        key: (usize, usize),
    ) -> Result<[ReceiverCurrentPassageId; 2], RelationalLanguageError> {
        if let Some(pending) = self.pending_current_passages.get(&key) {
            return Ok(pending.passages);
        }
        let forward = ReceiverCurrentPassageId(self.next_current_passage);
        let reverse = ReceiverCurrentPassageId(
            self.next_current_passage
                .checked_add(1)
                .ok_or(RelationalLanguageError::CarrierExtent)?,
        );
        let next_current_passage = self
            .next_current_passage
            .checked_add(2)
            .ok_or(RelationalLanguageError::CarrierExtent)?;
        if self
            .pending_current_passages
            .try_insert(
                key,
                PendingReceiverCurrentPair {
                    passages: [forward, reverse],
                },
            )
            .map_err(|_| RelationalLanguageError::CarrierExtent)?
            .is_some()
        {
            return Err(RelationalLanguageError::CarrierExtent);
        }
        self.next_current_passage = next_current_passage;
        Ok([forward, reverse])
    }

    pub fn clauses(&self) -> &[RelationalClause] {
        &self.clauses
    }

    pub fn parse_fibers(&self) -> &[RelationalParseFiber] {
        &self.parse_fibers
    }

    /// Inspect the physical body actually owned by this ecology. This receipt distinguishes the
    /// requested worker aperture from the retained Swing configuration and reports the machine's
    /// measured standing/lineage population. Worker width does not manufacture causal topology.
    pub fn execution_receipt(&self) -> RelationalExecutionReceipt {
        let mut phases = LocalSet::new();
        for (_, phase) in self.junction_phases.iter() {
            phases.insert(phase.clone());
        }
        RelationalExecutionReceipt {
            requested_worker_threads: self.requested_worker_threads,
            clauses: self.clauses.len(),
            structural_junctions: self.junction_phases.len(),
            conducting_channels: self.current_passages.len(),
            junction_phase_population: phases.len(),
            pending_junctions: self.pending_junctions.len(),
            open_passages: usize::from(self.open_passage.is_some()),
            pending_current_pairs: self.pending_current_passages.len(),
            received_passages: self.passage_identities.len(),
            association_memory: self.association.machine().memory(),
        }
    }

    pub fn passage_delivery_order(&self, identity: &str) -> Option<u64> {
        if let Some(open) = &self.open_passage {
            if open.identity.as_deref() == Some(identity) {
                return Some(open.delivery_order);
            }
        }
        self.passage_identities
            .get(&identity.to_owned())
            .map(|standing| standing.delivery_order)
    }

    /// Propagate a question through every receiver-local causal front admitted by the conditioned
    /// relation body. Equal-arrival branches advance together and remain factorized; when no
    /// closed traversal exists, every non-dominated open front survives for a later return.
    pub fn think_fiber(
        &self,
        question: &str,
        receiver_horizon: u64,
    ) -> Result<Option<RelationalThoughtFiber>, RelationalLanguageError> {
        Ok(self
            .think_fiber_with_execution(question, receiver_horizon)?
            .fiber)
    }

    /// The connected-question receiver with separate deterministic CPU-front testimony.
    pub fn think_fiber_with_execution(
        &self,
        question: &str,
        receiver_horizon: u64,
    ) -> Result<RelationalThoughtExecution, RelationalLanguageError> {
        let required_entity_regions = question_entity_regions(question, &self.predicate_lexicon);
        self.think_fiber_with_regions_execution(
            question,
            &required_entity_regions,
            receiver_horizon,
            true,
            None,
        )
    }

    /// Propagate through the complete mounted relation body while admitting only clauses carried
    /// by the declared caused passages. The passage set is an occurrence aperture, not a rebuilt
    /// temporary ecology: recurrent junctions and current capacities remain owned by this body,
    /// while no path may escape through an unrelated passage.
    pub fn think_fiber_in_passages(
        &self,
        question: &str,
        passages: &BTreeSet<String>,
        receiver_horizon: u64,
    ) -> Result<Option<RelationalThoughtFiber>, RelationalLanguageError> {
        if passages.is_empty() {
            return Ok(None);
        }
        let mut allowed_clauses = ExactSet::<usize>::new();
        for passage in passages {
            if let Some(clauses) = self.passage_incidence.get(passage) {
                allowed_clauses.extend(clauses.iter().copied());
            }
        }
        if allowed_clauses.is_empty() {
            return Ok(None);
        }
        let required_entity_regions = question_entity_regions(question, &self.predicate_lexicon);
        Ok(self
            .think_fiber_with_regions_execution(
                question,
                &required_entity_regions,
                receiver_horizon,
                true,
                Some(&allowed_clauses),
            )?
            .fiber)
    }

    /// Propagate through an explicitly received plural question frontier.
    ///
    /// This is the production seam used by a deliberative receiver: broad visible noun phrases
    /// remain contextual leaders while their local constituent regions may return through
    /// different, connected clauses.  It does not weaken [`clause_reaches`]; one local region is
    /// still received by one actual entity side, and cross-clause assembly still owes enacted
    /// relation joins.
    pub fn think_fiber_over_regions(
        &self,
        question: &str,
        required_entity_regions: &[BTreeSet<String>],
        receiver_horizon: u64,
    ) -> Result<Option<RelationalThoughtFiber>, RelationalLanguageError> {
        Ok(self
            .think_fiber_with_regions_execution(
                question,
                required_entity_regions,
                receiver_horizon,
                false,
                None,
            )?
            .fiber)
    }

    /// Receive a broad question through one factorized connected traversal computation.
    ///
    /// The question's regions are co-present inputs, but only an enacted chain of conducting
    /// relation channels may close their outer fiber. Equal-arrival predecessors advance as one
    /// antichain support, avoiding both Cartesian path enumeration and a canonical-path selector.
    pub fn think_deliberative_fiber_over_regions(
        &self,
        question: &str,
        required_entity_regions: &[BTreeSet<String>],
        receiver_horizon: u64,
    ) -> Result<Option<RelationalThoughtFiber>, RelationalLanguageError> {
        Ok(self
            .think_deliberative_fiber_over_regions_with_execution(
                question,
                required_entity_regions,
                receiver_horizon,
            )?
            .fiber)
    }

    /// The same receiver-local deliberation with physical CPU-front testimony kept beside the
    /// semantic fiber. Serial and multicore execution must return an equal fiber; only this
    /// receipt may differ with apparatus placement.
    pub fn think_deliberative_fiber_over_regions_with_execution(
        &self,
        question: &str,
        required_entity_regions: &[BTreeSet<String>],
        receiver_horizon: u64,
    ) -> Result<RelationalThoughtExecution, RelationalLanguageError> {
        let mut execution = self.think_fiber_with_regions_execution(
            question,
            required_entity_regions,
            receiver_horizon,
            false,
            None,
        )?;
        if execution.fiber.is_none() && !required_entity_regions.is_empty() {
            execution.fiber = Some(RelationalThoughtFiber {
                question: question.to_owned(),
                currents: Vec::new(),
                unreturned_question_regions: required_entity_regions.to_vec(),
                causal_front_fibers: Vec::new(),
                open_channel_boundaries: Vec::new(),
            });
        }
        Ok(execution)
    }

    fn think_fiber_with_regions_execution(
        &self,
        question: &str,
        required_entity_regions: &[BTreeSet<String>],
        receiver_horizon: u64,
        constrain_requested_relations: bool,
        allowed_clauses: Option<&BTreeSet<usize>>,
    ) -> Result<RelationalThoughtExecution, RelationalLanguageError> {
        if self.open_passage.is_some()
            || !self.pending_junctions.is_empty()
            || !self.pending_current_passages.is_empty()
        {
            return Err(RelationalLanguageError::OpenPassage);
        }
        if self.clauses.is_empty() || required_entity_regions.is_empty() {
            return Ok(RelationalThoughtExecution {
                fiber: None,
                cpu: None,
            });
        }
        let requested_relations = if constrain_requested_relations {
            question_requested_relations(question, &self.predicate_lexicon)
        } else {
            Default::default()
        };
        let clause_regions = self.clause_region_incidence(
            required_entity_regions,
            &requested_relations,
            allowed_clauses,
        );
        let mut seed_clauses = ExactSet::<usize>::new();
        seed_clauses.extend(clause_regions.keys().copied());
        let source_sections = self.source_occurrence_sections(&seed_clauses);
        if source_sections.is_empty() {
            return Ok(RelationalThoughtExecution {
                fiber: None,
                cpu: None,
            });
        }

        let mut currents = Vec::<RelationalThoughtCurrent>::new();
        let mut causal_front_fibers = Vec::<RelationalCausalFrontFiber>::new();
        let mut open_channel_boundaries = Vec::<RelationalCausalChannel>::new();
        let executor = self.thought_cpu_executor();
        let (returned_sections, execution) = executor
            .execute_indexed(&source_sections, |_source_at, source| {
                let (section, fiber, open_boundaries) = self.radiate_source_section(
                    source,
                    receiver_horizon,
                    required_entity_regions,
                    &clause_regions,
                    allowed_clauses,
                )?;
                let current = self.form_thought_current(
                    question,
                    required_entity_regions,
                    section,
                    constrain_requested_relations,
                )?;
                Ok::<_, RelationalLanguageError>((current, fiber, open_boundaries))
            })
            .map_err(relational_cpu_error)?;
        for (current, fiber, open_boundaries) in returned_sections {
            currents.push(current);
            causal_front_fibers.push(fiber);
            open_channel_boundaries.extend(open_boundaries);
        }
        currents.sort_by(|left, right| {
            left.open_entity_regions
                .len()
                .cmp(&right.open_entity_regions.len())
                .then_with(|| left.clauses.len().cmp(&right.clauses.len()))
                .then_with(|| {
                    left.clauses
                        .iter()
                        .map(|clause| clause.identity.as_str())
                        .cmp(right.clauses.iter().map(|clause| clause.identity.as_str()))
                })
        });
        causal_front_fibers.sort_by(|left, right| {
            (
                left.arrival_wave,
                left.target_clauses.as_ref(),
                left.source_clauses.as_ref(),
            )
                .cmp(&(
                    right.arrival_wave,
                    right.target_clauses.as_ref(),
                    right.source_clauses.as_ref(),
                ))
        });
        causal_front_fibers.dedup();
        open_channel_boundaries.sort_by(|left, right| {
            (
                left.from_clause.as_str(),
                left.to_clause.as_str(),
                &left.shared_entity_faces,
            )
                .cmp(&(
                    right.from_clause.as_str(),
                    right.to_clause.as_str(),
                    &right.shared_entity_faces,
                ))
        });
        open_channel_boundaries.dedup();
        let mut unreturned_question_regions = if currents.iter().any(|current| current.is_closed())
        {
            Vec::new()
        } else {
            currents
                .iter()
                .flat_map(|current| {
                    current
                        .open_entity_regions
                        .iter()
                        .filter_map(|at| current.required_entity_regions.get(*at))
                        .cloned()
                })
                .collect::<Vec<_>>()
        };
        unreturned_question_regions.sort();
        unreturned_question_regions.dedup();
        let cpu = execution;
        if std::env::var_os("EROS_TRACE").is_some() {
            eprintln!(
                "eros-trace relational weave tasks={} workers={} batches={} joins={}",
                cpu.tasks, cpu.workers_used, cpu.batches, cpu.joins
            );
        }
        Ok(RelationalThoughtExecution {
            fiber: (!currents.is_empty()).then_some(RelationalThoughtFiber {
                question: question.to_owned(),
                currents,
                unreturned_question_regions,
                causal_front_fibers,
                open_channel_boundaries,
            }),
            cpu: Some(cpu),
        })
    }

    fn thought_cpu_executor(&self) -> CpuExecutor {
        let workers = NonZeroUsize::new(self.requested_worker_threads.max(1))
            .expect("one requested relational worker is always nonzero");
        if workers.get() == 1 {
            CpuExecutor::serial()
        } else {
            CpuExecutor::multicore(workers)
        }
    }

    /// Group receiver contacts only by their caused source occurrence. No subset, dominance, or
    /// lexical quotient selects among the groups; every source section receives its own bounded
    /// current from the lower owner.
    fn source_occurrence_sections(
        &self,
        seeds: &BTreeSet<usize>,
    ) -> LocalSequence<LocalSet<usize>> {
        let mut remaining = LocalSet::from_iter(seeds.iter().copied());
        let mut sections = LocalSequence::new();
        while let Some(root) = remaining.first().copied() {
            remaining.remove(&root);
            let mut section = LocalSet::from([root]);
            if let Some(copresent) = self.passage_incidence.get(&self.clauses[root].passage) {
                for next in copresent {
                    if seeds.contains(next) && remaining.remove(next) {
                        section.insert(*next);
                    }
                }
            }
            sections.push(section);
        }
        sections
    }

    fn radiate_source_section(
        &self,
        source: &LocalSet<usize>,
        receiver_horizon: u64,
        required_entity_regions: &[BTreeSet<String>],
        clause_regions: &BTreeMap<usize, BTreeSet<usize>>,
        allowed_clauses: Option<&BTreeSet<usize>>,
    ) -> Result<
        (
            RelationalRadiatedSection,
            RelationalCausalFrontFiber,
            LocalSequence<RelationalCausalChannel>,
        ),
        RelationalLanguageError,
    > {
        let sources = source
            .iter()
            .map(|at| clause_site(*at))
            .collect::<Result<LocalSet<_>, _>>()?;
        let radiation = if let Some(allowed) = allowed_clauses {
            let aperture = allowed
                .iter()
                .map(|at| clause_site(*at))
                .collect::<Result<LocalSet<_>, _>>()?;
            self.receiver_current.radiate_to_horizon_in_aperture(
                sources,
                receiver_horizon,
                &aperture,
            )?
        } else {
            self.receiver_current
                .radiate_to_horizon(sources, receiver_horizon)?
        };
        self.project_radiated_section(&radiation, required_entity_regions, clause_regions)
    }

    fn project_radiated_section(
        &self,
        radiation: &ExactReceiverCurrentRadiation,
        required_entity_regions: &[BTreeSet<String>],
        clause_regions: &BTreeMap<usize, BTreeSet<usize>>,
    ) -> Result<
        (
            RelationalRadiatedSection,
            RelationalCausalFrontFiber,
            LocalSequence<RelationalCausalChannel>,
        ),
        RelationalLanguageError,
    > {
        let mut selected = BTreeSet::new();
        let mut clause_arrivals = BTreeMap::new();
        for site in radiation.arrivals.keys() {
            let at = usize::try_from(site.0).map_err(|_| RelationalLanguageError::CarrierExtent)?;
            let arrival = radiation
                .arrivals
                .get(site)
                .ok_or(RelationalLanguageError::MalformedClause)?;
            selected.insert(at);
            clause_arrivals.insert(at, arrival.chronology);
        }

        let returned_regions = selected
            .iter()
            .flat_map(|at| clause_regions.get(at).into_iter().flatten().copied())
            .collect::<BTreeSet<_>>();
        let open_regions = (0..required_entity_regions.len())
            .filter(|region| !returned_regions.contains(region))
            .collect::<BTreeSet<_>>();
        let mut open_boundaries = LocalSequence::new();
        for from in &selected {
            for to in &self.adjacency[*from] {
                if selected.contains(to)
                    || self
                        .current_passages
                        .contains(&ordered_clause_pair(*from, *to))
                {
                    continue;
                }
                if clause_regions
                    .get(to)
                    .is_some_and(|regions| !regions.is_disjoint(&open_regions))
                {
                    open_boundaries.push(self.relation_channel(*from, *to));
                }
            }
        }
        open_boundaries.sort_by(|left, right| {
            (left.from_clause.as_str(), left.to_clause.as_str())
                .cmp(&(right.from_clause.as_str(), right.to_clause.as_str()))
        });
        open_boundaries.dedup();

        let mut enacted_pairs = BTreeSet::new();
        let mut passages = Vec::new();
        let mut predecessor_incidence = LocalRelations::new();
        let mut channels = LocalSequence::new();
        for site in radiation.arrivals.keys() {
            let to = usize::try_from(site.0).map_err(|_| RelationalLanguageError::CarrierExtent)?;
            let arrival = radiation
                .arrivals
                .get(site)
                .ok_or(RelationalLanguageError::MalformedClause)?;
            let mut incoming = LocalSet::new();
            for predecessor in &arrival.predecessors {
                let from = usize::try_from(predecessor.from.0)
                    .map_err(|_| RelationalLanguageError::CarrierExtent)?;
                if !selected.contains(&from) {
                    continue;
                }
                let channel = self.relation_channel(from, to);
                let receipt = radiation
                    .passage_receipts
                    .iter()
                    .find(|receipt| {
                        receipt.passage == predecessor.passage
                            && receipt.from == predecessor.from
                            && receipt.to == *site
                            && receipt.arrival_chronology == arrival.chronology
                    })
                    .ok_or(RelationalLanguageError::MalformedClause)?;
                let join = relational_join(
                    &self.clauses[from],
                    &self.clauses[to],
                    channel.conduct,
                    channel.recurrence_population.to_owned(),
                );
                incoming.insert(self.clauses[from].identity.to_owned());
                enacted_pairs.insert(ordered_clause_pair(from, to));
                channels.push(channel);
                passages.push(RelationalTransportPassage {
                    identity: format!(
                        "{}#current={}",
                        transport_passage_identity(&join),
                        predecessor.passage.0
                    ),
                    from_clause: self.clauses[from].identity.to_owned(),
                    to_clause: self.clauses[to].identity.to_owned(),
                    delay: receipt.passage_delay,
                    arrival_chronology: receipt.arrival_chronology,
                    shared_entity_faces: join.shared_entity_faces,
                    shared_passage: join.shared_passage,
                });
            }
            if !incoming.is_empty() {
                predecessor_incidence
                    .try_insert(self.clauses[to].identity.to_owned(), incoming)
                    .map_err(|_| RelationalLanguageError::CarrierExtent)?;
            }
        }
        channels.sort_by(|left, right| {
            (left.from_clause.as_str(), left.to_clause.as_str())
                .cmp(&(right.from_clause.as_str(), right.to_clause.as_str()))
        });
        channels.dedup();

        let mut targets = LocalSequence::new();
        let mut exact_path_populations = LocalRelations::new();
        let mut factorized_path_population = BigUint::from(1_u8);
        for at in &selected {
            if !clause_regions.contains_key(at) {
                continue;
            }
            let site = clause_site(*at)?;
            let population = radiation.exact_path_population(site);
            factorized_path_population *= &population;
            let identity = self.clauses[*at].identity.to_owned();
            targets.push(identity.to_owned());
            exact_path_populations
                .try_insert(identity, population)
                .map_err(|_| RelationalLanguageError::CarrierExtent)?;
        }
        let mut source_clauses = LocalSequence::new();
        for source in &radiation.sources {
            let at =
                usize::try_from(source.0).map_err(|_| RelationalLanguageError::CarrierExtent)?;
            source_clauses.push(self.clauses[at].identity.to_owned());
        }
        let complete_support = selected
            .iter()
            .map(|at| self.clauses[*at].identity.to_owned())
            .collect();
        let receiver_horizon = radiation.receiver_horizon.unwrap_or(0);
        Ok((
            RelationalRadiatedSection {
                selected,
                enacted_pairs,
                clause_arrivals,
                passages,
                receiver_horizon,
                factorized_path_population,
            },
            RelationalCausalFrontFiber {
                source_clauses,
                target_clauses: targets,
                arrival_wave: receiver_horizon,
                predecessor_incidence,
                exact_path_populations,
                complete_support,
                channels,
            },
            open_boundaries,
        ))
    }

    fn form_thought_current(
        &self,
        question: &str,
        required_entity_regions: &[BTreeSet<String>],
        mut traversal: RelationalRadiatedSection,
        constrain_requested_relations: bool,
    ) -> Result<RelationalThoughtCurrent, RelationalLanguageError> {
        let requested_relations = if constrain_requested_relations {
            question_requested_relations(question, &self.predicate_lexicon)
        } else {
            Default::default()
        };
        // `selected` is completed with the co-present predecessor body of every passage that
        // actually arrived. A deictic antecedent inherits that passage's arrival chronology; it
        // never appears later as an invented separated edge or a source-free association.
        receive_deictic_antecedents(&mut traversal.selected, &self.clauses);
        let mut passage_arrivals = BTreeMap::<&str, u64>::new();
        for at in &traversal.selected {
            if let Some(arrival) = traversal.clause_arrivals.get(at).copied() {
                passage_arrivals
                    .entry(self.clauses[*at].passage.as_str())
                    .and_modify(|prior| *prior = (*prior).min(arrival))
                    .or_insert(arrival);
            }
        }
        for at in &traversal.selected {
            let chronology = passage_arrivals
                .get(self.clauses[*at].passage.as_str())
                .copied()
                .unwrap_or(traversal.receiver_horizon);
            traversal.clause_arrivals.entry(*at).or_insert(chronology);
        }
        let ordered = order_relation_path(&traversal.selected, &self.clauses);
        let clauses = ordered
            .iter()
            .map(|at| self.clauses[*at].clone())
            .collect::<Vec<_>>();
        let joins = self.causal_relation_joins(&ordered, &traversal.enacted_pairs);
        let returned_entity_regions = required_entity_regions
            .iter()
            .enumerate()
            .filter_map(|(region_at, region)| {
                clauses
                    .iter()
                    .any(|clause| {
                        clause_reaches(clause, region)
                            && (requested_relations.is_empty()
                                || requested_relations.contains(&clause.relation))
                    })
                    .then_some(region_at)
            })
            .collect::<BTreeSet<_>>();
        let open_entity_regions = (0..required_entity_regions.len())
            .filter(|region| !returned_entity_regions.contains(region))
            .collect::<BTreeSet<_>>();
        let source_witnesses = clauses
            .iter()
            .map(|clause| clause.source.clone())
            .collect::<BTreeSet<_>>();
        let passage_witnesses = clauses
            .iter()
            .map(|clause| clause.passage.clone())
            .collect::<BTreeSet<_>>();
        let parse_fibers = clauses
            .iter()
            .filter_map(|clause| {
                self.parse_fibers
                    .iter()
                    .find(|fiber| fiber.selected_clause == clause.identity)
                    .cloned()
            })
            .collect::<Vec<_>>();
        let factorized_parse_population = parse_fiber_population(&clauses, &parse_fibers);
        // An open current may speak internally without being promoted to a final answer.  Its
        // realization is explicitly carried beside the unresolved boundary, so an autonomous
        // ecology can question or criticize the partial relation instead of turning uncertainty
        // into silence.  Laboratory answer projection below still requires an actually closed
        // current.
        let realizations =
            realize_relation_fibers(&clauses, &parse_fibers, &self.inherited_surfaces)?;
        if open_entity_regions.is_empty() && realizations.is_empty() {
            return Err(RelationalLanguageError::MalformedClause);
        }
        let selected_realization = realizations
            .iter()
            .position(|realization| realization.voice_dual && !realization.inherited_contiguous)
            .or_else(|| {
                realizations
                    .iter()
                    .position(|realization| !realization.inherited_contiguous)
            })
            .unwrap_or(0);
        let transport = self.relation_transport_from_radiated_section(
            &ordered,
            &clauses,
            &joins,
            &realizations,
            &open_entity_regions,
            &traversal,
        )?;
        Ok(RelationalThoughtCurrent {
            question: question.to_owned(),
            clauses,
            joins,
            required_entity_regions: required_entity_regions.to_vec(),
            returned_entity_regions,
            open_entity_regions,
            source_witnesses,
            passage_witnesses,
            parse_fibers,
            factorized_transport_population: traversal.factorized_path_population.clone(),
            factorized_parse_population,
            realizations,
            selected_realization,
            transport,
        })
    }

    /// Restrict the question's simultaneous receiver regions through the standing constituent
    /// aperture. This is an incidence intersection followed by the exact clause receiver test;
    /// it is not a corpus scan or a lexical similarity ranking.
    fn clause_region_incidence(
        &self,
        required_entity_regions: &[BTreeSet<String>],
        requested_relations: &BTreeSet<String>,
        allowed_clauses: Option<&BTreeSet<usize>>,
    ) -> BTreeMap<usize, BTreeSet<usize>> {
        let mut incidence = BTreeMap::<usize, BTreeSet<usize>>::new();
        for (region_at, region) in required_entity_regions.iter().enumerate() {
            let mut faces = region.iter();
            let Some(first) = faces.next() else {
                continue;
            };
            let Some(mut candidates) = self.face_incidence.get(first).cloned() else {
                continue;
            };
            for face in faces {
                let Some(carriers) = self.face_incidence.get(face) else {
                    candidates.clear();
                    break;
                };
                candidates = candidates.intersection(carriers).copied().collect();
            }
            for clause_at in candidates {
                if allowed_clauses.is_some_and(|allowed| !allowed.contains(&clause_at)) {
                    continue;
                }
                let clause = &self.clauses[clause_at];
                if clause_reaches(clause, region)
                    && (requested_relations.is_empty()
                        || requested_relations.contains(&clause.relation))
                {
                    incidence.entry(clause_at).or_default().insert(region_at);
                }
            }
        }
        incidence
    }

    fn relation_channel(&self, from: usize, to: usize) -> RelationalCausalChannel {
        let key = ordered_clause_pair(from, to);
        let phase = self
            .junction_phases
            .get(&key)
            .expect("every structural relation channel retains its exact junction phase");
        let recurrence = match self
            .junction_returns
            .get(&key)
            .map(ResonanceOccurrenceRead::conduct)
        {
            Some(ResonanceOccurrenceConduct::Complete { .. }) => 2_u8,
            Some(ResonanceOccurrenceConduct::Open { .. }) | None => 1_u8,
        };
        let left = &self.clauses[from];
        let right = &self.clauses[to];
        let conduct = if let Some(conduct) = inherited_channel_conduct(left, right) {
            conduct
        } else if self.current_passages.contains(&key) {
            RelationalChannelConduct::Ride
        } else {
            RelationalChannelConduct::Open
        };
        RelationalCausalChannel {
            from_clause: left.identity.clone(),
            to_clause: right.identity.clone(),
            shared_entity_faces: phase.shared_entity_faces.clone(),
            conduct,
            recurrence_population: BigUint::from(recurrence),
        }
    }

    fn causal_relation_joins(
        &self,
        ordered: &[usize],
        enacted_pairs: &BTreeSet<(usize, usize)>,
    ) -> Vec<RelationalJoin> {
        let mut joins = Vec::new();
        // One chronological spanning seam is a complete factorization of each co-present passage
        // cell. The clause population and common passage identity retain the higher cell; a
        // complete binary clique would add no testimony and would make observation quadratic.
        let mut preceding_in_passage = BTreeMap::<&str, usize>::new();
        for right in ordered {
            let passage = self.clauses[*right].passage.as_str();
            if let Some(left) = preceding_in_passage.insert(passage, *right) {
                joins.push(relational_join(
                    &self.clauses[left],
                    &self.clauses[*right],
                    RelationalChannelConduct::Copresent,
                    BigUint::from(1u8),
                ));
            }
        }
        let selected = ordered.iter().copied().collect::<BTreeSet<_>>();
        for (left, right) in enacted_pairs {
            if !selected.contains(left)
                || !selected.contains(right)
                || self.clauses[*left].passage == self.clauses[*right].passage
            {
                continue;
            }
            let channel = self.relation_channel(*left, *right);
            joins.push(relational_join(
                &self.clauses[*left],
                &self.clauses[*right],
                channel.conduct,
                channel.recurrence_population,
            ));
        }
        joins
    }

    fn relation_transport_from_radiated_section(
        &self,
        ordered: &[usize],
        clauses: &[RelationalClause],
        joins: &[RelationalJoin],
        realizations: &[RelationalRealization],
        open_entity_regions: &BTreeSet<usize>,
        traversal: &RelationalRadiatedSection,
    ) -> Result<RelationalCurrentTransport, RelationalLanguageError> {
        let clause_at = clauses
            .iter()
            .enumerate()
            .map(|(at, clause)| (clause.identity.as_str(), at))
            .collect::<BTreeMap<_, _>>();
        let complete_edges = joins
            .iter()
            .map(|join| {
                Ok(RelationalTransportEdge {
                    from: *clause_at
                        .get(join.from_clause.as_str())
                        .ok_or(RelationalLanguageError::MalformedClause)?,
                    to: *clause_at
                        .get(join.to_clause.as_str())
                        .ok_or(RelationalLanguageError::MalformedClause)?,
                    identity: transport_passage_identity(join),
                })
            })
            .collect::<Result<Vec<_>, RelationalLanguageError>>()?;
        let adjacency = transport_adjacency(clauses.len(), &complete_edges);
        let components = transport_components(clauses, &adjacency);
        let clause_arrivals = ordered
            .iter()
            .map(|at| {
                Ok((
                    self.clauses[*at].identity.clone(),
                    traversal
                        .clause_arrivals
                        .get(at)
                        .copied()
                        .ok_or(RelationalLanguageError::MalformedClause)?,
                ))
            })
            .collect::<Result<BTreeMap<_, _>, RelationalLanguageError>>()?;
        let selected_identities = clauses
            .iter()
            .map(|clause| clause.identity.as_str())
            .collect::<BTreeSet<_>>();
        let mut passages = traversal
            .passages
            .iter()
            .filter(|passage| {
                selected_identities.contains(passage.from_clause.as_str())
                    && selected_identities.contains(passage.to_clause.as_str())
            })
            .cloned()
            .collect::<Vec<_>>();
        passages.sort_by(|left, right| {
            (left.arrival_chronology, left.identity.as_str())
                .cmp(&(right.arrival_chronology, right.identity.as_str()))
        });
        passages.dedup_by(|left, right| {
            left.identity == right.identity && left.arrival_chronology == right.arrival_chronology
        });
        let ordered_transport_product = passages
            .iter()
            .map(|passage| passage.identity.clone())
            .collect();
        let receiver_horizon = clause_arrivals.values().copied().max().unwrap_or(0);
        let local_branch_capacities = ordered
            .iter()
            .map(|at| {
                let site = clause_site(*at)?;
                let capacity = self
                    .receiver_current
                    .site(site)
                    .ok_or(RelationalLanguageError::MalformedClause)?
                    .capacity
                    .clone();
                Ok((self.clauses[*at].identity.clone(), capacity))
            })
            .collect::<Result<BTreeMap<_, _>, RelationalLanguageError>>()?;
        let receiver_quotients = realizations
            .iter()
            .enumerate()
            .map(|(realization, quotient)| RelationalReceiverQuotient {
                realization,
                voice_dual: quotient.voice_dual,
                inherited_contiguous: quotient.inherited_contiguous,
                surface: quotient.text.clone(),
            })
            .collect();
        Ok(RelationalCurrentTransport {
            components: components
                .iter()
                .map(|component| {
                    component
                        .iter()
                        .map(|at| clauses[*at].identity.clone())
                        .collect()
                })
                .collect(),
            clause_arrivals,
            passages,
            ordered_transport_product,
            receiver_horizon,
            local_branch_capacities,
            boundary_storage: open_entity_regions.clone(),
            holonomy_generators: transport_holonomy(clauses, &complete_edges),
            receiver_quotients,
        })
    }
}
