//! **The pending ratio: a delayed comparison read at the contemporary constitution.**
//!
//! [definition] A [`PendingRatio`] holds the producing operands only (design (a), "The pending
//! read"; guard 3): the anchor, the lift point `λ` at the cut; a copy of the encoder moment's counts
//! `M` at the cut (never `m̃`, and never a handle to a moment that later ingests extend); a copy of
//! the receiving parametron's active suffix address at the cut (`hnn::receiving::ActiveAddress`,
//! its receiver's `D` letters and the reader of the next ones: the clock's phases, the windings
//! since the aeon's opening and the contacts' site kinds its contact letters read, so every
//! bundle of the epoch's known targets is read from the state at the cut; campaign 2); its
//! [`ReceivingPhases`]; and the commit it was produced at. Every
//! word opens at zero change or, under a declared reception carry, on the resident's carried change
//! held beside the ratio ([`PendingRatio::open_on`]), so the anchor needs no waves. A read ([`PendingRatio::open`])
//! recomputes `m̃ = ⟨M, E_now⟩` and runs the word at the contemporary constitution, `q` included;
//! at compare, the contemporary landmark tree is read at each phase's causal address, the copied
//! suffix after the epoch's earlier targets (the landmark tree, [`PendingRatio::against`]):
//!
//! - `refine` publishes only faces, with no commit flag, so no source is counted twice and `E` is
//!   never mixed across two cuts;
//! - with no intervening deposit a delayed read equals the immediate one exactly; after a deposit
//!   it returns the residual against the emitted face (Lean `HNN/Retention.contemporary_read`, on
//!   the abstract block operator; the concrete-tick bridge is owed in #62);
//! - the producing anchor is a clock reading, not material, and no frozen cut of earlier material.
//!
//! The source constructor never accepts a face in place of its moment. An opt-in, trusted
//! realization handoff separately attaches a finite observation context after the actual read.
//! It retains only resolved membership bits, never logits/material as a memorization key.
//! The source-constructor guarantee is structural: the fields are
//! private and [`PendingRatio::produce`], the only constructor, takes the anchor's lift point, the
//! moment, the receiving phases and the commit. The doctest shows a face refused where the moment
//! goes (`E0308`, a type mismatch):
//!
//! ```compile_fail,E0308
//! use holonics::hnn::{ActiveAddress, Current, PendingRatio, ReceivingPhases};
//! use holonics::hnn::ratio::Faces;
//! // A face is not the moment a pending ratio is produced from (guard 3).
//! fn from_face(
//!     current: &Current,
//!     faces: &Faces,
//!     address: &ActiveAddress,
//!     phases: &ReceivingPhases,
//! ) -> PendingRatio {
//!     PendingRatio::produce(current, faces, address, phases, 0).unwrap()
//! }
//! ```
//!
//! and it has no lifetime parameter (guard 2):
//!
//! ```compile_fail,E0107
//! fn borrowed(pending: holonics::hnn::PendingRatio<'static>) {}
//! ```

use num_bigint::BigInt;

use crate::compression::landmark::context::{LandmarkFace, Letter, ObservedAddress};
use crate::hnn::HnnError;
use crate::hnn::chart::Charts;
use crate::hnn::field::{ConstitutionRead, Current, Field};
use crate::hnn::moment::SourceMoment;
use crate::hnn::ratio::Faces;
use crate::hnn::realization::indexed;
use crate::hnn::receiving::{ActiveAddress, ReceivingPhases, Scored};
use crate::hnn::word::{Word, WordOpening};
use crate::ratio::Rat;

/// [definition] **A pending ratio**: the producing anchor `λ`, the encoder moment `M`, the active
/// suffix address, the receiving phases and the producing commit. See the module header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PendingRatio {
    anchor: Vec<BigInt>,
    moment: SourceMoment,
    address: ActiveAddress,
    phases: ReceivingPhases,
    commit: u64,
    view: crate::hnn::ring::modes::ModeView,
    observation: Option<Vec<Vec<bool>>>,
    prepared_input: Option<crate::hnn::reference::prepared_input::PreparedInputCut>,
}

/// [definition] **An epoch's faces at compare**: the combined faces (the tree's at each phase's
/// address plus the wave's) and the tree faces they were formed from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Against {
    pub faces: Faces,
    pub trees: Vec<LandmarkFace>,
}

impl PendingRatio {
    /// Transport the retained producing cut into a derived field, without inventing past ticks.
    pub(crate) fn found_ring(
        &self,
        field: &Field,
        constitution: &crate::hnn::constitution::Constitution,
        ring: usize,
        contact: usize,
        key: u64,
    ) -> Result<Self, HnnError> {
        let mut next = self.clone();
        next.moment.found_ring(field, ring)?;
        next.anchor.push(BigInt::from(key));
        let current = Current::at(field, next.anchor.clone())?;
        next.address = self
            .address
            .found_ring(field, constitution, ring, contact, &current)?;
        Ok(next)
    }

    /// [definition; agent-inferred, October 4] The one arrived ratio's producing operands:
    /// commit, anchor, SourceMoment copy, declaring phases and producing address/reader.
    /// There is no saved material, word or face, and no sequence of prior comparisons.
    pub(crate) fn write_saved(&self, s: &mut String) {
        use crate::hnn::state_text::line;
        let mut header = vec![self.commit.to_string()];
        for &(g, _, d) in self.view.selections() {
            header.push(g.to_string());
            header.push(d.to_string());
        }
        line(s, if self.prepared_input.is_some(){"ratio-prepared-commit"}else{"ratio-commit"}, header);
        if let Some(p)=&self.prepared_input{line(s,"ratio-control",[crate::hnn::reference::prepared_input::codec::hex(&p.to_text())]);}
        line(s, "ratio-anchor", &self.anchor);
        self.moment.write(s);
        self.phases.write_saved(s);
        if self.phases.observation_partition().is_some() {
            line(
                s,
                "ratio-observation",
                [self.observation.as_ref().map_or(0, Vec::len).to_string()],
            );
            if let Some(paths) = &self.observation {
                for path in paths {
                    line(
                        s,
                        "observation-bits",
                        [path
                            .iter()
                            .map(|b| if *b { '1' } else { '0' })
                            .collect::<String>()],
                    );
                }
            }
        }
        self.address.write(s);
    }

    pub(crate) fn read_saved<'a>(
        field: &Field,
        prototype: &ActiveAddress,
        next: crate::hnn::state_text::Next<'_, 'a>,
    ) -> Result<Self, HnnError> {
        use crate::hnn::state_text::{keyed, values};
        let header=next("the producing commit")?;
        let prepared=header.starts_with("ratio-prepared-commit ");
        let commit: Vec<u64> = values(&keyed(header,if prepared{"ratio-prepared-commit"}else{"ratio-commit"},"the producing commit")?,"the producing commit")?;
        let prepared_input=if prepared{
            let row=keyed(next("the original prepared input cut")?,"ratio-control","the original prepared input cut")?;
            if row.len()!=1{return Err(HnnError::Unadmitted{reason:"one complete original prepared cut"});}
            Some(crate::hnn::reference::prepared_input::PreparedInputCut::from_text(&crate::hnn::reference::prepared_input::codec::unhex(row[0])?)?)
        }else{None};
        if commit.is_empty() || commit.len() % 2 != 1 {
            return Err(HnnError::Unadmitted {
                reason: "a saved ratio's commit and mode selections",
            });
        }
        let mut selections = Vec::new();
        for pair in commit[1..].chunks_exact(2) {
            selections.push((
                usize::try_from(pair[0]).map_err(|_| HnnError::CountOverflow)?,
                pair[1],
            ));
        }
        let view = crate::hnn::ring::modes::ModeView::from_periods(field, &selections)?;
        let anchor: Vec<BigInt> = values(
            &keyed(
                next("the producing anchor")?,
                "ratio-anchor",
                "the producing anchor",
            )?,
            "the producing anchor",
        )?;
        let current = Current::at(field, anchor)?;
        let moment = SourceMoment::read(field, next("the producing moment")?, next)?;
        let phases = ReceivingPhases::read_saved(field, next("the producing phases")?)?;
        let observation = if let Some(partition) = phases.observation_partition() {
            let n: Vec<usize> = values(
                &keyed(
                    next("the producing observation")?,
                    "ratio-observation",
                    "the producing observation",
                )?,
                "the producing observation",
            )?;
            if n.len() != 1 || (n[0] != 0 && n[0] != phases.aperture()) {
                return Err(HnnError::Unadmitted {
                    reason: "one saved observation per receiving phase",
                });
            }
            let mut paths = Vec::new();
            for _ in 0..n[0] {
                let words = keyed(
                    next("observation membership bits")?,
                    "observation-bits",
                    "observation membership bits",
                )?;
                if words.len() != 1
                    || words[0].len() != partition.outcome_bits(field, phases.ring())
                    || !words[0].bytes().all(|b| b == b'0' || b == b'1')
                {
                    return Err(HnnError::Unadmitted {
                        reason: "a saved receiver observation of its partition's width",
                    });
                }
                let bits: Vec<bool> = words[0].bytes().map(|b| b == b'1').collect();
                partition.path(bits.clone())?;
                paths.push(bits);
            }
            if n[0] == 0 { None } else { Some(paths) }
        } else {
            None
        };
        let address = prototype
            .truncated(phases.depth())?
            .continued(next("the producing address")?, next)?;
        Self::produce(&current, &moment, &address, &phases, commit[0]).map(|mut ratio| {
            ratio.view = view;
            ratio.observation = observation;
            ratio.prepared_input=prepared_input;
            ratio
        })
    }

    /// **Produce a pending ratio at the cut**: the lift point, a copy of the moment's counts, the
    /// receiver's first `D` letters of the active suffix address, the receiving phases and the
    /// commit. These are operands only. Refused when the address register is shallower than the
    /// receiver's depth.
    pub fn produce(
        current: &Current,
        moment: &SourceMoment,
        address: &ActiveAddress,
        phases: &ReceivingPhases,
        commit: u64,
    ) -> Result<Self, HnnError> {
        Ok(Self {
            anchor: current.lift().to_vec(),
            moment: moment.clone(),
            address: address.truncated(phases.depth())?,
            phases: phases.clone(),
            commit,
            view: crate::hnn::ring::modes::ModeView::whole(),
            observation: None,
            prepared_input: None,
        })
    }

    /// Bind a declared source view to the same producing moment, lift and commit.
    pub fn with_view(
        mut self,
        field: &Field,
        view: &crate::hnn::ring::modes::ModeView,
    ) -> Result<Self, HnnError> {
        if self.observation.is_some() {
            return Err(HnnError::Unadmitted {
                reason: "a produced observation cannot be rebound to a source view",
            });
        }
        view.check(field)?;
        self.view = view.clone();
        Ok(self)
    }
    /// Trusted cross-realization handoff, called exactly once after the actual initial raw
    /// wave read and before any target or tree combination: `anchors` are the receiving phases'
    /// anchors the read ran through and `wave` its faces ([`ObservationPartition::read`]). This
    /// derives its own finite paths; callers cannot attach arbitrary paths. As with other backend
    /// read handoffs, shape admission does not cryptographically prove an arbitrary external Face
    /// was executed. Native PendingId slots bind the producing resident and immutable WordOpening.
    pub fn admit_observed_read(
        &mut self,
        field: &Field,
        anchors: &[Vec<Rat>],
        wave: &Faces,
    ) -> Result<(), HnnError> {
        let Some(partition) = self.phases.observation_partition() else {
            return Ok(());
        };
        if self.observation.is_some() {
            return Err(HnnError::Unadmitted {
                reason: "an observation context is bound only once",
            });
        }
        if field.receiving_context(self.phases.ring()) != Some(partition) {
            return Err(HnnError::Unadmitted {
                reason: "an observed read belongs to its declared receiving phases",
            });
        }
        self.observation = Some(partition.read(field, &self.phases, anchors, wave)?);
        Ok(())
    }

    /// Frozen cut metadata: each phase's observation letters in the partition's order (a maximum
    /// set's class-index-ordered membership bits, a section's side readings).
    /// Successor rereads preserve this conditioning path; they do not claim to observe it anew.
    pub fn observation_bits(&self) -> Option<&[Vec<bool>]> {
        self.observation.as_deref()
    }

    pub fn view(&self) -> &crate::hnn::ring::modes::ModeView {
        &self.view
    }

    /// The producing anchor `λ`.
    pub fn anchor(&self) -> &[BigInt] {
        &self.anchor
    }

    /// The encoder moment's counts at the cut.
    pub fn moment(&self) -> &SourceMoment {
        &self.moment
    }

    /// The active suffix address at the cut, `D` letters newest first.
    pub fn address(&self) -> &ActiveAddress {
        &self.address
    }

    /// **The epoch's phase addresses** given its known targets
    /// (`hnn::receiving::ActiveAddress::phase`).
    pub fn addresses(&self, known: &[usize]) -> Result<Vec<Vec<Letter>>, HnnError> {
        self.phases.addresses(&self.address, known)
    }

    pub fn phases(&self) -> &ReceivingPhases {
        &self.phases
    }

    /// The commit the ratio was produced at.
    pub fn commit(&self) -> u64 {
        self.commit
    }

    /// The anchor as a lift point of the field.
    pub fn current(&self, field: &Field) -> Result<Current, HnnError> {
        Current::at(field, self.anchor.clone())
    }

    /// **Open the word at the contemporary constitution** on the anchor and the moment's counts,
    /// every solve seeded afresh.
    pub fn open<'c>(
        &self,
        field: &'c Field,
        constitution: &impl ConstitutionRead,
    ) -> Result<Word<'c>, HnnError> {
        self.open_charted(field, constitution, &mut Charts::new())
    }

    /// **Open the word, its solves warm-started from a resident's charts** (the lattice word).
    pub fn open_charted<'c>(
        &self,
        field: &'c Field,
        constitution: &impl ConstitutionRead,
        charts: &mut Charts,
    ) -> Result<Word<'c>, HnnError> {
        self.open_on(field, constitution, charts, &WordOpening::Rest)
    }

    /// **Open the word on a reception's opening** ([`Word::open_received`]; the reception carry):
    /// at [`WordOpening::Rest`] exactly [`PendingRatio::open_charted`]. The opening is the resident's
    /// carried change, read beside the pending ratio, never a field of it (guard 3).
    pub fn open_on<'c>(
        &self,
        field: &'c Field,
        constitution: &impl ConstitutionRead,
        charts: &mut Charts,
        opening: &WordOpening,
    ) -> Result<Word<'c>, HnnError> {
        Word::open_received_view(
            field,
            constitution,
            &self.current(field)?,
            &self.moment,
            charts,
            opening,
            &self.view,
        )
    }

    /// **The contemporary read**: the word run through its receiving epochs and the wave's faces
    /// read at the receiver's grain, every solve seeded afresh. Returns the word (for its return)
    /// and the faces.
    pub fn read<'c>(
        &self,
        field: &'c Field,
        constitution: &impl ConstitutionRead,
    ) -> Result<(Word<'c>, Faces), HnnError> {
        self.read_charted(field, constitution, &mut Charts::new())
    }

    /// **The contemporary read, warm-started from a resident's charts**: what [`PendingRatio::read`]
    /// returns, each solve refined from the chart its key last left (the charts are replaced by the
    /// refined ones). The receiving epochs' reads each read only their own anchor and run together
    /// (`hnn::realization`). These are the wave's faces; the tree part is added at compare
    /// ([`PendingRatio::against`]).
    pub fn read_charted<'c>(
        &self,
        field: &'c Field,
        constitution: &impl ConstitutionRead,
        charts: &mut Charts,
    ) -> Result<(Word<'c>, Faces), HnnError> {
        self.read_on(field, constitution, charts, &WordOpening::Rest)
    }

    /// A detached call may intentionally evaluate another material/opening as a counterfactual;
    /// it does not authenticate resident continuation or rebind a frozen observation prefix.
    /// **The contemporary read on a reception's opening** ([`PendingRatio::open_on`]): what
    /// [`PendingRatio::read_charted`] returns, the word opened on `opening`.
    pub fn read_on<'c>(
        &self,
        field: &'c Field,
        constitution: &impl ConstitutionRead,
        charts: &mut Charts,
        opening: &WordOpening,
    ) -> Result<(Word<'c>, Faces), HnnError> {
        if self.prepared_input.is_some(){return Err(HnnError::Unadmitted{reason:"prepared input uses the typed native material read route"});}
        let word = self.open_on(field, constitution, charts, opening)?;
        self.read_word(field, constitution, word)
    }

    pub(crate) fn read_on_scoped<'c>(
        &self,
        scope: &mut crate::hnn::propagation::RingScope<'c>,
        charts: &mut Charts,
        opening: &WordOpening,
    ) -> Result<(Word<'c>, Faces), HnnError> {
        let field = scope.field();
        let material = scope.material();
        let word = self.open_on_scoped(scope, charts, opening)?;
        self.read_word(field, material, word)
    }

    pub(crate) fn open_on_scoped<'c>(
        &self,
        scope: &mut crate::hnn::propagation::RingScope<'c>,
        charts: &mut Charts,
        opening: &WordOpening,
    ) -> Result<Word<'c>, HnnError> {
        let current = self.current(scope.field())?;
        let field=scope.field();let theta=scope.material();
        let word=Word::open_received_scoped(scope, &current, &self.moment, charts, opening, &self.view)?;
        match &self.prepared_input{Some(p)=>p.apply(field,theta,self,word),None=>Ok(word)}
    }

    fn read_word<'c>(
        &self,
        field: &'c Field,
        constitution: &impl ConstitutionRead,
        mut word: Word<'c>,
    ) -> Result<(Word<'c>, Faces), HnnError> {
        let anchors = word.forward(&self.phases)?;
        self.read_forward_word(field, constitution, word, anchors)
    }

    pub(crate) fn read_on_scanned<'c>(
        &self,
        field: &'c Field,
        constitution: &impl ConstitutionRead,
        charts: &mut Charts,
        opening: &WordOpening,
        partitions: usize,
    ) -> Result<(Word<'c>, Faces, crate::hnn::word::scan::ForwardSpanReading), HnnError> {
        let mut word = self.open_on(field, constitution, charts, opening)?;
        let (anchors, span) = word.forward_scanned(&self.phases, partitions)?;
        let (word, faces) = self.read_forward_word(field, constitution, word, anchors)?;
        Ok((word, faces, span))
    }

    pub(crate) fn read_on_scoped_scanned<'c>(
        &self,
        scope: &mut crate::hnn::propagation::RingScope<'c>,
        charts: &mut Charts,
        opening: &WordOpening,
        partitions: usize,
    ) -> Result<(Word<'c>, Faces, crate::hnn::word::scan::ForwardSpanReading), HnnError> {
        let field = scope.field();
        let material = scope.material();
        let mut word = self.open_on_scoped(scope, charts, opening)?;
        let (anchors, span) = word.forward_scanned(&self.phases, partitions)?;
        let (word, faces) = self.read_forward_word(field, material, word, anchors)?;
        Ok((word, faces, span))
    }

    fn read_forward_word<'c>(
        &self,
        field: &'c Field,
        constitution: &impl ConstitutionRead,
        mut word: Word<'c>,
        anchors: Vec<Vec<Rat>>,
    ) -> Result<(Word<'c>, Faces), HnnError> {
        let reads = if matches!(
            constitution.receiving_layout(self.phases.ring()),
            Some(crate::hnn::constitution::ReceivingLayout::ArrivalContext { .. })
        ) {
            word.prepare_response()?;
            let column = word.response().expect("prepared response");
            indexed(anchors.len(), |j| {
                let crossing = self.phases.first_epoch() + j;
                self.phases.read_paired(
                    field,
                    constitution,
                    &anchors[j],
                    &column.records[crossing].anchors[self.phases.ring()],
                )
            })?
        } else {
            indexed(anchors.len(), |j| {
                self.phases.read(field, constitution, &anchors[j])
            })?
        };
        Ok((word, Faces::of_reads(&reads, self.phases.grain())?))
    }

    /// The frozen phase-specific observation prefixes paired with the ordinary causal
    /// addresses. Known targets advance only the latter; they never form an observation.
    pub fn observed_addresses(
        &self,
        known: &[usize],
    ) -> Result<Option<Vec<ObservedAddress>>, HnnError> {
        if self.phases.observation_partition().is_none() {
            return Ok(None);
        }
        let paths = self.observation.as_ref().ok_or(HnnError::Unadmitted {
            reason: "receiving observation context has not been realized",
        })?;
        let causal = self.addresses(known)?;
        if paths.len() != causal.len() {
            return Err(HnnError::Unadmitted {
                reason: "observation phase count differs from causal addresses",
            });
        }
        Ok(Some(
            paths
                .iter()
                .zip(causal)
                .map(|(bits, address)| {
                    Ok(ObservedAddress::new(
                        self.phases
                            .observation_partition()
                            .expect("checked above")
                            .path(bits.clone())?,
                        address,
                    ))
                })
                .collect::<Result<Vec<_>, HnnError>>()?,
        ))
    }

    pub(crate) fn with_prepared_input(mut self,cut:crate::hnn::reference::prepared_input::PreparedInputCut)->Result<Self,HnnError>{
        if cut.source_cells!=self.moment.cells() || cut.lift!=self.anchor || cut.commit!=self.commit{return Err(HnnError::Unadmitted{reason:"prepared cut matches its actual source ratio"});}
        self.prepared_input=Some(cut);Ok(self)
    }
    pub(crate) fn prepared_input(&self)->Option<&crate::hnn::reference::prepared_input::PreparedInputCut>{self.prepared_input.as_ref()}
    /// Native body route for an opt-in prepared ratio. Generic/counterfactual
    /// material reads do not silently discard its original input operation.
    pub fn read_on_native<'c>(&self,field:&'c Field,theta:&crate::hnn::constitution::Constitution,charts:&mut Charts,opening:&WordOpening)->Result<(Word<'c>,Faces),HnnError>{
        let word=Word::open_received_view(field,theta,&self.current(field)?,&self.moment,charts,opening,&self.view)?;
        let word=match &self.prepared_input{Some(p)=>p.apply(field,theta,self,word)?,None=>word};
        self.read_word(field,theta,word)
    }

    /// The contemporary tree faces at each phase's causal address given the epoch's known targets:
    /// what [`PendingRatio::against`] adds to the wave (read-only).
    pub(crate) fn tree_faces(
        &self,
        constitution: &impl ConstitutionRead,
        known: &[usize],
    ) -> Result<Vec<crate::compression::landmark::context::LandmarkFace>, HnnError> {
        if let Some(addresses) = self.observed_addresses(known)? {
            let ring = self.phases.ring();
            let tree = constitution
                .landmarks(ring)
                .ok_or(HnnError::MissingReceivingMap { ring })?;
            let window = tree.window_observed(&addresses, known)?;
            let splits = indexed(window.phases(), |j| Ok(window.splits(j)))?;
            crate::hnn::receiving::faces_of_splits(tree.declaration(), &splits, self.phases.grain())
        } else {
            self.phases.tree_faces(constitution, &self.address, known)
        }
    }

    /// **The epoch's faces at compare** (module header; the landmark tree): the contemporary tree
    /// read at each phase's causal address given the epoch's known targets, added to the wave's
    /// faces. At a compare every target is known; at a release none is, and every phase reads the
    /// address where the epoch opens (`hnn::receiving::ActiveAddress::phase`).
    pub fn against(
        &self,
        constitution: &impl ConstitutionRead,
        wave: &Faces,
        known: &[usize],
    ) -> Result<Against, HnnError> {
        let trees = self.tree_faces(constitution, known)?;
        Ok(Against {
            faces: self.phases.combine(wave, &trees)?,
            trees,
        })
    }

    /// **The epoch scored by the receiver's population** (ruling A, THE_REBUILD U1,
    /// `hnn::receiving::score`): the contemporary population weighs the tree's faces against the
    /// combined faces at the targets by the families' likelihoods, each phase's code length under
    /// it, and the steps its deposit applies. Refused when the constitution carries no population on
    /// the receiving ring.
    pub fn scored(
        &self,
        constitution: &impl ConstitutionRead,
        against: &Against,
        targets: &[usize],
    ) -> Result<Scored, HnnError> {
        let ring = self.phases.ring();
        let population = constitution
            .population(ring)
            .ok_or(HnnError::MissingReceivingMap { ring })?;
        crate::hnn::receiving::score(population, ring, &against.faces, &against.trees, targets)
    }

    /// **The contemporary read against targets**: the wave's read ([`PendingRatio::read_charted`])
    /// and the combined faces at the targets' addresses ([`PendingRatio::against`]).
    pub fn read_against<'c>(
        &self,
        field: &'c Field,
        constitution: &impl ConstitutionRead,
        charts: &mut Charts,
        targets: &[usize],
    ) -> Result<(Word<'c>, Against), HnnError> {
        self.read_against_on(field, constitution, charts, targets, &WordOpening::Rest)
    }

    /// The contemporary read against targets on a reception's opening ([`PendingRatio::read_on`]).
    pub fn read_against_on<'c>(
        &self,
        field: &'c Field,
        constitution: &impl ConstitutionRead,
        charts: &mut Charts,
        targets: &[usize],
        opening: &WordOpening,
    ) -> Result<(Word<'c>, Against), HnnError> {
        let (word, wave) = self.read_on(field, constitution, charts, opening)?;
        let against = self.against(constitution, &wave, targets)?;
        Ok((word, against))
    }

    /// The resident's explicitly provenance-preserving successor reread. The original
    /// observation prefix is fixed cut metadata, while the successor wave/tree are recomputed.
    /// The caller retains the native arrived slot's unchanged WordOpening and lineage; a local
    /// commit comparison alone is not authentication of arbitrary detached constitutions.
    pub fn read_successor_against_on<'c>(
        &self,
        field: &'c Field,
        constitution: &crate::hnn::constitution::Constitution,
        charts: &mut Charts,
        targets: &[usize],
        opening: &WordOpening,
    ) -> Result<(Word<'c>, Against), HnnError> {
        if constitution.commit() < self.commit {
            return Err(HnnError::Unadmitted {
                reason: "a successor reread cannot precede its producing commit",
            });
        }
        let (word,wave)=self.read_on_native(field,constitution,charts,opening)?;
        let against=self.against(constitution,&wave,targets)?;
        Ok((word,against))
    }

    /// The pending ratio's exact bits: the anchor's integers, the moment's dense code and the
    /// active suffix address.
    pub fn bits(&self) -> u64 {
        self.anchor.iter().map(|x| x.bits() + 1).sum::<u64>()
            + self.view.bits()
            + self
                .observation
                .as_ref()
                .map_or(0, |paths| paths.iter().map(|p| p.len() as u64).sum::<u64>())
            + self.moment.dense_bits()
            + self.address.bits(self.moment.alphabet())
    }
}
