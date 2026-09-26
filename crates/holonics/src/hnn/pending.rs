//! **The pending ratio: a delayed comparison read at the contemporary constitution.**
//!
//! [definition] A [`PendingRatio`] holds the producing operands only (design (a), "The pending
//! read"; guard 3): the anchor, the lift point `λ` at the cut; a copy of the encoder moment's counts
//! `M` at the cut (never `m̃`, and never a handle to a moment that later ingests extend); a copy of
//! the receiving parametron's active suffix address at the cut (`hnn::receiving::ActiveAddress`,
//! its receiver's `D` letters); its [`ReceivingPhases`]; and the commit it was produced at. Every
//! word opens at zero change, so the anchor needs no waves. A read ([`PendingRatio::open`])
//! recomputes `m̃ = ⟨M, E_now⟩` and runs the word at the contemporary constitution, `q` included;
//! at compare, the contemporary landmark tree is read at each phase's causal address, the copied
//! suffix after the window's earlier targets (Decision 28, [`PendingRatio::against`]):
//!
//! - `refine` publishes only faces, with no commit flag, so no source is counted twice and `E` is
//!   never mixed across two cuts;
//! - with no intervening deposit a delayed read equals the immediate one exactly; after a deposit
//!   it returns the residual against the emitted face (Lean `HNN/Retention.contemporary_read`, on
//!   the abstract block operator; the concrete-tick bridge is owed in #62);
//! - the producing anchor is a clock reading, not material, and no frozen cut of earlier material.
//!
//! No constructor accepts a material, a word or a face. The guarantee is structural: the fields are
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

use crate::hnn::HnnError;
use crate::hnn::chart::Charts;
use crate::hnn::field::{ConstitutionRead, Current, Field};
use crate::hnn::landmark::{LandmarkFace, Letter};
use crate::hnn::moment::SourceMoment;
use crate::hnn::ratio::Faces;
use crate::hnn::realization::indexed;
use crate::hnn::receiving::{ActiveAddress, ReceivingPhases, Scored};
use crate::hnn::word::Word;

/// [definition] **A pending ratio**: the producing anchor `λ`, the encoder moment `M`, the active
/// suffix address, the receiving phases and the producing commit. See the module header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PendingRatio {
    anchor: Vec<BigInt>,
    moment: SourceMoment,
    address: ActiveAddress,
    phases: ReceivingPhases,
    commit: u64,
}

/// [definition] **A window's faces at compare**: the combined faces (the tree's at each phase's
/// address plus the wave's) and the tree faces they were formed from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Against {
    pub faces: Faces,
    pub trees: Vec<LandmarkFace>,
}

impl PendingRatio {
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
        })
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

    /// **The window's phase addresses** given its known targets
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

    /// **Open the word, its solves warm-started from a resident's charts** (Decision 24).
    pub fn open_charted<'c>(
        &self,
        field: &'c Field,
        constitution: &impl ConstitutionRead,
        charts: &mut Charts,
    ) -> Result<Word<'c>, HnnError> {
        Word::open_charted(
            field,
            constitution,
            &self.current(field)?,
            &self.moment,
            charts,
        )
    }

    /// **The contemporary read**: the word run over its receiving window and the wave's faces read
    /// at the receiver's grain, every solve seeded afresh. Returns the word (for its return) and the
    /// faces.
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
        let current = self.current(field)?;
        let mut word = self.open_charted(field, constitution, charts)?;
        let anchors = word.forward(&self.phases)?;
        let reads = indexed(anchors.len(), |j| {
            self.phases.read(field, constitution, &current, &anchors[j])
        })?;
        Ok((word, Faces::of_reads(&reads, self.phases.grain())?))
    }

    /// **The window's faces at compare** (module header; Decision 28): the contemporary tree read at
    /// each phase's causal address given the window's known targets, added to the wave's faces.
    /// At a compare every target is known; at a release none is, and every phase reads the
    /// window's opening address (`hnn::receiving::ActiveAddress::phase`).
    pub fn against(
        &self,
        constitution: &impl ConstitutionRead,
        wave: &Faces,
        known: &[usize],
    ) -> Result<Against, HnnError> {
        let trees = self.phases.tree_faces(constitution, &self.address, known)?;
        Ok(Against {
            faces: self.phases.combine(wave, &trees)?,
            trees,
        })
    }

    /// **The window scored by the receiver's mixture** (ruling A, `hnn::receiving::Mixture`): the
    /// contemporary mixture's `β` weighs the tree's faces against the combined faces at the
    /// targets, each phase's code length under the mixture, and the steps its deposit applies.
    /// Refused when the constitution carries no mixture on the receiving ring.
    pub fn scored(
        &self,
        constitution: &impl ConstitutionRead,
        against: &Against,
        targets: &[usize],
    ) -> Result<Scored, HnnError> {
        let ring = self.phases.ring();
        constitution
            .mixture(ring)
            .ok_or(HnnError::MissingReceivingMap { ring })?
            .score(ring, &against.faces, &against.trees, targets)
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
        let (word, wave) = self.read_charted(field, constitution, charts)?;
        let against = self.against(constitution, &wave, targets)?;
        Ok((word, against))
    }

    /// The pending ratio's exact bits: the anchor's integers, the moment's dense code and the
    /// active suffix address.
    pub fn bits(&self) -> u64 {
        self.anchor.iter().map(|x| x.bits() + 1).sum::<u64>()
            + self.moment.dense_bits()
            + self.address.bits(self.moment.alphabet())
    }
}
