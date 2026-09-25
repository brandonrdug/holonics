//! **The pending ratio: a delayed comparison read at the contemporary constitution.**
//!
//! [definition] A [`PendingRatio`] holds the producing operands only (design (a), "The pending
//! read"; guard 3): the anchor, the lift point `λ` at the cut; a copy of the encoder moment's counts
//! `M` at the cut (never `m̃`, and never a handle to a moment that later ingests extend); its
//! [`ReceivingPhases`]; and the commit it was produced at. Every word opens at zero change, so the
//! anchor needs no waves. A read ([`PendingRatio::open`]) recomputes `m̃ = ⟨M, E_now⟩` and runs the
//! word at the contemporary constitution, `q` included:
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
//! use holonics::hnn::{Current, PendingRatio, ReceivingPhases};
//! use holonics::hnn::ratio::Faces;
//! // A face is not the moment a pending ratio is produced from (guard 3).
//! fn from_face(current: &Current, faces: &Faces, phases: &ReceivingPhases) -> PendingRatio {
//!     PendingRatio::produce(current, faces, phases, 0)
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
use crate::hnn::field::{ConstitutionRead, Current, Field};
use crate::hnn::moment::SourceMoment;
use crate::hnn::ratio::Faces;
use crate::hnn::receiving::ReceivingPhases;
use crate::hnn::word::Word;

/// [definition] **A pending ratio**: the producing anchor `λ`, the encoder moment `M`, the
/// receiving phases and the producing commit. See the module header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PendingRatio {
    anchor: Vec<BigInt>,
    moment: SourceMoment,
    phases: ReceivingPhases,
    commit: u64,
}

impl PendingRatio {
    /// **Produce a pending ratio at the cut**: the lift point, a copy of the moment's counts, the
    /// receiving phases and the commit. These are operands only.
    pub fn produce(
        current: &Current,
        moment: &SourceMoment,
        phases: &ReceivingPhases,
        commit: u64,
    ) -> Self {
        Self {
            anchor: current.lift().to_vec(),
            moment: moment.clone(),
            phases: phases.clone(),
            commit,
        }
    }

    /// The producing anchor `λ`.
    pub fn anchor(&self) -> &[BigInt] {
        &self.anchor
    }

    /// The encoder moment's counts at the cut.
    pub fn moment(&self) -> &SourceMoment {
        &self.moment
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

    /// **Open the word at the contemporary constitution** on the anchor and the moment's counts.
    pub fn open<'c>(
        &self,
        field: &'c Field,
        constitution: &impl ConstitutionRead,
    ) -> Result<Word<'c>, HnnError> {
        Word::open(field, constitution, &self.current(field)?, &self.moment)
    }

    /// **The contemporary read**: the word run over its receiving window and the faces read at the
    /// receiver's grain. Returns the word (for its return) and the faces.
    pub fn read<'c>(
        &self,
        field: &'c Field,
        constitution: &impl ConstitutionRead,
    ) -> Result<(Word<'c>, Faces), HnnError> {
        let current = self.current(field)?;
        let mut word = self.open(field, constitution)?;
        let anchors = word.forward(&self.phases)?;
        let reads = anchors
            .iter()
            .map(|anchor| self.phases.read(field, constitution, &current, anchor))
            .collect::<Result<Vec<_>, _>>()?;
        Ok((word, Faces::of_reads(&reads, self.phases.grain())?))
    }

    /// The pending ratio's exact bits: the anchor's integers and the moment's dense code.
    pub fn bits(&self) -> u64 {
        self.anchor.iter().map(|x| x.bits() + 1).sum::<u64>() + self.moment.dense_bits()
    }
}
