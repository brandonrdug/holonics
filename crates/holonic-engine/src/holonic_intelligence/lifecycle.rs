/// A foreign-realization boundary return has physically separate productive, cold, and open lanes.
pub trait DismantlingBoundaryReturn {
    type Productive;
    type ColdWitness;
    type Insufficiency;

    fn productive(&self) -> &Self::Productive;
    fn cold_witness(&self) -> &Self::ColdWitness;
    fn insufficiency(&self) -> &Self::Insufficiency;
}

/// One inference cut through which reusable morphology remains fixed.
pub trait InferenceCirculation {
    type Morphology: PartialEq;
    type EnteringOccurrence;
    type ActiveSection;
    type ConductedSection;
    type Receiver;
    type Face;
    type EmittedOccurrence;
    type Lineage;
    type Reconstruction;
    type OpenObligation;

    fn predecessor_morphology(&self) -> &Self::Morphology;
    fn entering_occurrence(&self) -> &Self::EnteringOccurrence;
    fn active_section(&self) -> &Self::ActiveSection;
    fn conducted_section(&self) -> &Self::ConductedSection;
    fn receiver(&self) -> &Self::Receiver;
    fn face(&self) -> &Self::Face;
    fn emitted_occurrence(&self) -> &Self::EmittedOccurrence;
    fn lineage(&self) -> &Self::Lineage;
    fn reconstruction(&self) -> &Self::Reconstruction;
    fn successor_morphology(&self) -> &Self::Morphology;
    fn open_obligations(&self) -> &[Self::OpenObligation];
    fn morphology_is_fixed(&self) -> bool {
        self.successor_morphology() == self.predecessor_morphology()
    }
}

/// One genuinely later return which may change reusable morphology.
pub trait CultivationLifecycle {
    type Morphology: PartialEq;
    type Occurrence;
    type Difference;
    type Delta;
    type Probe;
    type Face: PartialEq;
    type RestIdentity;

    fn predecessor(&self) -> &Self::Morphology;
    fn emitted_occurrence(&self) -> &Self::Occurrence;
    fn returned_occurrence(&self) -> &Self::Occurrence;
    fn returned_difference(&self) -> &Self::Difference;
    fn proposed_delta(&self) -> &Self::Delta;
    fn successor(&self) -> &Self::Morphology;
    fn witness_probe(&self) -> &Self::Probe;
    fn predecessor_face(&self) -> &Self::Face;
    fn successor_face(&self) -> &Self::Face;
    fn successor_rest(&self) -> &Self::RestIdentity;
    fn precedes(&self, left: &Self::Occurrence, right: &Self::Occurrence) -> bool;
    fn remounted_successor(&self) -> &Self::Morphology;
    fn withdrawn_predecessor(&self) -> &Self::Morphology;

    fn return_is_later(&self) -> bool {
        self.precedes(self.emitted_occurrence(), self.returned_occurrence())
    }

    fn morphology_changed(&self) -> bool {
        self.successor() != self.predecessor()
    }

    fn later_conduct_changed(&self) -> bool {
        self.successor_face() != self.predecessor_face()
    }

    fn remount_is_exact(&self) -> bool {
        self.remounted_successor() == self.successor()
    }

    fn withdrawal_is_exact(&self) -> bool {
        self.withdrawn_predecessor() == self.predecessor()
    }
}

/// Exact codeword intake retains both its represented value and complete richer preimage.
pub trait ExactWeightPassage {
    type Source;
    type Code: PartialEq;
    type Native: PartialEq;

    fn encode(&self, source: &Self::Source) -> Self::Code;
    fn source_value(&self, source: &Self::Source) -> Self::Native;
    fn stored_value(&self, code: &Self::Code) -> Self::Native;
    fn residual(&self, source: &Self::Source) -> Self::Native;
    fn combine(&self, stored: &Self::Native, residual: &Self::Native) -> Self::Native;

    fn reconstructs_exactly(&self, source: &Self::Source) -> bool {
        let code = self.encode(source);
        let stored = self.stored_value(&code);
        let residual = self.residual(source);
        self.combine(&stored, &residual) == self.source_value(source)
    }

    fn same_code(&self, left: &Self::Source, right: &Self::Source) -> bool {
        self.encode(left) == self.encode(right)
    }
}
