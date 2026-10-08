//! A prepared source port, its actual participating world, and the reached receiving return.
//!
//! [agent-inferred; Refs #73 #62] The request constrains a prospective native carrier;
//! it is never the observed consequence. `y(u)=y(0)+R P A I B u` uses the current
//! source, interior, material and absolute pump clock. Only a unique whole preimage
//! releases a control. A plural affine fibre and an annihilator obstruction remain whole.
//! The actual Robin world supplies q after execution; the same Word returns p-q to R.
//! The observer-only publication preserves the executed current and its full conditional
//! contact tangent. Neither the requested carrier, an old Word nor an earlier R snapshot
//! is installed as resident retention.
//!
//! This is an exact identity-chart, fixed-frame, one-source/one-future consumer. It is
//! not a general action-selection law: an informative probe of retained alternatives
//! still needs its complete finite partition and the existing receiver::release join.
//! Model preparation work and actual world-port work are distinct supplies. The world
//! reflection replaces the nonloaded source storage after each native full tick, before
//! the next tick, with boundary work equal to minus the actual World port work. The
//! common Resident keeps the World state and clock. A held HNN-only contact differential
//! is refused before this coupled future: its World tangent/finite certificate is owed.

mod world;
pub use world::{BoundJointWorld, NativeEncounter, NativeEncounterFailure, WaveJointStep};

use super::{PhysicalReceiver, communication::PhysicalBoundary};
use crate::hnn::HnnError;
use crate::hnn::constitution::{Constitution, DepositReading};
use crate::hnn::encoding::Encoded;
use crate::hnn::field::{Current, Field, FieldMaterial, ReceiverDeclaration};
use crate::hnn::moment::SourceMoment;
use crate::hnn::prediction::{
    DamagedSection, PhysicalRepair, RepairedCell, StationRead, Unresolved,
};
use crate::hnn::receiving::ReceivingPhases;
use crate::hnn::word::action::{
    AppliedPortPreparation, PortPreparation, PortPreparationReceipt, ProspectiveControl,
};
use crate::hnn::word::variation::VariationReading;
use crate::hnn::word::{
    FieldBalance, NativeReceivingReturn, ReceptionCarry, SourceOpeningReceipt, SourceWaveReturn,
    Word, WordBalance,
};
use crate::holon::HolonState;
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;
use num_traits::Zero;
use std::sync::Arc;

/// An exterior attribution control from an actual earlier receiving material. Its private
/// chart/frame identity bars an arbitrary replacement matrix or an old physical opening.
#[derive(Debug)]
pub struct ReceivingSnapshot {
    field: Field,
    current: Current,
    chart: Encoded,
    receiver: ReceiverDeclaration,
    producing_commit: u64,
    map: ExactRatMatrix,
}

impl ReceivingSnapshot {
    pub fn producing_commit(&self) -> u64 {
        self.producing_commit
    }
    pub fn map(&self) -> &ExactRatMatrix {
        &self.map
    }
}

/// The native actual comparison, optional nonzero material deposition, and held differential
/// rebound. Absence of a deposit is a zero/absent comparison, not a fabricated normal sample.
#[derive(Debug)]
pub struct ActionComparison {
    pub returned: NativeReceivingReturn,
    pub publication: Option<DepositReading>,
    pub receiving_before: ExactRatMatrix,
    pub receiving_after: ExactRatMatrix,
    pub receiving_variation: Option<VariationReading>,
}

/// The complete blind native boundary and actual world receipt precede the learned publication.
/// A refused return leaves the already published blind carry and old material in place.
#[derive(Debug)]
pub struct ActionReception {
    pub boundary: PhysicalBoundary,
    pub opening: SourceOpeningReceipt,
    pub preparation: PortPreparationReceipt,
    pub balances: Vec<FieldBalance>,
    pub word: WordBalance,
    pub source_returns: Vec<SourceWaveReturn>,
    pub applied: AppliedPortPreparation,
    pub encounter: NativeEncounter,
    pub carry: ReceptionCarry,
    pub comparison: Result<ActionComparison, HnnError>,
}

impl ActionReception {
    pub fn closes(&self) -> bool {
        self.opening.closes()
            && self.preparation.closes()
            && self.word.closes()
            && self.opening.after == self.preparation.before
            && &self.word.open + &self.word.resonator_open == self.preparation.after
            && self.balances.iter().all(FieldBalance::closes)
            && self.carry.ticks == self.encounter.after_native_tick
            && self.source_returns.len() == self.encounter.steps().len()
            && self
                .source_returns
                .iter()
                .zip(self.encounter.steps())
                .all(|(returned, step)| {
                    returned.incident == step.incident
                        && returned.reflected == step.reflected
                        && returned.work == -&step.port_work
                        && self.encounter.before_native_tick + returned.tick == step.native_tick
                })
    }
}

#[derive(Debug)]
pub enum ActionCommunication {
    /// No native/world action is released from this full plural or obstructed relation.
    Held {
        prospective: ProspectiveControl,
    },
    Received(ActionReception),
    /// A world refusal after blind execution preserves both the native carry and every
    /// actual partial world state/receipt. It does not rewind a failed physical exploration.
    Interrupted(ActionInterruption),
}

#[derive(Debug)]
pub struct ActionInterruption {
    pub boundary: PhysicalBoundary,
    pub opening: SourceOpeningReceipt,
    pub preparation: PortPreparationReceipt,
    pub balances: Vec<FieldBalance>,
    pub word: WordBalance,
    pub source_returns: Vec<SourceWaveReturn>,
    pub applied: AppliedPortPreparation,
    pub encounter: NativeEncounterFailure,
    pub carry: ReceptionCarry,
}

/// A bound, unrun preparation. Borrowing the receiver bars interleaved material/current edits.
pub struct PreparedPhysicalAction<'r, 'f> {
    owner: &'r mut PhysicalReceiver<'f>,
    word: Word<'f>,
    prospective: ProspectiveControl,
    section: DamagedSection,
    source_length: usize,
    receiver_index: usize,
    opening: SourceOpeningReceipt,
}

impl PreparedPhysicalAction<'_, '_> {
    pub fn prospective(&self) -> &ProspectiveControl {
        &self.prospective
    }
    pub fn source_chart(&self) -> &Encoded {
        self.section.chart()
    }
    pub fn producing_commit(&self) -> u64 {
        self.prospective.producing_commit()
    }
    pub fn current(&self) -> &Current {
        self.prospective.current()
    }
    pub fn opened_at(&self) -> usize {
        self.prospective.opened_at()
    }
    pub fn receiving_phases(&self) -> &ReceivingPhases {
        self.prospective.phases()
    }

    /// Execute against the one actual World retained by this receiver's common Resident.
    /// A plural fibre remains held; no World branch, reset or guessed point is released.
    pub fn encounter(self) -> Result<ActionCommunication, HnnError> {
        let Self {
            owner,
            word,
            prospective,
            section,
            source_length,
            receiver_index,
            opening,
        } = self;
        if prospective.unique_control().is_none() {
            return Ok(ActionCommunication::Held { prospective });
        }
        let phases = prospective.phases().clone();
        if owner.resident.held_contact_variation().is_some() {
            return Err(HnnError::Unadmitted {
                reason: "the held HNN-only contact differential has no actual World tangent and finite ray",
            });
        }
        let (mut word, preparation, applied) = prospective.prepare(word)?;
        word.admit_source_boundary(applied.ring())?;
        owner
            .resident
            .participating_world()
            .ok_or(HnnError::Unadmitted {
                reason: "an actual retained participating World precedes execution",
            })?
            .admit(
                section.chart(),
                applied.actual_source_wave(),
                owner.field.ring(applied.ring()).admittance(),
                owner.field.step(),
                word.opened_at(),
            )?;
        let producing = owner.constitution().clone();
        let epochs = phases.epochs().collect::<Vec<_>>();
        let encounter = owner.resident.participating_world_mut()?.execute_word(
            &mut word,
            applied.ring(),
            phases.junction_steps(),
            &epochs,
            applied.compared(),
            phases.grain(),
        );
        // Keep every actually executed physical state, including an interrupted interaction.
        // Neither a rejected comparison nor a World refusal is permission to rewind a trial.
        let carry = word.reception_end()?;
        owner.resident.publish_reception_with_variation(
            None,
            HolonState::at(carry.clone(), producing.commit()),
            None,
            None,
            section.chart(),
            None,
        )?;
        let reads = phases
            .epochs()
            .enumerate()
            .filter_map(|(station, crossing)| {
                word.anchor(crossing, phases.ring()).map(|anchor| {
                    Ok(StationRead {
                        station,
                        crossing,
                        tick: word.opened_at() + crossing,
                        read: phases.read(owner.field, &producing, owner.current(), anchor)?,
                    })
                })
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        let blind = PhysicalRepair {
            cells: section
                .placed()
                .into_iter()
                .map(|c| match c {
                    Some(class) => RepairedCell::Intact(class),
                    None => RepairedCell::Held {
                        fibre: (0..owner.field.alphabet()).collect(),
                        unresolved: Unresolved::UncertifiedDomain,
                    },
                })
                .collect(),
            reads,
            domains: vec![None; phases.aperture()],
            opening,
            balances: word.field_balances().to_vec(),
            word: WordBalance::of(&word.released()?),
            carry,
        };
        let source_returns = word.source_returns().to_vec();
        let boundary = PhysicalBoundary::of_suffix(
            &blind,
            section.chart().clone(),
            source_length,
            phases.grain(),
            false,
        );
        let encounter = match encounter {
            Ok(encounter) => encounter,
            Err(encounter) => {
                return Ok(ActionCommunication::Interrupted(ActionInterruption {
                    boundary,
                    opening: blind.opening,
                    preparation,
                    balances: blind.balances,
                    word: blind.word,
                    source_returns,
                    applied,
                    encounter,
                    carry: blind.carry,
                }));
            }
        };
        if !blind.opening.closes()
            || !blind.word.closes()
            || blind.opening.after != preparation.before
            || &blind.word.open + &blind.word.resonator_open != preparation.after
            || blind.balances.iter().any(|b| !b.closes())
            || encounter.chart() != section.chart()
            || encounter.before_native_tick != word.opened_at()
            || encounter.after_native_tick != blind.carry.ticks
        {
            return Err(HnnError::Unadmitted {
                reason: "the co-clock native/World passage closes its actual work and chart",
            });
        }
        // Actual World return changes the model's prospective carrier. Request equality is
        // therefore not an acceptance of this executed coupled path. Only producer/clock match.
        applied.verify_producer(&word)?;
        let comparison = (|| {
            let returned = word.return_observed_receiving(
                receiver_index,
                &applied,
                encounter.observed().to_vec(),
            )?;
            let before = producing
                .receiving_map(phases.ring())
                .ok_or(HnnError::MissingReceivingMap {
                    ring: phases.ring(),
                })?
                .clone();
            let (publication, receiving_variation) = match returned.deposit.as_ref() {
                None => (None, None),
                Some(deposit) => {
                    let (material, reading) = producing.deposited(deposit)?;
                    let variation = owner.resident.publish_receiving_translation(
                        material.clone(),
                        HolonState::at(blind.carry.clone(), material.commit()),
                        section.chart(),
                    )?;
                    (Some(reading), variation)
                }
            };
            let after = owner
                .constitution()
                .receiving_map(phases.ring())
                .ok_or(HnnError::MissingReceivingMap {
                    ring: phases.ring(),
                })?
                .clone();
            Ok(ActionComparison {
                returned,
                publication,
                receiving_before: before,
                receiving_after: after,
                receiving_variation,
            })
        })();
        let carry = owner
            .resident
            .carried()
            .ok_or(HnnError::ContinuingState {
                what: "the actual coupled passage's continuing current",
            })?
            .clone();
        Ok(ActionCommunication::Received(ActionReception {
            boundary,
            opening: blind.opening,
            preparation,
            balances: blind.balances,
            word: blind.word,
            source_returns,
            applied,
            encounter,
            carry,
            comparison,
        }))
    }
}

impl<'f> PhysicalReceiver<'f> {
    /// Bind once. Both participants' actual current survives into every later action and view.
    /// No API drops or substitutes this World to unlock an unsupported admitted future.
    pub fn bind_world(&mut self, world: BoundJointWorld) -> Result<(), HnnError> {
        self.resident.bind_participating_world(world)
    }

    pub fn participating_world(&self) -> Option<&BoundJointWorld> {
        self.resident.participating_world()
    }

    /// Bind one actual earlier R for an exterior matched-control reading. No old current,
    /// normal statistics, World state or Word is replayed by this snapshot.
    pub fn receiving_snapshot(
        &self,
        receiver: &ReceiverDeclaration,
    ) -> Result<ReceivingSnapshot, HnnError> {
        self.action_receiver_index(receiver)?;
        Ok(ReceivingSnapshot {
            field: self.field.clone(),
            current: self.current().clone(),
            chart: self
                .resident
                .receiving_chart()
                .ok_or(HnnError::Unadmitted {
                    reason: "an actual producing receiving chart precedes its snapshot",
                })?
                .clone(),
            receiver: receiver.clone(),
            producing_commit: self.constitution().commit(),
            map: self
                .constitution()
                .receiving_map(receiver.ring)
                .ok_or(HnnError::MissingReceivingMap {
                    ring: receiver.ring,
                })?
                .clone(),
        })
    }

    pub fn plan_action(
        &self,
        source: &Encoded,
        receiver: &ReceiverDeclaration,
        preparation: &PortPreparation,
        requested: &[Vec<Rat>],
        compared: &[bool],
    ) -> Result<ProspectiveControl, HnnError> {
        let (_, phases, word, _) =
            self.action_opening(source, receiver, preparation, compared, self.constitution())?;
        word.prospective_port_preparation(&phases, preparation, requested, compared)
    }

    /// Recompute at PRESENT source/current/carry/operators with only the actual earlier R.
    /// This is an exterior attribution diagnostic, not a retained or executed counterfactual.
    pub fn plan_action_with_receiving(
        &self,
        snapshot: &ReceivingSnapshot,
        source: &Encoded,
        receiver: &ReceiverDeclaration,
        preparation: &PortPreparation,
        requested: &[Vec<Rat>],
        compared: &[bool],
    ) -> Result<ProspectiveControl, HnnError> {
        if &snapshot.field != self.field
            || &snapshot.current != self.current()
            || &snapshot.receiver != receiver
            || snapshot.chart != source.part(0..0)?
        {
            return Err(HnnError::Unadmitted {
                reason: "the earlier actual R snapshot keeps this complete chart, field and source frame",
            });
        }
        let material = self.constitution().clone().with_ports(
            receiver.ring,
            None,
            None,
            Some(snapshot.map.clone()),
        )?;
        let (_, phases, word, _) =
            self.action_opening(source, receiver, preparation, compared, &material)?;
        word.prospective_port_preparation(&phases, preparation, requested, compared)
    }

    pub fn prepare_action<'r>(
        &'r mut self,
        source: &Encoded,
        receiver: &ReceiverDeclaration,
        preparation: &PortPreparation,
        requested: &[Vec<Rat>],
        compared: &[bool],
    ) -> Result<PreparedPhysicalAction<'r, 'f>, HnnError> {
        let receiver_index = self.action_receiver_index(receiver)?;
        let (section, phases, word, opening) =
            self.action_opening(source, receiver, preparation, compared, self.constitution())?;
        let prospective =
            word.prospective_port_preparation(&phases, preparation, requested, compared)?;
        Ok(PreparedPhysicalAction {
            owner: self,
            word,
            prospective,
            section,
            source_length: source.len(),
            receiver_index,
            opening,
        })
    }

    fn action_receiver_index(&self, receiver: &ReceiverDeclaration) -> Result<usize, HnnError> {
        self.field
            .receivers()
            .iter()
            .position(|r| r == receiver)
            .ok_or(HnnError::Unadmitted {
                reason: "the native action binds an actually declared Field receiver",
            })
    }

    fn action_opening(
        &self,
        source: &Encoded,
        receiver: &ReceiverDeclaration,
        preparation: &PortPreparation,
        compared: &[bool],
        material: &Constitution,
    ) -> Result<
        (
            DamagedSection,
            ReceivingPhases,
            Word<'f>,
            SourceOpeningReceipt,
        ),
        HnnError,
    > {
        self.resident.admit_exact_current_point()?;
        if self.resident.held_contact_variation().is_some() {
            return Err(HnnError::Unadmitted {
                reason: "actual World action cannot discard the held HNN-only contact differential",
            });
        }
        self.action_receiver_index(receiver)?;
        if self.field.sources() != [preparation.ring()]
            || self.current() != &Current::at_rest(self.field)
            || self.current().lift().iter().any(|lift| !lift.is_zero())
            || source.is_empty()
            || source.len().checked_add(1) != Some(receiver.aperture)
            || compared.len() != receiver.aperture
            || compared[..source.len()].iter().any(|x| *x)
            || !compared[source.len()]
        {
            return Err(HnnError::Unadmitted {
                reason: "the first actual world consumer declares one source, one future comparison and the fixed identity source frame",
            });
        }
        let section =
            DamagedSection::of_runs(receiver.aperture, source, vec![(0, source.clone())])?;
        self.resident.admit_receiving_chart(section.chart())?;
        let phases = ReceivingPhases::declare(self.field, material, self.current(), receiver)?;
        section.admit(self.field, material, &phases)?;
        let mut moment = SourceMoment::open_with(self.field, self.current(), material)?;
        moment = moment.station_section(
            self.field,
            self.current(),
            preparation.ring(),
            &section.placed(),
        )?;
        let (word, opening) = Word::open_source_exact_received(
            self.field,
            material,
            self.current(),
            Arc::new(moment),
            &self.resident.reception_opening(),
        )?;
        Ok((section, phases, word, opening))
    }
}
