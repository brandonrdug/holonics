//! Bounded reciprocal compatibility and one addressed, entailed source-port return (Refs #73 #62).
//!
//! Gamma contains COMPLETE (relation, a, b) tuples. Testimony never becomes an intact teacher.
//! This finite exterior capability is not native retention or a saved Word. A producing-cut token
//! expires on any native change. Only its common signed local packet can reach the paired source
//! normal owner; its reverse dyad is part of that one batch. No language-score veto is introduced.
//! Pair-slip certification remains the existing local law. General contextual families and two
//! independently plastic unknown materials remain outside this first finite join.

use super::*;
use crate::compression::keys::repair::PairRelation;
use crate::hnn::encoding::observed::PairedObservation;
use crate::hnn::paired::{PairedCarrier, PairingDeclaration};
use crate::hnn::reference::observed::ObservedCrib;
use crate::ratio::linear::ExactRatMatrix;

fn refused(reason: &'static str) -> HnnError {
    HnnError::Unadmitted { reason }
}
impl From<crate::hnn::paired::PairedDefect> for HnnError {
    fn from(error: crate::hnn::paired::PairedDefect) -> Self {
        Self::ReciprocalPaired(Box::new(error))
    }
}

/// A declared ambiguity channel, not a diagnosis of either participant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JointChannel {
    Exact,
    AtMostOneChanged,
    BothMayChange,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JointMember {
    pub hypothesis: usize,
    pub antecedent: usize,
    pub consequence: usize,
}

/// Explicit finite-work declaration, checked BEFORE Cartesian enumeration/allocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct JointBound {
    pub members: usize,
    pub visits: usize,
}

/// Work performed by compatibility refinement, separate from native material learning.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CompatibilityWork {
    pub tuple_visits: usize,
    pub relation_reads: usize,
    pub reused: bool,
}

/// Full family/assignment correlation. The finite menu and channels assert no real-world coverage.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JointFamily {
    menu: Vec<PairRelation>,
    transposed: bool,
    positions: [usize; 2],
    testimony: [usize; 2],
    channel: JointChannel,
    members: Vec<JointMember>,
    bound: JointBound,
    last_constraint: Option<Vec<JointMember>>,
    separating_return: Option<(usize, usize, Vec<BigInt>)>,
}

impl JointFamily {
    pub fn declare(
        menu: Vec<PairRelation>,
        positions: [usize; 2],
        testimony: [usize; 2],
        domains: [Vec<usize>; 2],
        channel: JointChannel,
        bound: JointBound,
    ) -> Result<(Self, CompatibilityWork), HnnError> {
        let Some(first) = menu.first() else {
            return Err(refused(
                "a reciprocal family needs a declared finite relation menu",
            ));
        };
        let classes = first.classes();
        let visits = menu
            .len()
            .checked_mul(classes)
            .and_then(|n| n.checked_mul(classes))
            .ok_or(HnnError::CountOverflow)?;
        if classes == 0
            || positions[0] == positions[1]
            || visits > bound.visits
            || bound.members == 0
            || menu.iter().any(|r| r.classes() != classes)
            || testimony.iter().any(|&c| c >= classes)
            || domains.iter().flatten().any(|&c| c >= classes)
        {
            return Err(refused(
                "the declared joint family alphabet, addresses and finite work/member bounds",
            ));
        }
        let mut members = Vec::new();
        let mut work = CompatibilityWork::default();
        for (hypothesis, relation) in menu.iter().enumerate() {
            for a in 0..classes {
                for b in 0..classes {
                    work.tuple_visits += 1;
                    if !domains[0].contains(&a) || !domains[1].contains(&b) {
                        continue;
                    }
                    let changed = usize::from(a != testimony[0]) + usize::from(b != testimony[1]);
                    if changed
                        > match channel {
                            JointChannel::Exact => 0,
                            JointChannel::AtMostOneChanged => 1,
                            JointChannel::BothMayChange => 2,
                        }
                    {
                        continue;
                    }
                    work.relation_reads += 1;
                    if relation.joins(a, b) {
                        if members.len() == bound.members {
                            return Err(refused("the declared joint member bound"));
                        }
                        members.push(JointMember {
                            hypothesis,
                            antecedent: a,
                            consequence: b,
                        });
                    }
                }
            }
        }
        Ok((
            Self {
                menu,
                transposed: false,
                positions,
                testimony,
                channel,
                members,
                bound,
                last_constraint: None,
                separating_return: None,
            },
            work,
        ))
    }
    pub fn members(&self) -> &[JointMember] {
        &self.members
    }
    pub fn positions(&self) -> [usize; 2] {
        self.positions
    }
    pub fn testimony(&self) -> [usize; 2] {
        self.testimony
    }

    /// Hypothetical relational future, preserving every complete member's support. It is not
    /// an observed class, emitted response, or branch-specific native field evolution.
    pub fn relational_future(&self) -> Result<Vec<(JointMember, usize)>, HnnError> {
        let visits = self
            .members
            .len()
            .checked_mul(self.menu[0].classes())
            .ok_or(HnnError::CountOverflow)?;
        if visits > self.bound.visits {
            return Err(refused("the finite relational future work bound"));
        }
        let mut future = Vec::new();
        for m in &self.members {
            for z in 0..self.menu[0].classes() {
                let r = &self.menu[m.hypothesis];
                let joined = if self.transposed {
                    r.joins(z, m.consequence)
                } else {
                    r.joins(m.consequence, z)
                };
                if joined {
                    future.push((m.clone(), z));
                }
            }
        }
        Ok(future)
    }

    /// An addressed return's declared support intersects COMPLETE members. It neither overwrites
    /// immutable testimony nor manufactures a new teacher. Identical support is an exact reuse.
    pub fn refine_return(
        &self,
        positions: [usize; 2],
        support: &[JointMember],
    ) -> Result<(Self, CompatibilityWork), HnnError> {
        if positions != self.positions || support.len() > self.bound.members {
            return Err(refused(
                "a returned constraint belongs to these same addressed finite members",
            ));
        }
        if self.last_constraint.as_deref() == Some(support) {
            return Ok((
                self.clone(),
                CompatibilityWork {
                    reused: true,
                    ..Default::default()
                },
            ));
        }
        if support.iter().any(|m| {
            m.hypothesis >= self.menu.len()
                || m.antecedent >= self.menu[0].classes()
                || m.consequence >= self.menu[0].classes()
        }) {
            return Err(refused(
                "a returned joint support is in the declared menu and alphabet",
            ));
        }
        let mut next = self.clone();
        let visits = next
            .members
            .len()
            .checked_mul(support.len())
            .ok_or(HnnError::CountOverflow)?;
        if visits > self.bound.visits {
            return Err(refused("the returned support finite work bound"));
        }
        next.members.retain(|m| support.contains(m));
        next.last_constraint = Some(support.to_vec());
        Ok((
            next,
            CompatibilityWork {
                tuple_visits: visits,
                ..Default::default()
            },
        ))
    }

    /// Transpose the relation, not the inverse of a possibly noninjective function.
    pub fn swapped(&self) -> Self {
        let mut next = self.clone();
        next.transposed = !next.transposed;
        next.positions.swap(0, 1);
        next.testimony.swap(0, 1);
        for m in &mut next.members {
            std::mem::swap(&mut m.antecedent, &mut m.consequence);
        }
        next.last_constraint = None;
        next
    }
}

/// Provenance of a derived packet. IDs are exterior testimony identifiers, never numeric model
/// features. E0 is calibration of the native source, not an intact participant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReturnOrigin {
    Observed,
    Entailed {
        family: String,
        menu: String,
        channel: String,
        source: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrientedPacket {
    pub source_ring: usize,
    pub receiver_ring: usize,
    pub positions: [usize; 2],
    pub lifts: [Vec<BigInt>; 2],
    pub turns: BigInt,
    pub classes: (usize, usize),
}

/// Ephemeral bound producing operand, never serialized as learned retention or replay history.
pub struct SourceReturnCut {
    field: Field,
    source_ring: usize,
    predecessor: ContinuingState,
    crib: ObservedCrib,
    pairing: PairingDeclaration,
    prior: ExactRatMatrix,
    family: JointFamily,
    packets: Vec<OrientedPacket>,
    origin: ReturnOrigin,
    prepared: std::sync::OnceLock<(Resident, ReciprocalReceipt)>,
}

#[derive(Clone, Debug)]
pub struct ReciprocalReceipt {
    pub packet: OrientedPacket,
    pub origin: ReturnOrigin,
    pub compatible_branches: usize,
    pub slip_before: Rat,
    pub slip_after: Rat,
    pub source_step: crate::hnn::constitution::SourceStep,
    pub paired_batches: usize,
    pub normal_preparations: usize,
    pub validation_word_openings: usize,
}
#[derive(Clone, Debug)]
pub enum ReciprocalOutcome {
    NoCompatibleBranch,
    Hold { branches: usize },
    Published(ReciprocalReceipt),
}

impl Reference {
    /// An exact actual later return restricts the declared relational future. Its raw class and
    /// full lift are read from witnessed native ingress, not supplied from a predicted branch.
    /// This first slice admits an exact new observation channel, not uncertain new latent returns.
    pub fn refine_joint_exact_return(
        &self,
        resident: &Resident,
        crib: &ObservedCrib,
        family: &JointFamily,
        source_ring: usize,
        returned_position: usize,
    ) -> Result<(JointFamily, CompatibilityWork), HnnError> {
        resident.admit_exact_current()?;
        if source_ring >= resident.field.rings().len() {
            return Err(refused("the returned source ring"));
        }
        let entry = crib
            .entries()
            .iter()
            .find(|e| e.position == returned_position)
            .ok_or_else(|| {
                refused("the separating return is an actual bounded witnessed occurrence")
            })?;
        let lift = crib.addressed_lift(
            &resident.field,
            &resident.current,
            returned_position,
            entry.class,
        )?;
        let old = crib.addressed_lift(
            &resident.field,
            &resident.current,
            family.positions[1],
            family.testimony[1],
        )?;
        let mut support = Vec::new();
        let mut visits = 0;
        for m in &family.members {
            let relation = &family.menu[m.hypothesis];
            let expected = BigInt::from(relation.offset()) * if family.transposed { -1 } else { 1 };
            if &lift[source_ring] - &old[source_ring] != expected {
                return Err(refused(
                    "the exact returned observation's signed relative source clock",
                ));
            }
            visits += 1;
            let joins = if family.transposed {
                relation.joins(entry.class, m.consequence)
            } else {
                relation.joins(m.consequence, entry.class)
            };
            if joins {
                support.push(m.clone());
            }
        }
        let (mut next, mut work) = family.refine_return(family.positions, &support)?;
        next.separating_return = Some((returned_position, entry.class, lift));
        work.relation_reads = visits;
        Ok((next, work))
    }
    pub fn bind_source_return(
        &self,
        resident: &Resident,
        crib: &ObservedCrib,
        pairing: &PairingDeclaration,
        prior: &ExactRatMatrix,
        source_ring: usize,
        family: &JointFamily,
        origin: ReturnOrigin,
    ) -> Result<SourceReturnCut, HnnError> {
        resident.admit_exact_current()?;
        if !resident.pending.is_empty()
            || !resident.staged.is_empty()
            || resident.arrived.is_some()
            || resident.moments.len() != 1
            || resident.opens != self.reception.opens()
            || source_ring >= resident.field.rings().len()
            || !resident.field.is_source(source_ring)
        {
            return Err(refused(
                "an addressed source return needs one committed live source and no open comparison",
            ));
        }
        if usize::try_from(
            resident
                .moments
                .values()
                .next()
                .expect("one moment")
                .cells(),
        )
        .map_err(|_| HnnError::CountOverflow)?
            != crib.next_position()
        {
            return Err(refused(
                "the addressed testimony ends at the actual source moment",
            ));
        }
        if let Some((position, class, lift)) = &family.separating_return {
            if crib.addressed_lift(&resident.field, &resident.current, *position, *class)? != *lift
            {
                return Err(refused(
                    "a saved separating return keeps its actual witnessed full lift",
                ));
            }
            let (supported, _) =
                self.refine_joint_exact_return(resident, crib, family, source_ring, *position)?;
            if supported.members != family.members {
                return Err(refused(
                    "every complete member retains support from its actual separating return",
                ));
            }
        }
        let newest = family.separating_return.as_ref().map_or_else(
            || family.positions[0].max(family.positions[1]),
            |(p, _, _)| *p,
        );
        if resident
            .source_return_frontier
            .get(&source_ring)
            .is_some_and(|&seen| newest <= seen)
        {
            return Err(refused(
                "this source encounter was already consumed; internal repropagation is not new evidence",
            ));
        }
        let [receiver] = resident.admitted.as_slice() else {
            return Err(refused(
                "one declared receiving section for an addressed return",
            ));
        };
        if matches!(origin, ReturnOrigin::Observed)
            && family
                .members
                .iter()
                .any(|m| [m.antecedent, m.consequence] != family.testimony)
        {
            return Err(refused(
                "a derived latent packet is Entailed, never directly Observed testimony",
            ));
        }
        let boundary = PairedObservation::admit(&resident.field, &resident.constitution, pairing)?;
        boundary.check_material(&resident.constitution)?;
        let port = resident
            .constitution
            .source_port(source_ring)
            .ok_or(HnnError::MissingSourcePort { ring: source_ring })?;
        let carrier = PairedCarrier::admit(&resident.field, source_ring, pairing, port)?;
        // Calibration must carry the SAME admitted dyad and full source dimensions.
        PairedCarrier::admit(&resident.field, source_ring, pairing, prior)?;
        let _ = carrier;
        let mut lifts = Vec::new();
        for (&position, &class) in family.positions.iter().zip(&family.testimony) {
            lifts.push(crib.addressed_lift(&resident.field, &resident.current, position, class)?);
        }
        let turns = &lifts[1][source_ring] - &lifts[0][source_ring];
        let mut packets = Vec::new();
        for member in &family.members {
            let relation = &family.menu[member.hypothesis];
            let expected = BigInt::from(relation.offset()) * if family.transposed { -1 } else { 1 };
            let joins = if family.transposed {
                relation.joins(member.consequence, member.antecedent)
            } else {
                relation.joins(member.antecedent, member.consequence)
            };
            if turns != expected || !joins {
                return Err(refused(
                    "the joint relation's actual signed lift and complete tuple at this cut",
                ));
            }
            packets.push(OrientedPacket {
                source_ring,
                receiver_ring: receiver.ring(),
                positions: family.positions,
                lifts: [lifts[0].clone(), lifts[1].clone()],
                turns: turns.clone(),
                classes: (member.antecedent, member.consequence),
            });
        }
        Ok(SourceReturnCut {
            field: resident.field.clone(),
            source_ring,
            predecessor: resident.continuing_state(source_ring)?,
            crib: crib.clone(),
            pairing: pairing.clone(),
            prior: prior.clone(),
            family: family.clone(),
            packets,
            origin,
            prepared: std::sync::OnceLock::new(),
        })
    }
}

impl SourceReturnCut {
    pub fn family(&self) -> &JointFamily {
        &self.family
    }
    pub fn publish(
        self,
        reference: &Reference,
        resident: &mut Resident,
        crib: &ObservedCrib,
    ) -> Result<ReciprocalOutcome, HnnError> {
        self.publish_checked(reference, resident, crib, |_| Ok(()))
    }
    fn publish_checked(
        self,
        reference: &Reference,
        resident: &mut Resident,
        crib: &ObservedCrib,
        check: impl FnOnce(&Resident) -> Result<(), HnnError>,
    ) -> Result<ReciprocalOutcome, HnnError> {
        let ring = self.source_ring;
        if resident.field != self.field
            || crib != &self.crib
            || !resident.pending.is_empty()
            || !resident.staged.is_empty()
            || resident.arrived.is_some()
            || resident.opens != reference.reception.opens()
            || resident.continuing_state(ring)? != self.predecessor
        {
            return Err(refused(
                "a source return requires its unchanged producing source, material, clock, carry, chart and testimony",
            ));
        }
        let Some(packet) = self.packets.first() else {
            return Ok(ReciprocalOutcome::NoCompatibleBranch);
        };
        if self.packets.iter().any(|p| p != packet) {
            return Ok(ReciprocalOutcome::Hold {
                branches: self.packets.len(),
            });
        }
        let (next, receipt, _) = self.prepare_native(resident, crib)?;
        check(&next)?;
        *resident = next;
        Ok(ReciprocalOutcome::Published(receipt))
    }
    /// Engineering reuse at ONE unchanged immutable cut. No native state, observation, teacher or
    /// predicted class is published. A changed source/material/family/clock/carry/crib invalidates
    /// this token before cache lookup. This is memoization, not learned compression.
    pub fn prepare_reading(
        &self,
        resident: &Resident,
        crib: &ObservedCrib,
    ) -> Result<(ContinuingState, bool), HnnError> {
        let (next, _, reused) = self.prepare_native(resident, crib)?;
        Ok((next.continuing_state(self.source_ring)?, reused))
    }
    fn prepare_native(
        &self,
        resident: &Resident,
        crib: &ObservedCrib,
    ) -> Result<(Resident, ReciprocalReceipt, bool), HnnError> {
        let ring = self.source_ring;
        if resident.field != self.field
            || crib != &self.crib
            || resident.arrived.is_some()
            || !resident.pending.is_empty()
            || !resident.staged.is_empty()
            || resident.continuing_state(ring)? != self.predecessor
        {
            return Err(refused(
                "an immutable prepared source return invalidates on changed producing context",
            ));
        }
        let packet = self
            .packets
            .first()
            .ok_or_else(|| refused("no compatible packet to prepare"))?;
        if self.packets.iter().any(|p| p != packet) {
            return Err(refused(
                "plural distinct packets are held, never prepared by a centre",
            ));
        }
        if let Some((next, receipt)) = self.prepared.get() {
            return Ok((next.clone(), receipt.clone(), true));
        }
        let carrier = PairedCarrier::admit(
            &self.field,
            ring,
            &self.pairing,
            resident
                .constitution
                .source_port(ring)
                .ok_or(HnnError::MissingSourcePort { ring })?,
        )?;
        // Exactly ONE paired batch; the helper adds the signed reverse, not a second observation.
        let (constitution, deposit) = carrier.deposit_oriented_pair(
            &self.field,
            &resident.constitution,
            &self.prior,
            packet.turns.clone(),
            packet.classes,
        )?;
        let mut next = resident.clone();
        next.constitution = constitution;
        let newest = self.family.separating_return.as_ref().map_or_else(
            || self.family.positions[0].max(self.family.positions[1]),
            |(p, _, _)| *p,
        );
        next.source_return_frontier.insert(ring, newest);
        PairedObservation::admit(&self.field, &next.constitution, &self.pairing)?;
        next.constitution.admit_epoch_field(&self.field)?;
        let source = std::sync::Arc::new(
            next.moments
                .values()
                .next()
                .ok_or_else(|| refused("the actual producing moment"))?
                .clone(),
        );
        let (_, opening) = Word::open_source_exact_received(
            &self.field,
            &next.constitution,
            &next.current,
            source,
            &next.reception_opening(),
        )?;
        if !opening.closes() {
            return Err(refused(
                "the successor source entrance's exact opening work",
            ));
        }
        // Existing passage codec validates contemporary admission while retaining every live
        // state operand. No mount/reset, target reread, tree update or terminal flush occurs.
        let _ = next.continuing_state(ring)?;
        let receipt = ReciprocalReceipt {
            packet: packet.clone(),
            origin: self.origin.clone(),
            compatible_branches: self.family.members.len(),
            slip_before: deposit.slip_before,
            slip_after: deposit.slip_after,
            source_step: deposit.source,
            paired_batches: 1,
            normal_preparations: 2,
            validation_word_openings: 1,
        };

        let _ = self.prepared.set((next.clone(), receipt.clone()));
        Ok((next, receipt, false))
    }
}

mod checkpoint;
pub use checkpoint::ReciprocalCheckpoint;

#[cfg(test)]
mod tests;
