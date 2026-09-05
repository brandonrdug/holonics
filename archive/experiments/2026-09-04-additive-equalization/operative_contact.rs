//! WITHDRAWN EXPERIMENT: addition does not supply a desired comparison target.
//! Owned additive-junction contacts in the existing complete native session.
//!
//! A binding is derived from an actual Contract -> unary reaction word -> Add incidence. The other Add input is the
//! arriving current; the Contract owns the presented section and the population receiving the
//! factorized return. Both directions are admitted when both arrivals are contractions. There is
//! no caller-supplied target population, observation-ID join, label, or expected-answer router.
//! The return crosses the actual intermediate reactions in reverse order; normalization is not
//! dropped to pretend that a composed nonlinear branch is a direct linear contraction.
//! This is one declared local constitutive chart, not an assertion that every junction should
//! adapt this way or that every nonlinear reaction has identity admittance.

use serde::Serialize;
use std::collections::BTreeMap;
use std::rc::Rc;

use super::{
    full_operation::{carrier_of, ContemporaryCarrier},
    operative_backward::{NativeAdjointReturnTrace, ReturnDeed},
    operative_return::{
        additive_junction_difference, deposit_from_material, enact_additive_junction_contact,
        scale_contact_differential, DepositMaterial, OverlayAtom,
    },
    NativeCarrierOrdinal, NativeFullCycle, NativeFullOperationError, NativeFullOperatorEcology,
    NativeFullOperatorSession, NativeMorphologyDeposit, NativeOperationPrimitive,
    NativeOperatorNode, NativeOperatorResidence, NativeReturnAperture, NativeTensorOrdinal,
};

/// Descriptive chart of an actual graph contact; runtime construction is private and derived.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeJunctionContact {
    pub joining_operation: u32,
    pub transport_operation: u32,
    /// Actual unary reaction word, from the junction backwards to the contraction.
    pub reaction_path: Vec<u32>,
    pub presented: NativeCarrierOrdinal,
    pub transported: NativeCarrierOrdinal,
    pub arrived: NativeCarrierOrdinal,
    pub population: NativeTensorOrdinal,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeJunctionReturn {
    pub contact: NativeJunctionContact,
    /// The actual session occurrence generation, not an input-supplied identity.
    pub occurrence: u64,
    /// The declared readout factor placed before the local adjoint; the deposit carries the
    /// remaining factor. Their sum is the requested shift, never a second learning rate.
    pub receiver_scale_shift: u32,
    pub receiver_scale_width_grains: u64,
    /// None means exact zero current; chronology still advances through the joined occurrence.
    pub deposit: Option<NativeMorphologyDeposit>,
}

pub(super) struct JunctionCultivation<'chart> {
    /// Runtime ownership capability only, not a semantic identity or serialized model address.
    origin: Rc<()>,
    pub aperture: NativeReturnAperture,
    bindings: BTreeMap<u32, Vec<NativeJunctionContact>>,
    last_source_use: BTreeMap<NativeCarrierOrdinal, u32>,
    pending: BTreeMap<NativeTensorOrdinal, Vec<OverlayAtom<'chart>>>,
    returns: Vec<NativeJunctionReturn>,
}

/// Recoverable ownership of the actual factors removed for an attribution receiver.
/// This is neither a cloned ecology nor a reconstructed predecessor.
pub struct NativeJunctionWithdrawal<'chart> {
    origin: Rc<()>,
    atoms: BTreeMap<NativeTensorOrdinal, Vec<OverlayAtom<'chart>>>,
}

impl NativeJunctionWithdrawal<'_> {
    pub fn factor_rank(&self) -> usize {
        self.atoms.values().flatten().map(OverlayAtom::rank).sum()
    }
}

fn bindings_of(operations: &[NativeOperatorNode]) -> BTreeMap<u32, Vec<NativeJunctionContact>> {
    let producers: BTreeMap<_, _> = operations.iter().map(|node| (node.output, node)).collect();
    let mut bindings = BTreeMap::new();
    for joining in operations {
        if !matches!(joining.primitive, NativeOperationPrimitive::Add) || joining.inputs.len() != 2
        {
            continue;
        }
        let mut contacts = Vec::new();
        for direction in 0..2 {
            let transported = joining.inputs[direction];
            let arrived = joining.inputs[1 - direction];
            let Some(mut transport) = producers.get(&transported).copied() else {
                continue;
            };
            let mut reaction_path = Vec::new();
            while transport.inputs.len() == 1
                && matches!(
                    transport.primitive,
                    NativeOperationPrimitive::RmsRebase { .. }
                        | NativeOperationPrimitive::Reshape
                        | NativeOperationPrimitive::Scale { .. }
                        | NativeOperationPrimitive::GeluTanh
                        | NativeOperationPrimitive::Tanh
                        | NativeOperationPrimitive::Select { .. }
                )
            {
                let Some(previous) = producers.get(&transport.inputs[0]).copied() else {
                    break;
                };
                if previous.ordinal >= transport.ordinal {
                    break;
                }
                reaction_path.push(transport.ordinal);
                transport = previous;
            }
            // Every role follows the actual operator graph. Equal widths or co-presence are
            // deliberately insufficient to supply a missing transport or second arrival.
            if !matches!(transport.primitive, NativeOperationPrimitive::Contract)
                || transport.inputs.len() != 1
                || transport.coefficients.len() != 1
                || transport.ordinal >= joining.ordinal
                || transported == arrived
                || !producers
                    .get(&arrived)
                    .is_some_and(|node| node.ordinal < joining.ordinal)
            {
                continue;
            }
            contacts.push(NativeJunctionContact {
                joining_operation: joining.ordinal,
                transport_operation: transport.ordinal,
                reaction_path,
                presented: transport.inputs[0],
                transported,
                arrived,
                population: transport.coefficients[0],
            });
        }
        if !contacts.is_empty() {
            bindings.insert(joining.ordinal, contacts);
        }
    }
    bindings
}

impl NativeFullOperatorEcology {
    /// Preflight the model's own contact graph before loading its coefficient payload.
    pub fn junction_contacts(
        &self,
    ) -> Result<Vec<NativeJunctionContact>, NativeFullOperationError> {
        self.validate()?;
        Ok(bindings_of(&self.operations)
            .into_values()
            .flatten()
            .collect())
    }
}

impl<'chart> JunctionCultivation<'chart> {
    fn found(ecology: &NativeFullOperatorEcology, aperture: NativeReturnAperture) -> Self {
        let bindings = bindings_of(&ecology.operations);
        let mut last_source_use: BTreeMap<NativeCarrierOrdinal, u32> = BTreeMap::new();
        for contact in bindings.values().flatten() {
            let mut needed = vec![contact.presented, contact.transported, contact.arrived];
            for at in &contact.reaction_path {
                let reaction = &ecology.operations[*at as usize];
                needed.push(reaction.output);
                needed.extend_from_slice(&reaction.inputs);
            }
            for carrier in needed {
                last_source_use
                    .entry(carrier)
                    .and_modify(|last| *last = (*last).max(contact.joining_operation))
                    .or_insert(contact.joining_operation);
            }
        }
        Self {
            origin: Rc::new(()),
            aperture,
            bindings,
            last_source_use,
            pending: BTreeMap::new(),
            returns: Vec::new(),
        }
    }

    pub(super) fn retains_source_after(
        &self,
        carrier: NativeCarrierOrdinal,
        operation: u32,
    ) -> bool {
        self.last_source_use
            .get(&carrier)
            .is_some_and(|last| *last > operation)
    }

    pub(super) fn released_sources_at(&self, operation: u32) -> Vec<NativeCarrierOrdinal> {
        self.last_source_use
            .iter()
            .filter_map(|(carrier, last)| (*last == operation).then_some(*carrier))
            .collect()
    }
}

impl<'residence, 'chart> NativeFullOperatorSession<'residence, 'chart> {
    /// Found the declared additive-junction developmental chart. It uses the same cycle owner
    /// as the prefix chart, but does not install the prefix's different comparison rule as well.
    pub fn found_with_junction_return(
        ecology: &'residence NativeFullOperatorEcology,
        residence: &'residence mut NativeOperatorResidence<'chart>,
        aperture: NativeReturnAperture,
    ) -> Result<Self, NativeFullOperationError> {
        ecology.validate()?;
        let cultivation = JunctionCultivation::found(ecology, aperture);
        if cultivation.bindings.is_empty() {
            return Err(NativeFullOperationError::Contact(
                "the body has no admitted additive contact",
            ));
        }
        let mut session = Self::found(ecology, residence)?;
        session.junction_cultivation = Some(cultivation);
        Ok(session)
    }

    pub fn junction_contact_population(&self) -> usize {
        self.junction_cultivation
            .as_ref()
            .map_or(0, |c| c.bindings.values().map(Vec::len).sum())
    }

    /// An explicit fixed-morphology attribution receiver, not the default inference lifecycle.
    /// The same owned cycle executes and chronology advances; no factor or ecology is cloned.
    pub fn observe_junction_cycle(
        mut self,
        rows: &[u32],
    ) -> Result<NativeFullCycle<'residence, 'chart>, NativeFullOperationError> {
        if !self.cycle_complete && self.operation_at != 0 {
            return Err(NativeFullOperationError::Contact(
                "an observation requires an operation boundary",
            ));
        }
        let chart = self
            .junction_cultivation
            .take()
            .ok_or(NativeFullOperationError::Contact(
                "this session has no junction chart",
            ))?;
        if !chart.pending.is_empty() || !chart.returns.is_empty() {
            return Err(NativeFullOperationError::Contact(
                "an unclosed local return is not an observation boundary",
            ));
        }
        let mut cycle = self.advance_cycle(rows)?;
        cycle.successor.junction_cultivation = Some(chart);
        Ok(cycle)
    }

    /// Withdraw the complete local delta for a declared attribution experiment. A later normal
    /// operation may learn again; restoration refuses if new factors now occupy this difference.
    pub fn withdraw_junction_changes(
        &mut self,
    ) -> Result<NativeJunctionWithdrawal<'chart>, NativeFullOperationError> {
        let chart = self
            .junction_cultivation
            .as_ref()
            .ok_or(NativeFullOperationError::Contact(
                "this session has no junction chart",
            ))?;
        if !self.cycle_complete || !chart.pending.is_empty() || !chart.returns.is_empty() {
            return Err(NativeFullOperationError::Contact(
                "withdrawal requires a completed operation",
            ));
        }
        Ok(NativeJunctionWithdrawal {
            origin: Rc::clone(&chart.origin),
            atoms: std::mem::take(&mut self.overlay),
        })
    }

    /// On refusal the caller retains the actual withdrawn factors, so recovery is not deletion.
    pub fn restore_junction_changes(
        &mut self,
        withdrawal: NativeJunctionWithdrawal<'chart>,
    ) -> Result<(), (NativeFullOperationError, NativeJunctionWithdrawal<'chart>)> {
        let compatible = self.junction_cultivation.as_ref().is_some_and(|chart| {
            Rc::ptr_eq(&chart.origin, &withdrawal.origin)
                && chart.pending.is_empty()
                && chart.returns.is_empty()
        });
        if !self.cycle_complete || !compatible || !self.overlay.is_empty() {
            return Err((
                NativeFullOperationError::Contact(
                    "the withdrawal does not rejoin this unmodified native base",
                ),
                withdrawal,
            ));
        }
        self.overlay = withdrawal.atoms;
        Ok(())
    }

    pub(super) fn return_at_junction(
        &mut self,
        operation: u32,
    ) -> Result<(), NativeFullOperationError> {
        let Some(cultivation) = self.junction_cultivation.as_ref() else {
            return Ok(());
        };
        let Some(bindings) = cultivation.bindings.get(&operation).cloned() else {
            return Ok(());
        };
        let aperture = cultivation.aperture;
        for contact in bindings {
            let mut receiver_scale_width_grains = 0;
            let receiver_scale_shift = if contact.reaction_path.is_empty() {
                0
            } else {
                aperture.learning_shift
            };
            // These borrows can only resolve sections owned by this cycle/checkpoint population.
            // No public API accepts a manufactured SectionContactMaterial or an ordinal-only join.
            let source = carrier_of(&self.carriers, &self.checkpoints, &contact.presented).ok_or(
                NativeFullOperationError::Contact("the presented carrier was not retained"),
            )?;
            let transported = carrier_of(&self.carriers, &self.checkpoints, &contact.transported)
                .ok_or(NativeFullOperationError::Carrier)?;
            let arrived = carrier_of(&self.carriers, &self.checkpoints, &contact.arrived)
                .ok_or(NativeFullOperationError::Carrier)?;
            let returned = if contact.reaction_path.is_empty() {
                enact_additive_junction_contact(
                    self.residence.surface(),
                    &source.section,
                    source.bound_octaves,
                    &transported.section,
                    transported.bound_octaves,
                    &arrived.section,
                    arrived.bound_octaves,
                    aperture,
                )?
            } else {
                let differential = additive_junction_difference(
                    self.residence.surface(),
                    &transported.section,
                    transported.bound_octaves,
                    &arrived.section,
                    arrived.bound_octaves,
                )?;
                match differential {
                    None => None,
                    Some(differential) => {
                        let (differential, width) = scale_contact_differential(
                            self.residence.surface(),
                            differential,
                            receiver_scale_shift,
                        )?;
                        receiver_scale_width_grains = width;
                        let mut adjoint = BTreeMap::from([(
                            contact.transported,
                            ContemporaryCarrier {
                                section: differential.section,
                                bound_octaves: differential.octaves,
                            },
                        )]);
                        let mut trace = NativeAdjointReturnTrace {
                            held_overlay_rank: self.morphology_overlay_rank(),
                            operations_returned: 0,
                            layers_replayed: 0,
                            deposits: Vec::new(),
                            populations_deposited: Vec::new(),
                            supports: Vec::new(),
                            lookups_reached: Vec::new(),
                            elapsed_milliseconds: 0,
                        };
                        let mut unexpected = BTreeMap::new();
                        for at in &contact.reaction_path {
                            let reaction = self.ecology.operations[*at as usize].clone();
                            let dy = adjoint
                                .remove(&reaction.output)
                                .ok_or(NativeFullOperationError::Carrier)?;
                            self.return_through(
                                &reaction,
                                dy,
                                &mut adjoint,
                                &ReturnDeed::Cultivate(aperture),
                                &mut trace,
                                &mut unexpected,
                            )?;
                        }
                        let endpoint =
                            self.ecology.operations[contact.transport_operation as usize].output;
                        let dy = adjoint
                            .remove(&endpoint)
                            .ok_or(NativeFullOperationError::Carrier)?;
                        if !adjoint.is_empty() || !unexpected.is_empty() {
                            return Err(NativeFullOperationError::Contact(
                                "the declared unary return escaped its local word",
                            ));
                        }
                        let source =
                            carrier_of(&self.carriers, &self.checkpoints, &contact.presented)
                                .ok_or(NativeFullOperationError::Carrier)?;
                        Some(deposit_from_material(
                            self.residence.surface(),
                            DepositMaterial {
                                differential: &dy.section,
                                differential_octaves: dy.bound_octaves,
                                presented: &source.section,
                                presented_octaves: source.bound_octaves,
                                grain: source.section.grain(),
                            },
                            NativeReturnAperture {
                                learning_shift: 0,
                                ..aperture
                            },
                        )?)
                    }
                }
            };
            let cultivation = self
                .junction_cultivation
                .as_mut()
                .expect("same owned chart");
            let deposit = returned.map(|(atom, mut deposit)| {
                deposit.population = contact.population.0;
                cultivation
                    .pending
                    .entry(contact.population)
                    .or_default()
                    .push(atom);
                deposit
            });
            cultivation.returns.push(NativeJunctionReturn {
                contact,
                occurrence: self.generation,
                receiver_scale_shift,
                receiver_scale_width_grains,
                deposit,
            });
        }
        Ok(())
    }

    pub(super) fn publish_junction_returns(&mut self) -> Vec<NativeJunctionReturn> {
        let Some(cultivation) = self.junction_cultivation.as_mut() else {
            return Vec::new();
        };
        for (population, atoms) in std::mem::take(&mut cultivation.pending) {
            self.overlay.entry(population).or_default().extend(atoms);
        }
        std::mem::take(&mut cultivation.returns)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn node(
        at: u32,
        primitive: NativeOperationPrimitive,
        inputs: &[u32],
        coefficients: &[u32],
    ) -> NativeOperatorNode {
        NativeOperatorNode {
            ordinal: at,
            layer: None,
            primitive,
            inputs: inputs.iter().copied().map(NativeCarrierOrdinal).collect(),
            output: NativeCarrierOrdinal(at),
            coefficients: coefficients
                .iter()
                .copied()
                .map(NativeTensorOrdinal)
                .collect(),
        }
    }

    #[test]
    fn contact_roles_follow_both_actual_contraction_arrivals_and_not_co_presence() {
        let mut operations = vec![
            node(0, NativeOperationPrimitive::Emit, &[], &[]),
            node(1, NativeOperationPrimitive::Contract, &[0], &[7]),
            node(2, NativeOperationPrimitive::Contract, &[0], &[9]),
            node(3, NativeOperationPrimitive::Add, &[1, 2], &[]),
        ];
        let contacts = bindings_of(&operations);
        assert_eq!(contacts[&3].len(), 2);
        assert_eq!(contacts[&3][0].population, NativeTensorOrdinal(7));
        assert_eq!(contacts[&3][1].population, NativeTensorOrdinal(9));
        assert_eq!(contacts[&3][0].presented, NativeCarrierOrdinal(0));
        operations[3].inputs = vec![NativeCarrierOrdinal(1), NativeCarrierOrdinal(1)];
        assert!(
            bindings_of(&operations).is_empty(),
            "one arrival copied twice is not a paired contact"
        );
        operations[3].inputs = vec![NativeCarrierOrdinal(1), NativeCarrierOrdinal(20)];
        assert!(
            bindings_of(&operations).is_empty(),
            "an unproduced ordinal is not an arrival"
        );
    }

    #[test]
    fn contact_roles_retain_the_actual_unary_reaction_word_instead_of_skipping_its_adjoint() {
        let operations = vec![
            node(0, NativeOperationPrimitive::Emit, &[], &[]),
            node(1, NativeOperationPrimitive::Contract, &[0], &[7]),
            node(2, NativeOperationPrimitive::Tanh, &[1], &[]),
            node(3, NativeOperationPrimitive::Reshape, &[2], &[]),
            node(4, NativeOperationPrimitive::Add, &[0, 3], &[]),
        ];
        let contacts = bindings_of(&operations);
        assert_eq!(contacts[&4].len(), 1);
        assert_eq!(contacts[&4][0].reaction_path, vec![3, 2]);
        assert_eq!(contacts[&4][0].transport_operation, 1);
        assert_eq!(contacts[&4][0].transported, NativeCarrierOrdinal(3));
        assert_eq!(contacts[&4][0].population, NativeTensorOrdinal(7));
    }
}
