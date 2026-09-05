//! Joined-passage return over actual native contraction/reaction/junction incidences.
//!
//! HNP1 uses the joining operation's OUTPUT as the target section: (t + p) - t = p.
//! The archived Add-equalization experiment used p - t and was withdrawn; this binding does not
//! treat a partner as a desired target. The actual output and before/after occurrence are owned
//! by this session. Local adjoints use the retained morphology, and deltas publish at cycle close.
//! Formal owner: HolonicOrientedSiteTransport.ConstitutiveSectionReturn.additive_joined_passage_effect.
//! See research/records/2026-09-04_HNP1_ADDITIVE_EQUALIZATION_CHANGED_CONDUCT_BUT_DID_NOT_FOUND_A_LEARNING_COMPARISON.md.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::rc::Rc;

use super::{
    full_operation::{carrier_of, ContemporaryCarrier},
    operative_backward::{NativeAdjointReturnTrace, ReturnDeed},
    operative_return::{
        deposit_from_material, enact_identity_admittance_contact, native_section_difference,
        scale_contact_differential, DepositMaterial, OverlayAtom,
    },
    NativeCarrierOrdinal, NativeFullCycle, NativeFullOperationError, NativeFullOperatorEcology,
    NativeFullOperatorSession, NativeMorphologyDeposit, NativeOperationPrimitive,
    NativeOperatorNode, NativeOperatorResidence, NativeReturnAperture, NativeTensorOrdinal,
};

/// Descriptive chart of an actual graph contact; runtime construction is private and derived.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeJoinedPassage {
    pub joining_operation: u32,
    pub transport_operation: u32,
    /// Actual unary reaction word, from the junction backwards to the contraction.
    pub reaction_path: Vec<u32>,
    pub presented: NativeCarrierOrdinal,
    pub transported: NativeCarrierOrdinal,
    /// The other arriving leg is retained as lineage, never treated as a desired target.
    pub partner: NativeCarrierOrdinal,
    /// The actual result of the joining operation, after the interaction.
    pub arrived: NativeCarrierOrdinal,
    pub population: NativeTensorOrdinal,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativePassageReturn {
    pub contact: NativeJoinedPassage,
    /// The actual session occurrence generation, not an input-supplied identity.
    pub occurrence: u64,
    /// The declared readout factor placed before the local adjoint; the deposit carries the
    /// remaining factor. Their sum is the requested shift, never a second learning rate.
    pub receiver_scale_shift: u32,
    pub receiver_scale_width_grains: Option<u64>,
    /// None means exact zero current; chronology still advances through the joined occurrence.
    pub deposit: Option<NativeMorphologyDeposit>,
}

pub(super) struct PassageCultivation<'chart> {
    /// Runtime ownership capability only, not a semantic identity or serialized model address.
    origin: Rc<()>,
    pub aperture: NativeReturnAperture,
    bindings: BTreeMap<u32, Vec<NativeJoinedPassage>>,
    last_source_use: BTreeMap<NativeCarrierOrdinal, u32>,
    pending: BTreeMap<NativeTensorOrdinal, Vec<OverlayAtom<'chart>>>,
    returns: Vec<NativePassageReturn>,
}

/// Recoverable ownership of the actual factors removed for an attribution receiver.
/// This is neither a cloned ecology nor a reconstructed predecessor.
pub struct NativePassageWithdrawal<'chart> {
    origin: Rc<()>,
    atoms: BTreeMap<NativeTensorOrdinal, Vec<OverlayAtom<'chart>>>,
}

impl NativePassageWithdrawal<'_> {
    pub fn factor_rank(&self) -> usize {
        self.atoms.values().flatten().map(OverlayAtom::rank).sum()
    }
}

fn bindings_of(operations: &[NativeOperatorNode]) -> BTreeMap<u32, Vec<NativeJoinedPassage>> {
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
            let partner = joining.inputs[1 - direction];
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
                || transported == partner
                || !producers
                    .get(&partner)
                    .is_some_and(|node| node.ordinal < joining.ordinal)
            {
                continue;
            }
            contacts.push(NativeJoinedPassage {
                joining_operation: joining.ordinal,
                transport_operation: transport.ordinal,
                reaction_path,
                presented: transport.inputs[0],
                transported,
                partner,
                arrived: joining.output,
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
    pub fn joined_passages(&self) -> Result<Vec<NativeJoinedPassage>, NativeFullOperationError> {
        self.validate()?;
        Ok(bindings_of(&self.operations)
            .into_values()
            .flatten()
            .collect())
    }
}

impl<'chart> PassageCultivation<'chart> {
    pub(super) fn check_rest_ownership(&self) -> Result<(), super::NativeSessionRestError> {
        if Rc::strong_count(&self.origin) != 1 {
            return Err(super::NativeSessionRestError::Unsupported("an external withdrawal still owns part of this passage lineage"));
        }
        Ok(())
    }

    pub(super) fn detach_rest(&self, surface: &crate::resident_section::ResidentSurface<'chart>)
        -> Result<super::NativePassageRest, super::NativeSessionRestError> {
        self.check_rest_ownership()?;
        Ok(super::NativePassageRest { aperture: self.aperture,
            pending: super::operative_rest::detach_overlays(surface, &self.pending)?, returns: self.returns.clone() })
    }

    pub(super) fn remount_rest(ecology: &NativeFullOperatorEcology,
        surface: &'chart crate::resident_section::ResidentSurface<'chart>, rest: &super::NativePassageRest,
    ) -> Result<Self, super::NativeSessionRestError> {
        let mut passage = Self::found(ecology, rest.aperture);
        for returned in &rest.returns {
            if !passage.bindings.get(&returned.contact.joining_operation)
                .is_some_and(|contacts| contacts.contains(&returned.contact)) {
                return Err(super::NativeSessionRestError::Malformed("pending return does not join the actual graph".into()));
            }
        }
        passage.pending = super::operative_rest::mount_overlays(surface, &rest.pending)?;
        passage.returns = rest.returns.clone();
        Ok(passage)
    }

    fn found(ecology: &NativeFullOperatorEcology, aperture: NativeReturnAperture) -> Self {
        let bindings = bindings_of(&ecology.operations);
        let mut last_source_use: BTreeMap<NativeCarrierOrdinal, u32> = BTreeMap::new();
        for contact in bindings.values().flatten() {
            let mut needed = vec![
                contact.presented,
                contact.transported,
                contact.partner,
                contact.arrived,
            ];
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
    /// Found the declared observed joined-passage developmental chart. It uses the same cycle owner
    /// as the prefix chart, but does not install the prefix's different comparison rule as well.
    pub fn found_with_passage_return(
        ecology: &'residence NativeFullOperatorEcology,
        residence: &'residence mut NativeOperatorResidence<'chart>,
        aperture: NativeReturnAperture,
    ) -> Result<Self, NativeFullOperationError> {
        ecology.validate()?;
        let cultivation = PassageCultivation::found(ecology, aperture);
        if cultivation.bindings.is_empty() {
            return Err(NativeFullOperationError::Contact(
                "the body has no admitted additive contact",
            ));
        }
        let mut session = Self::found(ecology, residence)?;
        session.passage_cultivation = Some(cultivation);
        session.forward_reuse = Some(super::operative_reuse::NativeForwardReuse::found(ecology));
        Ok(session)
    }

    pub fn joined_passage_population(&self) -> usize {
        self.passage_cultivation
            .as_ref()
            .map_or(0, |c| c.bindings.values().map(Vec::len).sum())
    }

    /// An explicit fixed-morphology attribution receiver, not the default inference lifecycle.
    /// The same owned cycle executes and chronology advances; no factor or ecology is cloned.
    pub fn observe_passage_cycle(
        mut self,
        rows: &[u32],
    ) -> Result<NativeFullCycle<'residence, 'chart>, NativeFullOperationError> {
        if !self.cycle_complete && self.operation_at != 0 {
            return Err(NativeFullOperationError::Contact(
                "an observation requires an operation boundary",
            ));
        }
        let chart = self
            .passage_cultivation
            .take()
            .ok_or(NativeFullOperationError::Contact(
                "this session has no joined-passage chart",
            ))?;
        if !chart.pending.is_empty() || !chart.returns.is_empty() {
            return Err(NativeFullOperationError::Contact(
                "an unclosed local return is not an observation boundary",
            ));
        }
        let mut cycle = self.advance_cycle(rows)?;
        cycle.successor.passage_cultivation = Some(chart);
        Ok(cycle)
    }

    /// Withdraw the complete local delta for a declared attribution experiment. A later normal
    /// operation may learn again; restoration refuses if new factors now occupy this difference.
    pub fn withdraw_passage_changes(
        &mut self,
    ) -> Result<NativePassageWithdrawal<'chart>, NativeFullOperationError> {
        let chart = self
            .passage_cultivation
            .as_ref()
            .ok_or(NativeFullOperationError::Contact(
                "this session has no joined-passage chart",
            ))?;
        if !self.cycle_complete || !chart.pending.is_empty() || !chart.returns.is_empty() {
            return Err(NativeFullOperationError::Contact(
                "withdrawal requires a completed operation",
            ));
        }
        if let Some(reuse) = &mut self.forward_reuse { reuse.morphology_changed(self.overlay.keys().copied()); }
        Ok(NativePassageWithdrawal {
            origin: Rc::clone(&chart.origin),
            atoms: std::mem::take(&mut self.overlay),
        })
    }

    /// On refusal the caller retains the actual withdrawn factors, so recovery is not deletion.
    pub fn restore_passage_changes(
        &mut self,
        withdrawal: NativePassageWithdrawal<'chart>,
    ) -> Result<(), (NativeFullOperationError, NativePassageWithdrawal<'chart>)> {
        let compatible = self.passage_cultivation.as_ref().is_some_and(|chart| {
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
        if let Some(reuse) = &mut self.forward_reuse { reuse.morphology_changed(self.overlay.keys().copied()); }
        Ok(())
    }

    pub(super) fn return_joined_passage(
        &mut self,
        operation: u32,
    ) -> Result<(), NativeFullOperationError> {
        let Some(cultivation) = self.passage_cultivation.as_ref() else {
            return Ok(());
        };
        let Some(bindings) = cultivation.bindings.get(&operation).cloned() else {
            return Ok(());
        };
        let aperture = cultivation.aperture;
        // A joining operation publishes its pending differences only after all its contacts
        // return. On allocation refusal these local atoms drop, permitting an apparatus-only
        // cache eviction and retry without duplicating an earlier contact's deposit.
        let mut pending: BTreeMap<NativeTensorOrdinal, Vec<OverlayAtom<'chart>>> = BTreeMap::new();
        let mut returns = Vec::new();
        for contact in bindings {
            let mut receiver_scale_width_grains = None;
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
                enact_identity_admittance_contact(
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
                let differential = native_section_difference(
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
            let deposit = returned.map(|(atom, mut deposit)| {
                deposit.population = contact.population.0;
                pending.entry(contact.population)
                    .or_default()
                    .push(atom);
                deposit
            });
            returns.push(NativePassageReturn {
                contact,
                occurrence: self.generation,
                receiver_scale_shift,
                receiver_scale_width_grains,
                deposit,
            });
        }
        let cultivation = self.passage_cultivation.as_mut().expect("same owned chart");
        for (population, atoms) in pending { cultivation.pending.entry(population).or_default().extend(atoms); }
        cultivation.returns.extend(returns);
        Ok(())
    }

    pub(super) fn publish_passage_returns(&mut self) -> Vec<NativePassageReturn> {
        let Some(cultivation) = self.passage_cultivation.as_mut() else {
            return Vec::new();
        };
        if let Some(reuse) = &mut self.forward_reuse { reuse.morphology_changed(cultivation.pending.keys().copied()); }
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
        assert_eq!(contacts[&3][0].partner, NativeCarrierOrdinal(2));
        assert_eq!(
            contacts[&3][0].arrived,
            NativeCarrierOrdinal(3),
            "the actual joined output, not the partner, is the target section"
        );
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
        assert_eq!(contacts[&4][0].arrived, NativeCarrierOrdinal(4));
    }

    #[test]
    #[ignore = "requires CUDA; actual joined output and zero-partner discriminator"]
    fn zero_partner_actual_passage_has_no_return_and_equalization_is_distinguished() {
        use crate::{
            embedding_fiber::ResidentReadout,
            resident_section::{ResidentGrain, ResidentSectionRest, ResidentSurface},
        };
        let readout = ResidentReadout::new().expect("CUDA readout");
        let surface = ResidentSurface::on(&readout).expect("resident surface");
        let grain = ResidentGrain(4);
        let mount = |words: &[i64]| {
            surface
                .mount_section_rest(&ResidentSectionRest {
                    rows: 1,
                    width: words.len(),
                    grain,
                    bound_octaves: 8,
                    intervals: words.iter().map(|word| (*word, *word)).collect(),
                })
                .unwrap()
        };
        let source = mount(&[16, 0]);
        let transported = mount(&[48, 80]);
        let partner = mount(&[0, 0]);
        let joined = surface.fresh_section(1, 2, grain).unwrap();
        let shape = surface.shape_re_entry(1, 2, 8, 8).unwrap();
        let mut passage = surface.begin_passage(&[vec![]]).unwrap();
        {
            let lane = passage.open(0, &[]).unwrap();
            surface
                .record_re_entry(&lane, &transported, &partner, &joined)
                .unwrap();
        }
        passage.close(0, &joined, shape.needed).unwrap();
        let reading = passage.finish().unwrap().launch().unwrap();
        assert!(reading.obstruction.is_empty());
        let before = surface.census();
        let aperture = NativeReturnAperture {
            learning_shift: 0,
            series_terms: 14,
        };
        let effect = enact_identity_admittance_contact(
            &surface,
            &source,
            8,
            &transported,
            8,
            &joined,
            shape.needed,
            aperture,
        )
        .unwrap();
        assert!(
            effect.is_none(),
            "the unchanged native passage deposited nothing"
        );
        let rejected_target = enact_identity_admittance_contact(
            &surface,
            &source,
            8,
            &transported,
            8,
            &partner,
            8,
            aperture,
        )
        .unwrap();
        assert!(
            rejected_target.is_some(),
            "the prior wrong role is a discriminating foil"
        );
        assert_eq!(surface.census().section_read_outs, before.section_read_outs);
    }
}
