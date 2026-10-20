//! Absolute receiver-ingress target for the existing opt-in observed channel-D scope.
//!
//! [agent-inferred; 2026-10-20] L_target(a,N)=L_founding(a)+k(N). The old
//! from-zero incremental schedule telescopes to this absolute target. A delayed opt-in
//! retains the physical receiver clock; no activation-history field or source-cell clock
//! is introduced. This owner selects representation only; publication still belongs to the
//! actual full endpoint and the same-opening finite comparison. Lean join obligation: #62.

use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ObservedChannelGrainPlan {
    pub(crate) receiver: usize,
    pub(crate) ingress_before: u64,
    pub(crate) ingress_after: u64,
    grain_exponent: u32,
    founding: BTreeMap<usize, Lattice>,
    pub(crate) targets: BTreeMap<usize, Lattice>,
}

impl ObservedChannelGrainPlan {
    pub(crate) fn at_section(
        field: &Field, retained: &BTreeSet<Locus>, receiver: usize,
        ingress_before: u64, ingress_after: u64,
    ) -> Result<Option<Self>, HnnError> {
        if !field.receivers().iter().any(|declared| declared.ring == receiver)
            || ingress_after < ingress_before {
            return Err(refused("a channel grain target needs its declared receiver and monotone actual ingress"));
        }
        // A terminal source fragment that did not cross the receiver cannot schedule a level.
        if ingress_after == ingress_before { return Ok(None); }
        let grain_exponent = crate::hnn::reference::refining_grain_exponent(ingress_after)?;
        let mut founding = BTreeMap::new();
        let mut targets = BTreeMap::new();
        for locus in retained {
            let Locus::Channel(contact) = *locus else { continue; };
            let base = field.lattice(*locus).ok_or(HnnError::Lattice { locus: *locus })?;
            let target = base.exponent().checked_add(grain_exponent).ok_or_else(extent)?;
            founding.insert(contact, base);
            targets.insert(contact, Lattice::new(target));
        }
        Ok(Some(Self { receiver, ingress_before, ingress_after, grain_exponent, founding, targets }))
    }

    pub(super) fn reading(
        &self, opening: &Constitution, candidate: &Constitution,
        rebases: &BTreeMap<usize, channel_grain::ChannelGrainRebase>,
        eligible: &BTreeSet<usize>,
    ) -> Result<EpochChannelGrainReading, HnnError> {
        let mut contacts = Vec::new();
        for (&contact, target) in &self.targets {
            let locus = Locus::Channel(contact);
            let before = opening.lattice(locus)?.exponent();
            let after = candidate.lattice(locus)?.exponent();
            let delta = match rebases.get(&contact) {
                Some(rebase) => rebase.factor_delta[2].clone(),
                None => {
                    let matrix = &opening.contacts.get(contact).ok_or(HnnError::Lattice { locus })?.dissipation;
                    ExactRatMatrix::zero(matrix.rows(), matrix.columns())?
                }
            };
            contacts.push(EpochChannelGrainContactReading {
                contact, founding_exponent: self.founding[&contact].exponent(),
                target_exponent: target.exponent(), before_exponent: before, after_exponent: after,
                levels: after.checked_sub(before).ok_or_else(extent)?,
                shortfall: target.exponent().saturating_sub(after),
                limiting_held_factor: rebases.get(&contact).and_then(|r| r.limiting.clone()),
                deferred_without_fresh_update: !eligible.contains(&contact),
                scale_rebase: std::array::from_fn(|family| &candidate.contacts[contact].scales[family] - &opening.contacts[contact].scales[family]),
                dissipation_rebase: EpochSeriesReading::of(&EpochArray::from_dyadic_matrix(&delta)?),
                dissipation_scale_rebase: &candidate.contacts[contact].scales[2] - &opening.contacts[contact].scales[2],
            });
        }
        Ok(EpochChannelGrainReading { receiver: self.receiver, ingress_before: self.ingress_before,
            ingress_after: self.ingress_after, grain_exponent: self.grain_exponent, contacts })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn receiver_clock_grain_targets_founding_lattice_without_activation_history() {
        let field = Field::declare(crate::hnn::tests::learning::chain_declaration(1 << 16).by_lattice_rule()).unwrap();
        let receiver = field.receivers()[0].ring;
        let retained = crate::hnn::retention::loci(&field).into_iter().collect();
        let plan = ObservedChannelGrainPlan::at_section(&field, &retained, receiver, 113, 114).unwrap().unwrap();
        assert_eq!(plan.grain_exponent, 3);
        assert!(!plan.targets.is_empty());
        for (&contact, target) in &plan.targets {
            assert_eq!(target.exponent(), field.lattice(Locus::Channel(contact)).unwrap().exponent() + 3);
        }
        assert!(ObservedChannelGrainPlan::at_section(&field, &retained, receiver, 114, 114).unwrap().is_none());
        assert!(ObservedChannelGrainPlan::at_section(&field, &retained, receiver, 114, 113).is_err());
        assert!(ObservedChannelGrainPlan::at_section(&field, &retained, usize::MAX, 113, 114).is_err());
    }
}
