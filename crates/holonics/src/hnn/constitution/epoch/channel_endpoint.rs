//! Reflection at the actual producing cut, before final endpoint rays are certified.
//! C/K are one contact pair: their signed held-momentum work is tested together.
use super::*;
use crate::hnn::word::endpoint::ChannelEndpoint;

pub(super) fn reflect(
    opening: &Constitution,
    next: &mut Constitution,
    strokes: &mut BTreeMap<Locus, BudgetedCarry>,
    bound: &ChannelEndpoint,
) -> Result<Vec<EpochChannelEndpointReading>, HnnError> {
    if !bound.admits_predecessor(opening) || next.contacts.len() != opening.contacts.len() {
        return Err(refused(
            "channel reflection keeps the bound producing predecessor",
        ));
    }
    let mut readings = Vec::new();
    for contact in 0..opening.contacts.len() {
        let old = &opening.contacts[contact];
        let attempted = &next.contacts[contact];
        let attempted_factor_delta = [
            attempted.storage.subtract(&old.storage)?,
            attempted.stiffness.subtract(&old.stiffness)?,
        ];
        let changed = attempted.storage != old.storage || attempted.stiffness != old.stiffness;
        let mut reflected = None;
        let attempted_work = match bound.contact(next, contact) {
            Ok(reading) => {
                if reading.work.is_positive() {
                    reflected = Some("positive combined signed C/K work");
                }
                Some(reading.work)
            }
            Err(HnnError::HeldMomentum { contact: at }) if at == contact => {
                reflected = Some("held canonical momentum is outside the candidate storage range");
                None
            }
            Err(error) => return Err(error),
        };
        if changed
            && reflected.is_none()
            && certify_storage_growth(
                &[gram(&old.storage)?, gram(&old.stiffness)?],
                &[gram(&attempted.storage)?, gram(&attempted.stiffness)?],
            )?
            .is_none()
        {
            reflected = Some("candidate C/K storage growth is uncertified");
        }
        let locus = Locus::Channel(contact);
        let mut reflected_entries = Vec::new();
        if reflected.is_some() {
            next.contacts[contact].storage = old.storage.clone();
            next.contacts[contact].stiffness = old.stiffness.clone();
            // Rejected physical motion is not arithmetic remainder. Restore the
            // opening C/K fibres; keep reached scales/statistics and D intact.
            for family in 0..2 {
                let key = (locus, Carrier::Factor(family));
                next.carries.remove(&key);
                if let Some(carry) = opening.carries.get(&key) {
                    next.carries.insert(key, carry.clone());
                }
            }
            if let Some(stroke) = strokes.get_mut(&locus) {
                stroke.staged.retain(|(carrier, entry), (residual, q)| {
                    if matches!(carrier, Carrier::Factor(0 | 1)) {
                        reflected_entries.push((*carrier, *entry, residual.clone(), q.clone()));
                        false
                    } else {
                        true
                    }
                });
                stroke.moved = !stroke.staged.is_empty();
            }
        }
        let applied = bound.contact(next, contact)?;
        if applied.work.is_positive() {
            return Err(refused(
                "a reflected final C/K endpoint has nonpositive signed work",
            ));
        }
        let final_material = &next.contacts[contact];
        readings.push(EpochChannelEndpointReading {
            contact,
            producing_tick: bound.tick(),
            momentum: bound.momentum(contact).to_vec(),
            rate_before: bound.rate(contact).to_vec(),
            rate_after: applied.rate,
            attempted_work,
            applied_work: applied.work,
            reflected,
            attempted_factor_delta,
            applied_factor_delta: [
                final_material.storage.subtract(&old.storage)?,
                final_material.stiffness.subtract(&old.stiffness)?,
            ],
            applied_form_delta: applied.forms,
            reflected_entries,
        });
    }
    Ok(readings)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::word::{EndChange, PowerForm, ReceptionCarry};

    fn diagonal(width: usize, first: Rat) -> ExactRatMatrix {
        let mut entries = vec![Rat::zero(); width * width];
        entries[0] = first;
        ExactRatMatrix::new(entries.chunks(width).map(|row| row.to_vec()).collect()).unwrap()
    }

    fn fixture() -> (Field, Constitution, crate::hnn::Current, ReceptionCarry) {
        let field = crate::hnn::tests::learning::chain();
        let mut material = Constitution::initial(&field, u64::MAX).unwrap();
        let width = field.contact(0).width();
        assert!(width >= 2);
        material.contacts[0].storage = diagonal(width, Rat::one());
        material.contacts[0].stiffness = diagonal(width, Rat::one());
        let current = crate::hnn::Current::at_rest(&field);
        let change = EndChange {
            storage: field
                .rings()
                .iter()
                .map(|r| vec![Rat::zero(); r.width()])
                .collect(),
            arrivals: field
                .contacts()
                .iter()
                .map(|a| {
                    let (g, h) = a.ends();
                    [
                        vec![Rat::zero(); field.ring(g).width()],
                        vec![Rat::zero(); field.ring(h).width()],
                    ]
                })
                .collect(),
            states: field
                .contacts()
                .iter()
                .enumerate()
                .map(|(a, c)| {
                    let mut u = vec![Rat::zero(); c.width()];
                    let mut w = u.clone();
                    if a == 0 {
                        u[0] = rat(1, 2);
                        w[0] = Rat::one();
                        w[1] = rat(-7, 4);
                    }
                    [u, w]
                })
                .collect(),
            resonators: vec![None; field.rings().len()],
            resonator_phases: vec![None; field.rings().len()],
        };
        let momenta = material
            .contacts
            .iter()
            .zip(&change.states)
            .map(|(m, s)| gram(&m.storage).unwrap().apply(&s[1]).unwrap())
            .collect();
        // Read references from the same producing address, not a closing/rest surrogate.
        let conductances = (0..field.contacts().len())
            .map(|a| {
                let e =
                    crate::hnn::propagation::contact_exponent(&field, a, current.lift()).unwrap();
                assert_eq!(e.phase, 0);
                crate::ratio::exponentiated::power_of_two(&e.carry).unwrap()
                    * field.contact(a).admittance()
            })
            .collect();
        let carry = ReceptionCarry {
            change,
            ticks: 17,
            conductances,
            momenta,
            resonator_momenta: vec![None; field.rings().len()],
        };
        (field, material, current, carry)
    }

    #[test]
    fn ck_endpoint_combines_signed_work_and_preserves_kernel_and_real_next_opening() {
        let (field, material, current, carry) = fixture();
        let bound =
            ChannelEndpoint::bind(&field, &material, &current, &carry.change, &carry).unwrap();
        let before = material.continuing_state(0).unwrap().to_text();
        let mut next = material.clone();
        let width = field.contact(0).width();
        next.contacts[0].storage = diagonal(width, rat(2, 1));
        next.contacts[0].stiffness = diagonal(width, rat(3, 2));
        let readings = reflect(&material, &mut next, &mut BTreeMap::new(), &bound).unwrap();
        let r = &readings[0];
        assert_eq!(r.applied_work, rat(-7, 32));
        assert_eq!(r.reflected, None);
        assert_eq!(r.rate_after[0], rat(1, 4));
        assert_eq!(r.rate_after[1], rat(-7, 4));
        assert!(
            r.applied_form_delta
                .iter()
                .any(|m| m.entries().iter().any(|v| !v.is_zero()))
        );
        assert_eq!(r.momentum, carry.momenta[0]);
        assert_eq!(r.producing_tick, 17);
        let actual = PowerForm::read(&field, &next, &current)
            .unwrap()
            .opening(&field, &carry)
            .unwrap();
        assert_eq!(actual.states[0][1], r.rate_after);
        assert_eq!(actual.states[0][0], carry.change.states[0][0]);
        assert_eq!(actual.resonator_phases, carry.change.resonator_phases);
        assert_eq!(material.continuing_state(0).unwrap().to_text(), before);
        let state = next.continuing_state(0).unwrap();
        let cold = material.clone().continued_on(&field, &state).unwrap();
        assert_eq!(cold.continuing_state(0).unwrap().to_text(), state.to_text());
        assert_eq!(
            PowerForm::read(&field, &cold, &current)
                .unwrap()
                .opening(&field, &carry)
                .unwrap(),
            actual
        );
    }

    #[test]
    fn ck_reflection_restores_pair_fibres_and_keeps_attained_scales_and_d() {
        for range_failure in [false, true] {
            let (field, mut material, current, carry) = fixture();
            let locus = Locus::Channel(0);
            material.carries.insert(
                (locus, Carrier::Factor(0)),
                Carry(BTreeMap::from([(0, rat(1, 32))])),
            );
            let bound =
                ChannelEndpoint::bind(&field, &material, &current, &carry.change, &carry).unwrap();
            let before = material.continuing_state(0).unwrap().to_text();
            let mut next = material.clone();
            next.contacts[0].storage = diagonal(
                field.contact(0).width(),
                if range_failure {
                    Rat::zero()
                } else {
                    rat(1, 2)
                },
            );
            next.contacts[0].stiffness = diagonal(field.contact(0).width(), rat(3, 2));
            next.contacts[0].scales[0] = rat(5, 4);
            next.contacts[0].dissipation = diagonal(field.contact(0).width(), rat(3, 4));
            next.carries.insert(
                (locus, Carrier::Factor(0)),
                Carry(BTreeMap::from([(0, rat(-1, 64))])),
            );
            next.carries.insert(
                (locus, Carrier::FactorScale(0)),
                Carry(BTreeMap::from([(0, rat(1, 64))])),
            );
            let mut strokes = BTreeMap::from([(
                locus,
                BudgetedCarry {
                    lattice: material.lattice(locus).unwrap(),
                    clock: 1,
                    moved: true,
                    backtracks: vec![],
                    staged: BTreeMap::from([
                        ((Carrier::Factor(0), 0), (rat(-1, 64), BigInt::from(-1))),
                        ((Carrier::Factor(1), 0), (rat(1, 64), BigInt::from(1))),
                        ((Carrier::FactorScale(0), 0), (rat(1, 64), BigInt::from(0))),
                        ((Carrier::Factor(2), 0), (Rat::zero(), BigInt::from(1))),
                    ]),
                },
            )]);
            let attempted_rays =
                super::super::channel_ray::ChannelFactorDisplacement::read_all(&material, &next)
                    .unwrap();
            assert!(attempted_rays.iter().any(|ray| ray.family < 2));
            let r = reflect(&material, &mut next, &mut strokes, &bound)
                .unwrap()
                .remove(0);
            assert!(r.reflected.is_some());
            assert_eq!(r.attempted_work.is_none(), range_failure);
            assert_eq!(r.applied_work, Rat::zero());
            assert_eq!(r.rate_after, carry.change.states[0][1]);
            assert_eq!(r.reflected_entries.len(), 2);
            let final_rays =
                super::super::channel_ray::ChannelFactorDisplacement::read_all(&material, &next)
                    .unwrap();
            assert!(
                final_rays.iter().all(|ray| ray.family == 2),
                "final rays must be rebuilt after C/K reflection"
            );
            assert_eq!(next.contacts[0].storage, material.contacts[0].storage);
            assert_eq!(next.contacts[0].stiffness, material.contacts[0].stiffness);
            assert_eq!(next.contacts[0].scales[0], rat(5, 4));
            assert_ne!(
                next.contacts[0].dissipation,
                material.contacts[0].dissipation
            );
            assert_eq!(
                next.carries.get(&(locus, Carrier::Factor(0))),
                material.carries.get(&(locus, Carrier::Factor(0)))
            );
            assert_eq!(
                next.carries.get(&(locus, Carrier::Factor(1))),
                material.carries.get(&(locus, Carrier::Factor(1)))
            );
            assert!(next.carries.contains_key(&(locus, Carrier::FactorScale(0))));
            assert_eq!(strokes[&locus].staged.len(), 2);
            assert!(strokes[&locus].moved());
            assert_eq!(material.continuing_state(0).unwrap().to_text(), before);
        }
    }

    #[test]
    fn ck_binding_refuses_foreign_momentum_reference_change_and_predecessor() {
        let (field, material, current, carry) = fixture();
        let mut bad = carry.clone();
        bad.momenta[0][0] += Rat::one();
        assert!(ChannelEndpoint::bind(&field, &material, &current, &bad.change, &bad).is_err());
        let mut bad = carry.clone();
        bad.conductances[0] += Rat::one();
        assert!(ChannelEndpoint::bind(&field, &material, &current, &bad.change, &bad).is_err());
        let mut bad = carry.clone();
        bad.change.states[0][0][0] += Rat::one();
        assert!(ChannelEndpoint::bind(&field, &material, &current, &carry.change, &bad).is_err());
        let bound =
            ChannelEndpoint::bind(&field, &material, &current, &carry.change, &carry).unwrap();
        let mut foreign = material.clone();
        foreign.contacts[0].storage = diagonal(field.contact(0).width(), rat(2, 1));
        assert!(!bound.admits_predecessor(&foreign));
        assert!(reflect(&foreign, &mut foreign.clone(), &mut BTreeMap::new(), &bound).is_err());
    }
}

#[cfg(test)]
mod control_tests {
    use super::*;
    #[test]
    fn ck_ablation_state_keeps_candidate_except_predecessor_ck_and_cold_restores() {
        let field = crate::hnn::tests::learning::chain();
        let mut opening = Constitution::initial(&field, u64::MAX).unwrap();
        let founding = opening.clone();
        let locus = Locus::Channel(0);
        let unit = opening.lattice(locus).unwrap().unit();
        opening.clocks.insert(locus, 2);
        for family in 0..2 {
            opening.carries.insert(
                (locus, Carrier::Factor(family)),
                Carry(BTreeMap::from([(0, &unit / rat(8, 1))])),
            );
        }
        let predecessor = opening.continuing_state(0).unwrap();
        let mut candidate = opening.clone();
        candidate.contacts[0].storage = scaled_identity(field.contact(0).width(), rat(2, 1));
        candidate.contacts[0].stiffness = scaled_identity(field.contact(0).width(), rat(3, 4));
        candidate.contacts[0].dissipation = scaled_identity(field.contact(0).width(), rat(3, 4));
        candidate.contacts[0].scales[0] = rat(5, 4);
        candidate.commit += 1;
        candidate.clocks.insert(locus, 3);
        for family in 0..2 {
            candidate.carries.insert(
                (locus, Carrier::Factor(family)),
                Carry(BTreeMap::from([(0, &unit / rat(4, 1))])),
            );
        }
        let state = candidate.continuing_state(0).unwrap();
        let control = state.held_channel_storage_control(&predecessor).unwrap();
        let restored = founding.continued_on(&field, &control).unwrap();
        assert_eq!(restored.contacts[0].storage, opening.contacts[0].storage);
        assert_eq!(
            restored.contacts[0].stiffness,
            opening.contacts[0].stiffness
        );
        assert_eq!(
            restored.contacts[0].dissipation,
            candidate.contacts[0].dissipation
        );
        assert_eq!(restored.contacts[0].scales, candidate.contacts[0].scales);
        assert_eq!(restored.commit, candidate.commit);
        assert_eq!(restored.clocks, candidate.clocks);
        for family in 0..2 {
            assert_eq!(
                restored.carries.get(&(locus, Carrier::Factor(family))),
                opening.carries.get(&(locus, Carrier::Factor(family)))
            );
        }
        assert_eq!(restored.rings, candidate.rings);
        assert_eq!(restored.continuing_state(0).unwrap(), control);
        let mut bad = predecessor.clone();
        bad.lattices.insert(
            Locus::Channel(0),
            Lattice::new(opening.lattice(Locus::Channel(0)).unwrap().exponent() + 1),
        );
        assert!(state.held_channel_storage_control(&bad).is_err());
        // The complete candidate remains untouched by this disposable control.
        assert_eq!(candidate.continuing_state(0).unwrap(), state);
    }
}
