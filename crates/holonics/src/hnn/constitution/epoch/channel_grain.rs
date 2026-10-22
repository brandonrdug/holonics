//! Candidate-local exact channel grain rebases.
//!
//! This module is intentionally separate from the scheduler and from `Constitution::rebased`.
//! It changes only the requested channel carrier representation, does not deposit or commit, and
//! leaves the persistent channel clock untouched. The caller owns the absolute target lattice.

use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ChannelGrainRebase {
    pub(crate) contact: usize,
    pub(crate) before_lattice: Lattice,
    pub(crate) after_lattice: Lattice,
    pub(crate) requested_lattice: Lattice,
    /// First held C/K factor entry that would move at the next finer level.
    pub(crate) limiting: Option<(Carrier, usize, Rat)>,
    /// Exact represented factor changes from rebase alone, in C/K/D order.
    pub(crate) factor_delta: [ExactRatMatrix; 3],
}

const FACTOR_CARRIERS: [Carrier; 3] = [Carrier::Factor(0), Carrier::Factor(1), Carrier::Factor(2)];
const SCALE_CARRIERS: [Carrier; 3] = [Carrier::FactorScale(0), Carrier::FactorScale(1), Carrier::FactorScale(2)];

fn refuse(reason: &'static str) -> HnnError {
    HnnError::Unadmitted { reason }
}

fn channel_parts(material: &Constitution, contact: usize) -> Result<(&ContactMaterial, Lattice), HnnError> {
    let locus = Locus::Channel(contact);
    let channel = material.contacts.get(contact).ok_or(HnnError::Lattice { locus })?;
    let lattice = material.lattice(locus)?;
    Ok((channel, lattice))
}

fn conservation_holds(
    before: &[Rat],
    after: &[Rat],
    old_carry: &Carry,
    new_carry: &Carry,
) -> bool {
    before.len() == after.len()
        && before.iter().zip(after).enumerate().all(|(index, (old, new))| {
            old + old_carry.0.get(&index).cloned().unwrap_or_else(Rat::zero)
                == new + new_carry.0.get(&index).cloned().unwrap_or_else(Rat::zero)
        })
}

fn matrix_delta(before: &ExactRatMatrix, after: &ExactRatMatrix) -> Result<ExactRatMatrix, HnnError> {
    if (before.rows(), before.columns()) != (after.rows(), after.columns()) {
        return Err(HnnError::Shape {
            what: "channel grain rebase factor",
            expected: before.rows() * before.columns(),
            found: after.rows() * after.columns(),
        });
    }
    flat_matrix(
        before.rows(),
        before.columns(),
        before.entries().iter().zip(after.entries()).map(|(a, b)| b - a).collect(),
    )
}

/// Quotient-zero is monotone as the exponent decreases. The half-open tie is read by
/// div_rem itself: a negative half-unit is held, a positive half-unit lands. Binary search
/// therefore finds the largest safe exponent without inspecting every intervening level.
pub(super) fn largest_held_factor_lattice(
    opening: &Constitution, contact: usize, current: Lattice, target: Lattice,
) -> Result<(Lattice, Option<(Carrier, usize, Rat)>), HnnError> {
    let locus = Locus::Channel(contact);
    let channel = opening.contacts.get(contact).ok_or(HnnError::Lattice { locus })?;
    for (family, matrix) in [&channel.storage, &channel.stiffness].into_iter().enumerate() {
        if let Some(carry) = opening.carries.get(&(locus, Carrier::Factor(family))) {
            if let Some((&entry, _)) = carry.0.last_key_value() {
                if entry >= matrix.entries().len() {
                    return Err(HnnError::Shape { what: "held channel factor carry", expected: matrix.entries().len(), found: entry + 1 });
                }
            }
        }
    }
    let first = |exponent| {
        let lattice = Lattice::new(exponent);
        (0..2).find_map(|family| {
            opening.carries.get(&(locus, Carrier::Factor(family))).and_then(|carry| {
                carry.0.iter().find(|(_, r)| !lattice.div_rem(r).0.is_zero())
                    .map(|(&entry, r)| (Carrier::Factor(family), entry, r.clone()))
            })
        })
    };
    if first(current.exponent()).is_some() {
        return Err(refuse("held channel factor carry is outside its current half unit"));
    }
    let mut low = current.exponent();
    let mut high = target.exponent();
    while low < high {
        let middle = low + ((u64::from(high - low) + 1) / 2) as u32;
        if first(middle).is_none() { low = middle; } else { high = middle - 1; }
    }
    let bound = if low < target.exponent() { first(low + 1) } else { None };
    Ok((Lattice::new(low), bound))
}

/// Apply explicit absolute channel lattice targets atomically to a staged clone.
///
/// A missing target is an intentional no-op. Targets outside `retained`, unknown contacts,
/// released channels, or changed candidate channel state are refused.
/// A target already met or exceeded is a no-op; a coarser target cannot coarsen the current state.
/// All six factor/scale carriers are passed to the
/// existing exact `BudgetedCarry::rebase`; C and K factor entries remain represented exactly.
/// All three scales are statistics and rebase losslessly. A C/K factor carry bounds the
/// attained exponent; its shortfall waits for that family's own certified physical ray.
pub(crate) fn stage_rebases(
    opening: &Constitution,
    candidate: &mut Constitution,
    targets: &BTreeMap<usize, Lattice>,
    retained: &BTreeSet<Locus>,
) -> Result<BTreeMap<usize, ChannelGrainRebase>, HnnError> {
    let original_commit = candidate.commit;
    let original_clocks = candidate.clocks.clone();
    let mut staged = candidate.clone();
    let mut readings = BTreeMap::new();
    for (&contact, &target) in targets {
        let locus = Locus::Channel(contact);
        if !retained.contains(&locus) {
            return Err(refuse("channel grain target is not retained at this receiver"));
        }
        if opening.released.contains(&locus) || staged.released.contains(&locus) {
            return Err(HnnError::ReleasedLocus { locus });
        }
        let (old, before_lattice) = channel_parts(opening, contact)?;
        let (now, candidate_lattice) = channel_parts(&staged, contact)?;
        let carries_match = FACTOR_CARRIERS
            .into_iter()
            .chain(SCALE_CARRIERS)
            .all(|carrier| opening.carries.get(&(locus, carrier)) == staged.carries.get(&(locus, carrier)));
        if old != now
            || !carries_match
            || before_lattice != candidate_lattice
        {
            return Err(refuse("candidate channel must match its opening before grain rebase"));
        }
        if target.exponent() <= before_lattice.exponent() {
            continue;
        }

        let requested_lattice = target;
        let (target, limiting) = largest_held_factor_lattice(opening, contact, before_lattice, target)?;
        let levels = target.exponent() - before_lattice.exponent();
        if levels == 0 {
            readings.insert(contact, ChannelGrainRebase {
                contact, before_lattice, after_lattice: before_lattice, requested_lattice, limiting,
                factor_delta: [
                    ExactRatMatrix::zero(old.storage.rows(), old.storage.columns())?,
                    ExactRatMatrix::zero(old.stiffness.rows(), old.stiffness.columns())?,
                    ExactRatMatrix::zero(old.dissipation.rows(), old.dissipation.columns())?,
                ],
            });
            continue;
        }
        let next_clock = opening.clock(locus).checked_add(1).ok_or(HnnError::Rebase {
            exponent: before_lattice.exponent(),
            levels,
            staged: 0,
        })?;

        let old_matrices = [old.storage.clone(), old.stiffness.clone(), old.dissipation.clone()];
        let old_scales = old.scales.clone();
        let mut entries: [Vec<Rat>; 6] = [
            old_matrices[0].entries().to_vec(),
            old_matrices[1].entries().to_vec(),
            old_matrices[2].entries().to_vec(),
            vec![old_scales[0].clone()],
            vec![old_scales[1].clone()],
            vec![old_scales[2].clone()],
        ];
        let old_carries: [Carry; 6] = std::array::from_fn(|i| {
            let carrier = if i < 3 { FACTOR_CARRIERS[i] } else { SCALE_CARRIERS[i - 3] };
            opening.carries.get(&(locus, carrier)).cloned().unwrap_or_default()
        });
        let mut carries = old_carries.clone();
        {
            let mut at = BudgetedCarry::new(before_lattice, next_clock);
            // Split both arrays before borrowing their elements so every carrier has a distinct
            // mutable borrow for the duration of the shared rebase call.
            let [c0, c1, c2, c3, c4, c5] = &mut carries;
            let [e0, e1, e2, e3, e4, e5] = &mut entries;
            let arrays: &mut [(&mut Carry, &mut [Rat])] = &mut [
                (c0, e0.as_mut_slice()),
                (c1, e1.as_mut_slice()),
                (c2, e2.as_mut_slice()),
                (c3, e3.as_mut_slice()),
                (c4, e4.as_mut_slice()),
                (c5, e5.as_mut_slice()),
            ];
            at.rebase(levels, arrays)?;
            if at.lattice() != target || !at.released().is_empty() || at.moved() {
                return Err(refuse("channel grain rebase violated its representation-only contract"));
            }
        }

        let mut new_matrices = Vec::with_capacity(3);
        for i in 0..3 {
            let before = old_matrices[i].entries();
            if !conservation_holds(before, &entries[i], &old_carries[i], &carries[i]) {
                return Err(refuse("channel factor entry plus carry was not conserved exactly"));
            }
            new_matrices.push(flat_matrix(
                old_matrices[i].rows(),
                old_matrices[i].columns(),
                entries[i].clone(),
            )?);
        }
        for i in 0..3 {
            if !conservation_holds(
                std::slice::from_ref(&old_scales[i]),
                &entries[i + 3],
                &old_carries[i + 3],
                &carries[i + 3],
            ) {
                return Err(refuse("channel factor scale plus carry was not conserved exactly"));
            }
        }
        if new_matrices[0] != old_matrices[0]
            || new_matrices[1] != old_matrices[1]
        {
            return Err(refuse("channel grain rebase would change represented C/K factor entries"));
        }

        let deltas = [
            matrix_delta(&old_matrices[0], &new_matrices[0])?,
            matrix_delta(&old_matrices[1], &new_matrices[1])?,
            matrix_delta(&old_matrices[2], &new_matrices[2])?,
        ];
        let after_lattice = target;
        let contact_state = staged.contacts.get_mut(contact).ok_or(HnnError::Lattice { locus })?;
        contact_state.storage = new_matrices.remove(0);
        contact_state.stiffness = new_matrices.remove(0);
        contact_state.dissipation = new_matrices.remove(0);
        contact_state.scales = [entries[3][0].clone(), entries[4][0].clone(), entries[5][0].clone()];
        for i in 0..6 {
            let carrier = if i < 3 { FACTOR_CARRIERS[i] } else { SCALE_CARRIERS[i - 3] };
            if carries[i].0.is_empty() {
                staged.carries.remove(&(locus, carrier));
            } else {
                staged.carries.insert((locus, carrier), carries[i].clone());
            }
        }
        staged.lattices.insert(locus, after_lattice);
        readings.insert(contact, ChannelGrainRebase {
            contact,
            before_lattice,
            after_lattice,
            requested_lattice,
            limiting,
            factor_delta: deltas,
        });
    }

    if staged.commit != original_commit || staged.clocks != original_clocks {
        return Err(refuse("channel grain staging changed commit or persistent clocks"));
    }
    *candidate = staged;
    Ok(readings)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> (Field, Constitution) {
        let declaration = crate::hnn::tests::learning::chain_declaration(1 << 16);
        let field = Field::declare(declaration.by_lattice_rule()).unwrap();
        let material = Constitution::initial(&field, 1 << 40).unwrap();
        (field, material)
    }

    fn synthetic_carry(material: &mut Constitution, contact: usize, clock: u64, carrier: Carrier, value: Rat) {
        let locus = Locus::Channel(contact);
        material.clocks.insert(locus, clock);
        let mut carry = Carry::default();
        carry.0.insert(0, value);
        material.carries.insert((locus, carrier), carry);
    }

    #[test]
    fn held_factor_bound_reads_positive_and_negative_half_ties() {
        let (_field, mut opening) = fixture();
        let locus = Locus::Channel(0);
        let current = opening.lattice(locus).unwrap();
        let amount = current.unit() / crate::ratio::integer(4);
        for (remainder, levels) in [(amount.clone(), 0), (-amount, 1)] {
            synthetic_carry(&mut opening, 0, 7, Carrier::Factor(0), remainder);
            let (attained, limiting) = largest_held_factor_lattice(&opening, 0, current, Lattice::new(current.exponent()+4)).unwrap();
            assert_eq!(attained.exponent(), current.exponent()+levels);
            assert!(limiting.is_some());
        }
    }

    #[test]
    fn two_contacts_rebase_all_six_legal_gamma_grid_carries_without_clock_or_commit() {
        let (_field, mut opening) = fixture();
        let contacts = opening.contacts.len();
        assert!(contacts >= 2);
        for contact in 0..2 {
            let lattice = opening.lattice(Locus::Channel(contact)).unwrap();
            let amount = lattice.unit() / crate::ratio::integer(32);
            for carrier in FACTOR_CARRIERS.into_iter().chain(SCALE_CARRIERS) {
                synthetic_carry(&mut opening, contact, 7, carrier, amount.clone());
            }
        }
        let before_commit = opening.commit;
        let before_clocks = opening.clocks.clone();
        let mut candidate = opening.clone();
        let targets = (0..2).map(|contact| {
            let before = opening.lattice(Locus::Channel(contact)).unwrap();
            (contact, Lattice::new(before.exponent() + 1))
        }).collect();
        let retained = [Locus::Channel(0), Locus::Channel(1)].into_iter().collect();
        let result = stage_rebases(&opening, &mut candidate, &targets, &retained);
        // These six lawful synthetic remainders stay below the finer half-unit at one level;
        // all six are still carried and conserved exactly.
        assert!(result.is_ok());
        assert_eq!(candidate.commit, before_commit);
        assert_eq!(candidate.clocks, before_clocks);
        assert_eq!(candidate.lattice(Locus::Channel(0)).unwrap(), targets[&0]);
        assert_eq!(candidate.lattice(Locus::Channel(1)).unwrap(), targets[&1]);
        for contact in 0..2 {
            for carrier in FACTOR_CARRIERS.into_iter().chain(SCALE_CARRIERS) {
                assert!(candidate.carries.contains_key(&(Locus::Channel(contact), carrier)));
            }
        }
    }

    #[test]
    fn d_remainder_lands_all_scales_rebase_and_ck_factor_carries_bound_levels() {
        let (field, mut opening) = fixture();
        let founding = opening.clone();
        let locus = Locus::Channel(0);
        let old_lattice = opening.lattice(locus).unwrap();
        let amount = old_lattice.unit() / crate::ratio::integer(32); // gamma(7)=5 grid
        synthetic_carry(&mut opening, 0, 7, Carrier::Factor(2), amount.clone());
        synthetic_carry(&mut opening, 0, 7, Carrier::FactorScale(2), amount.clone());
        let mut candidate = opening.clone();
        let mut targets = BTreeMap::new();
        targets.insert(0, Lattice::new(old_lattice.exponent() + 8));
        let retained = [locus].into_iter().collect();
        let result = stage_rebases(&opening, &mut candidate, &targets, &retained).unwrap();
        assert_eq!(result[&0].factor_delta[2].entries()[0], amount);
        assert_ne!(candidate.contacts[0].dissipation, opening.contacts[0].dissipation);
        assert_ne!(candidate.contacts[0].scales[2], opening.contacts[0].scales[2]);
        assert_eq!(candidate.contacts[0].storage, opening.contacts[0].storage);
        assert_eq!(candidate.contacts[0].stiffness, opening.contacts[0].stiffness);
        let checkpoint = candidate.continuing_state(0).unwrap().to_text();
        let state = ContinuingState::from_text(&checkpoint, opening.budget()).unwrap();
        let cold = founding.continued_on(&field, &state).unwrap();
        assert_eq!(cold, candidate);
        assert_eq!(cold.continuing_state(0).unwrap().to_text(), checkpoint);
        let mut cold_again = cold.clone();
        assert!(stage_rebases(&cold, &mut cold_again, &targets, &retained).unwrap().is_empty());
        assert_eq!(cold_again, candidate, "cold continuation must preserve the already-landed target");

        for carrier in [
            Carrier::Factor(0),
            Carrier::FactorScale(0),
            Carrier::Factor(1),
            Carrier::FactorScale(1),
        ] {
            let mut invalid_opening = opening.clone();
            synthetic_carry(&mut invalid_opening, 0, 7, carrier, amount.clone());
            let mut invalid_candidate = invalid_opening.clone();
            let before = invalid_candidate.clone();
            let result = stage_rebases(&invalid_opening, &mut invalid_candidate, &targets, &retained).unwrap();
            if matches!(carrier, Carrier::Factor(_)) {
                assert_eq!(result[&0].after_lattice.exponent(), old_lattice.exponent() + 3);
                assert!(result[&0].limiting.is_some());
                assert_eq!(invalid_candidate.contacts[0].storage, before.contacts[0].storage);
                assert_eq!(invalid_candidate.contacts[0].stiffness, before.contacts[0].stiffness);
            } else {
                assert_eq!(result[&0].after_lattice, targets[&0]);
                assert!(result[&0].limiting.is_none());
                let family = if carrier == Carrier::FactorScale(0) { 0 } else { 1 };
                assert_eq!(&invalid_candidate.contacts[0].scales[family] - &before.contacts[0].scales[family], amount);
            }
        }
    }

    #[test]
    fn failure_on_second_contact_rolls_back_first_contact_rebase() {
        let (_field, mut opening) = fixture();
        assert!(opening.contacts.len() >= 2);
        let amount0 = opening.lattice(Locus::Channel(0)).unwrap().unit() / crate::ratio::integer(32);
        let amount1 = opening.lattice(Locus::Channel(1)).unwrap().unit() / crate::ratio::integer(32);
        synthetic_carry(&mut opening, 0, 7, Carrier::Factor(2), amount0);
        synthetic_carry(&mut opening, 1, 7, Carrier::Factor(1), amount1);
        let bad_index = opening.contacts[1].stiffness.entries().len();
        opening.carries.get_mut(&(Locus::Channel(1), Carrier::Factor(1))).unwrap().0.insert(bad_index, Rat::one());
        let mut candidate = opening.clone();
        let before = candidate.clone();
        let mut targets = BTreeMap::new();
        targets.insert(0, Lattice::new(opening.lattice(Locus::Channel(0)).unwrap().exponent() + 8));
        targets.insert(1, Lattice::new(opening.lattice(Locus::Channel(1)).unwrap().exponent() + 8));
        let retained = [Locus::Channel(0), Locus::Channel(1)].into_iter().collect();
        assert!(stage_rebases(&opening, &mut candidate, &targets, &retained).is_err());
        assert_eq!(candidate, before, "second-contact malformed K carry must roll back the first D rebase");
    }

    #[test]
    fn missing_foreign_released_and_coarsening_targets_are_bounded() {
        let (_field, opening) = fixture();
        let locus = Locus::Channel(0);
        let mut candidate = opening.clone();
        let empty = BTreeMap::new();
        assert!(stage_rebases(&opening, &mut candidate, &empty, &BTreeSet::new()).unwrap().is_empty());
        let mut targets = BTreeMap::new();
        targets.insert(opening.contacts.len(), Lattice::new(1));
        assert!(stage_rebases(&opening, &mut candidate, &targets, &BTreeSet::new()).is_err());
        targets.clear();
        targets.insert(0, Lattice::new(0));
        assert!(stage_rebases(&opening, &mut candidate, &targets, &[locus].into_iter().collect()).unwrap().is_empty());
        assert_eq!(candidate, opening, "a coarser target must preserve the current finer state");
        targets.clear();
        let mut malformed = opening.clone();
        let rows = malformed.contacts[0].storage.rows();
        let columns = malformed.contacts[0].storage.columns();
        let mut bad_carry = Carry::default();
        bad_carry.0.insert(rows * columns, Rat::one());
        malformed.carries.insert((locus, Carrier::Factor(0)), bad_carry);
        let mut malformed_candidate = malformed.clone();
        let before = malformed_candidate.clone();
        let mut targets = BTreeMap::new();
        targets.insert(0, Lattice::new(malformed.lattice(locus).unwrap().exponent() + 1));
        assert!(stage_rebases(&malformed, &mut malformed_candidate, &targets, &[locus].into_iter().collect()).is_err());
        assert_eq!(malformed_candidate, before, "bad carrier shape must roll back atomically");
        let mut released = opening.clone();
        released.released.insert(locus);
        let mut candidate = released.clone();
        let mut targets = BTreeMap::new();
        targets.insert(0, Lattice::new(opening.lattice(locus).unwrap().exponent() + 1));
        assert!(stage_rebases(&released, &mut candidate, &targets, &[locus].into_iter().collect()).is_err());
    }
}
