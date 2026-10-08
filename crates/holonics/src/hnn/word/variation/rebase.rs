//! Rechart the existing full contact first variation through an actual material publication.
//!
//! The caller declares the update differential `P = d theta_after / d theta_before` in the
//! existing raw contact-factor coordinates. It is not inferred from a finite material delta.
//! On an invertible parameter chart the new state columns are
//! `J_after = (H_x J_before + H_before + H_after P) P^-1`, where `H` is the native held-state
//! crossing. A fixed applied factor translation has `P = I`; this declares a fixed action
//! family, not a derivative through the learner's discrete selection or rounding policy.
//! The actual state, references and clock are checked before publishing a successor variation.
//! No Word, event history or extra state/costate carrier is retained. Refs #73 #62.

use super::*;

fn same_change_shape(a: &EndChange, b: &EndChange) -> bool {
    let vectors = |a: &[Vec<Rat>], b: &[Vec<Rat>]| {
        a.len() == b.len() && a.iter().zip(b).all(|(a, b)| a.len() == b.len())
    };
    let pairs = |a: &[[Vec<Rat>; 2]], b: &[[Vec<Rat>; 2]]| {
        a.len() == b.len() && a.iter().zip(b).all(|(a, b)| vectors(a, b))
    };
    vectors(&a.storage, &b.storage)
        && pairs(&a.arrivals, &b.arrivals)
        && pairs(&a.states, &b.states)
        && a.resonator_phases == b.resonator_phases
        && a.resonators.len() == b.resonators.len()
        && a.resonators
            .iter()
            .zip(&b.resonators)
            .all(|(a, b)| match (a, b) {
                (Some(a), Some(b)) => vectors(a, b),
                (None, None) => true,
                _ => false,
            })
}

fn values_mut(change: &mut EndChange) -> impl Iterator<Item = &mut Rat> {
    change
        .storage
        .iter_mut()
        .chain(change.arrivals.iter_mut().flatten())
        .chain(change.states.iter_mut().flatten())
        .chain(change.resonators.iter_mut().flatten().flatten())
        .flatten()
}

fn form_direction(
    factor: &ExactRatMatrix,
    direction: &ExactRatMatrix,
) -> Result<ExactRatMatrix, HnnError> {
    Ok(direction
        .multiply(&factor.transpose()?)?
        .add(&factor.multiply(&direction.transpose()?)?)?)
}

/// The differential of the same native canonical crossing as `PowerForm::held`.
/// Identity storage and direction transport preserve `dw`, including a compatible singular C.
/// Otherwise this first executable rechart requires an invertible new C. Selecting a singular
/// preimage at the primal point does not, by itself, declare the derivative of that selection.
fn held_rate_direction(
    before: &ExactRatMatrix,
    after: &ExactRatMatrix,
    d_before: &ExactRatMatrix,
    d_after: &ExactRatMatrix,
    rate_before: &[Rat],
    rate_after: &[Rat],
    tangent_before: &[Rat],
    inverse_after: Option<&ExactRatMatrix>,
) -> Result<Vec<Rat>, HnnError> {
    if before == after && d_before == d_after && rate_before == rate_after {
        return Ok(tangent_before.to_vec());
    }
    let inverse = inverse_after.ok_or(HnnError::Unadmitted {
        reason: "a nonidentity singular held-storage rechart needs its selected rank/fibre derivative",
    })?;
    let target = sub(
        &add(
            &before.apply(tangent_before)?,
            &d_before.apply(rate_before)?,
        ),
        &d_after.apply(rate_after)?,
    );
    let tangent = inverse.apply(&target)?;
    if after.apply(&tangent)? != target {
        return refuse("the held-state tangent must solve its actual canonical momentum relation");
    }
    Ok(tangent)
}

/// Convert the complete state columns from old parameter coordinates to the declared new
/// coordinates. Discrete phase tags are copied from the actual common state, never combined.
fn reindex_columns(
    columns: &[EndChange],
    inverse: &ExactRatMatrix,
) -> Result<Vec<EndChange>, HnnError> {
    let n = columns.len();
    if n == 0
        || inverse.rows() != n
        || inverse.columns() != n
        || columns
            .iter()
            .any(|column| !same_change_shape(&columns[0], column))
    {
        return refuse(
            "the parameter rechart preserves every full state column and its actual phase topology",
        );
    }
    if inverse == &ExactRatMatrix::identity(n)? {
        return Ok(columns.to_vec());
    }
    (0..n)
        .map(|new_coordinate| {
            let mut column = columns[0].clone();
            for value in values_mut(&mut column) {
                *value = Rat::zero();
            }
            for (old_coordinate, old) in columns.iter().enumerate() {
                let weight = inverse.get(old_coordinate, new_coordinate)?;
                if weight.is_zero() {
                    continue;
                }
                for (value, old) in values_mut(&mut column).zip(values(old)) {
                    *value += weight * old;
                }
            }
            Ok(column)
        })
        .collect()
}

impl HeldContactVariation {
    /// Rebind the current full-state differential after one *actual* native contact publication.
    ///
    /// `before` is this variation's reached carry. `after` is the native held-state result at
    /// the same crossing, not a newly simulated trajectory. `parameter_transport` must be the
    /// declared derivative of the admitted update/action family in `coordinates()` order.
    /// An identity is valid for a declared fixed applied factor translation; the actual finite
    /// before/after movement, a step certificate, or a normal-law rounding receipt does not
    /// establish that derivative. A learner-policy derivative must come from its actual owner.
    ///
    /// This method is atomic: all work happens on a detached successor. An unsupported chart,
    /// phase/reference/reader change, singular transport, rank crossing or budget refusal leaves
    /// the current variation intact. Source admission remains the existing `opened()` projection.
    pub(crate) fn rebased(
        &self,
        field: &Field,
        current: &Current,
        successor: &Constitution,
        before: &ReceptionCarry,
        after: &ReceptionCarry,
        parameter_transport: &ExactRatMatrix,
    ) -> Result<Self, HnnError> {
        let n = self.coordinates.len();
        if n == 0
            || self.columns.len() != n
            || parameter_transport.rows() != n
            || parameter_transport.columns() != n
            || !before.fits(field)
            || !after.fits(field)
            || !self.matches(&self.producing, before)
            || after.ticks != before.ticks
            || after.conductances != before.conductances
            || !same_change_shape(&before.change, &after.change)
            || self
                .columns
                .iter()
                .any(|chi| !same_change_shape(chi, &before.change))
            || successor.released() != self.producing.released()
        {
            return refuse(
                "a contact rechart binds the actual full current, clock, references and parameter topology",
            );
        }
        let identity = ExactRatMatrix::identity(n)?;
        let inverse_parameter = match if parameter_transport == &identity {
            Ok(identity.clone())
        } else {
            parameter_transport.inverse()
        } {
            Ok(inverse) => inverse,
            Err(_) => {
                return refuse(
                    "a singular parameter transport needs a declared retained fibre instead of a current-coordinate gradient",
                );
            }
        };
        // ExactRatMatrix::inverse certifies both sides; the identity constructor is exact.
        let old_ops = Operands::exact_at_cut(field, &self.producing, current)?;
        let new_ops = Operands::exact_at_cut(field, successor, current)?;
        admit(&old_ops)?;
        admit(&new_ops)?;
        if new_ops.resonators() != old_ops.resonators()
            || new_ops.surfaces() != old_ops.surfaces()
            || new_ops.step() != old_ops.step()
        {
            return refuse(
                "contact sensitivity rechart preserves its loaded, surface and clock declarations",
            );
        }
        for g in 0..field.rings().len() {
            if self.producing.standing(g) != successor.standing(g)
                || self.producing.passive_factor(g) != successor.passive_factor(g)
                || self.producing.contrast_port(g) != successor.contrast_port(g)
                || self.producing.slices(g) != successor.slices(g)
                || self.producing.source_port(g) != successor.source_port(g)
                || self.producing.receiving_map(g) != successor.receiving_map(g)
                || self.producing.receiving_carrier(g) != successor.receiving_carrier(g)
                || self.producing.transport(g) != successor.transport(g)
            {
                return refuse(
                    "a changing source or receiving chart supplies its own direct sensitivity term",
                );
            }
            for offset in 0..field.offsets().len() {
                if self.producing.pair_port(g, offset) != successor.pair_port(g, offset) {
                    return refuse(
                        "a contact sensitivity rechart keeps its actual pair-source chart",
                    );
                }
            }
            match (
                &old_ops.resonators()[g],
                &before.change.resonators[g],
                &before.resonator_momenta[g],
                &after.resonator_momenta[g],
            ) {
                (Some(resonator), Some([_, w]), Some(pi), Some(after_pi))
                    if resonator.material().forms().0.apply(w)? == *pi
                        && after_pi == pi
                        && before.change.resonator_phases[g]
                            == Some(resonator.phase_at(before.ticks.saturating_sub(1))) => {}
                (None, None, None, None) => {}
                _ => {
                    return refuse(
                        "the contact rechart keeps its actual loaded momentum and absolute pump phase",
                    );
                }
            }
        }
        for a in 0..field.contacts().len() {
            if self.producing.contact_stiffness_signature(a).is_some()
                || successor.contact_stiffness_signature(a).is_some()
                || self.producing.contact_surface_storage(a) != successor.contact_surface_storage(a)
                || old_ops.contacts()[a].conductance() != new_ops.contacts()[a].conductance()
                || old_ops.contacts()[a].conductance() != &self.references[a]
            {
                return refuse(
                    "the contact rechart preserves its admitted signature and actual reference",
                );
            }
            for (old, new) in factors(&self.producing, a)
                .into_iter()
                .zip(factors(successor, a))
            {
                if old.rows() != new.rows() || old.columns() != new.columns() {
                    return refuse(
                        "a parameter shape change needs a declared coordinate transport and retained fibre",
                    );
                }
            }
            let c_before = old_ops.contacts()[a].forms().0;
            let c_after = new_ops.contacts()[a].forms().0;
            if c_before.apply(&before.change.states[a][1])? != before.momenta[a]
                || c_after.apply(&after.change.states[a][1])? != after.momenta[a]
                || before.momenta[a] != after.momenta[a]
            {
                return refuse(
                    "the material rechart consumes the actual unchanged canonical contact momentum",
                );
            }
        }
        let old_form = PowerForm::read(field, &self.producing, current)?;
        let new_form = PowerForm::read(field, successor, current)?;
        if old_form.held(&new_form, &before.change)?.change != after.change {
            return refuse(
                "the sensitivity crossing is the same actual native held-state publication",
            );
        }
        // These are coefficients of the present local crossing, not an archive of publications.
        let inverse_storage: Vec<_> = new_ops
            .contacts()
            .iter()
            .map(|contact| contact.forms().0.inverse().ok())
            .collect();
        let mut raw_columns = self.columns.clone();
        for (j, chi) in raw_columns.iter_mut().enumerate() {
            let old_coordinate = &self.coordinates[j];
            for a in 0..field.contacts().len() {
                let old_factor = self.producing.contact_storage(a);
                let new_factor = successor.contact_storage(a);
                let mut old_entries =
                    vec![vec![Rat::zero(); old_factor.columns()]; old_factor.rows()];
                if old_coordinate.contact == a && old_coordinate.family == 0 {
                    old_entries[old_coordinate.row][old_coordinate.column] = integer(1);
                }
                let old_direction =
                    ExactRatMatrix::shaped(old_factor.rows(), old_factor.columns(), old_entries)?;
                let mut new_entries =
                    vec![vec![Rat::zero(); new_factor.columns()]; new_factor.rows()];
                for (i, coordinate) in self.coordinates.iter().enumerate() {
                    if coordinate.contact == a && coordinate.family == 0 {
                        let weight = parameter_transport.get(i, j)?;
                        if !weight.is_zero() {
                            new_entries[coordinate.row][coordinate.column] = weight.clone();
                        }
                    }
                }
                let new_direction =
                    ExactRatMatrix::shaped(new_factor.rows(), new_factor.columns(), new_entries)?;
                let d_before = form_direction(old_factor, &old_direction)?;
                let d_after = form_direction(new_factor, &new_direction)?;
                chi.states[a][1] = held_rate_direction(
                    old_ops.contacts()[a].forms().0,
                    new_ops.contacts()[a].forms().0,
                    &d_before,
                    &d_after,
                    &before.change.states[a][1],
                    &after.change.states[a][1],
                    &self.columns[j].states[a][1],
                    inverse_storage[a].as_ref(),
                )?;
            }
        }
        let mut next = self.clone();
        next.columns = reindex_columns(&raw_columns, &inverse_parameter)?;
        next.producing = successor.clone();
        // Time has not elapsed at a material crossing. Keep work/tick admissions and all phase
        // tags; the actual next Word recomputes its forcing at successor factors through advanced().
        next.read_bits()?;
        if !next.matches(successor, after) {
            return refuse("the rebased full sensitivity is bound to the native successor current");
        }
        Ok(next)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::geometry::{RatVec3, screw::ScrewGenerator};
    use crate::hnn::constitution::CAMPAIGN_ONE_BUDGET;
    use crate::hnn::field::{
        ContactDeclaration, CribDeclaration, FieldDeclaration, RingDeclaration,
    };
    use crate::ratio::rat;

    fn matrix(value: Rat) -> ExactRatMatrix {
        ExactRatMatrix::new(vec![vec![value]]).unwrap()
    }

    #[test]
    fn fixed_factor_translation_differentiates_the_native_held_rate() {
        // f_after=f_before+1, w_after=(f_before/(f_before+1))^2*(2/3).
        // Its actual derivative at f_before=2 is 2f/(f+1)^3*(2/3)=8/81.
        let before = matrix(integer(4));
        let after = matrix(integer(9));
        let inverse = after.inverse().unwrap();
        let got = held_rate_direction(
            &before,
            &after,
            &matrix(integer(4)),
            &matrix(integer(6)),
            &[rat(2, 3)],
            &[rat(8, 27)],
            &[integer(0)],
            Some(&inverse),
        )
        .unwrap();
        assert_eq!(got, vec![rat(8, 81)]);
        assert_eq!(after.apply(&got).unwrap(), vec![rat(8, 9)]);
    }

    #[test]
    fn identity_crossing_keeps_a_singular_compatible_rate_tangent() {
        let zero = matrix(integer(0));
        assert_eq!(
            held_rate_direction(
                &zero,
                &zero,
                &zero,
                &zero,
                &[rat(2, 3)],
                &[rat(2, 3)],
                &[rat(5, 7)],
                None
            )
            .unwrap(),
            vec![rat(5, 7)]
        );
        assert!(
            held_rate_direction(
                &matrix(integer(1)),
                &zero,
                &zero,
                &zero,
                &[integer(0)],
                &[integer(0)],
                &[integer(1)],
                None
            )
            .is_err()
        );
    }

    fn column(a: Rat, b: Rat) -> EndChange {
        EndChange {
            storage: vec![vec![integer(0)]],
            arrivals: vec![[vec![a.clone()], vec![b.clone()]]],
            states: vec![[vec![b.clone()], vec![a.clone()]]],
            resonators: vec![Some([vec![a], vec![b]])],
            resonator_phases: vec![Some(1)],
        }
    }

    #[test]
    fn parameter_rechart_transforms_full_hidden_credit_by_the_inverse_dual() {
        let transport = ExactRatMatrix::new(vec![
            vec![integer(1), integer(2)],
            vec![integer(0), integer(1)],
        ])
        .unwrap();
        let inverse = transport.inverse().unwrap();
        let old = vec![
            column(integer(1), integer(3)),
            column(integer(4), integer(7)),
        ];
        let new = reindex_columns(&old, &inverse).unwrap();
        let dual = ChangeCovector {
            storage: vec![vec![integer(0)]],
            arrivals: vec![[vec![integer(2)], vec![integer(-1)]]],
            states: vec![[vec![integer(3)], vec![integer(5)]]],
            resonators: vec![Some([vec![integer(7)], vec![integer(11)]])],
        };
        let old_credit: Vec<_> = old.iter().map(|chi| dual.pairing(chi)).collect();
        let new_credit: Vec<_> = new.iter().map(|chi| dual.pairing(chi)).collect();
        assert_eq!(
            new_credit,
            inverse.transpose().unwrap().apply(&old_credit).unwrap()
        );
        assert_ne!(new_credit[1], old_credit[1]);
        assert_eq!(new[0].resonator_phases, vec![Some(1)]);
        assert_eq!(new[1].resonator_phases, vec![Some(1)]);
        assert!(new.iter().all(|chi| chi.storage[0] == vec![integer(0)]));
    }

    #[test]
    fn parameter_rechart_refuses_a_truncated_or_mismatched_phase_column() {
        let mut incomplete = column(integer(1), integer(2));
        incomplete.arrivals.clear();
        let original = column(integer(3), integer(4));
        let identity = ExactRatMatrix::identity(2).unwrap();
        assert!(reindex_columns(&[original.clone(), incomplete], &identity).is_err());
        let mut wrong_phase = original.clone();
        wrong_phase.resonator_phases[0] = Some(0);
        assert!(reindex_columns(&[original, wrong_phase], &identity).is_err());
    }

    #[test]
    fn native_canonical_state_and_current_parameter_columns_survive_two_rebases() {
        let ring = || RingDeclaration {
            period: 2,
            screw: ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
            placements: vec![RatVec3::from_i64(1, 0, 0), RatVec3::from_i64(-1, 0, 0)],
            lock: vec![0, 1],
            reflector: vec![0, 1],
            admittance: integer(2),
            initial: 0,
        };
        let field = Field::declare(
            FieldDeclaration {
                rings: vec![ring(), ring()],
                contacts: vec![ContactDeclaration {
                    from: 0,
                    to: 1,
                    channel: vec![(0, 0)],
                    admittance: integer(2),
                    exponent: integer(0),
                }],
                loops: vec![],
                sources: vec![0],
                offsets: vec![],
                alphabet: 2,
                step: integer(1),
                exponent_grain: 1,
                receivers: vec![],
                crib: CribDeclaration {
                    window: 16,
                    offset: 1,
                },
                population: 1 << 16,
                lattice: Default::default(),
            }
            .by_lattice_rule(),
        )
        .unwrap();
        let identity = ExactRatMatrix::identity(2).unwrap();
        let before_theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET)
            .unwrap()
            .with_channel(
                0,
                identity.scaled(&integer(2)),
                identity.clone(),
                identity.clone(),
            )
            .unwrap();
        let current = Current::at_rest(&field);
        let before_ops = Operands::exact_at_cut(&field, &before_theta, &current).unwrap();
        let mut seed = EndChange::rest(&field, &before_ops);
        seed.states[0][1][0] = rat(2, 3);
        let nothing: Vec<_> = seed
            .storage
            .iter()
            .map(|row| vec![Rat::zero(); row.len()])
            .collect();
        let before = Word::continuing(&field, before_ops, &seed, &nothing, 0)
            .unwrap()
            .reception_end()
            .unwrap();
        let parameters = 3 * identity.rows() * identity.columns();
        let variation = HeldContactVariation::begin(
            &field,
            &before_theta,
            &current,
            Some(&before),
            VariationBudget {
                ratios: parameters * values(&seed).count(),
                bits: CAMPAIGN_ONE_BUDGET,
                column_ticks: 0,
            },
        )
        .unwrap();
        let transport = ExactRatMatrix::identity(parameters).unwrap();
        let mut theta = before_theta;
        let mut carry = before;
        let mut variation = variation;
        for factor in [integer(3), integer(4)] {
            let next_theta = theta
                .clone()
                .with_channel(
                    0,
                    identity.scaled(&factor),
                    identity.clone(),
                    identity.clone(),
                )
                .unwrap();
            let held = PowerForm::read(&field, &theta, &current)
                .unwrap()
                .held(
                    &PowerForm::read(&field, &next_theta, &current).unwrap(),
                    &carry.change,
                )
                .unwrap();
            let next_carry = Word::continuing(
                &field,
                Operands::exact_at_cut(&field, &next_theta, &current).unwrap(),
                &held.change,
                &nothing,
                carry.ticks,
            )
            .unwrap()
            .reception_end()
            .unwrap();
            let new = variation
                .rebased(
                    &field,
                    &current,
                    &next_theta,
                    &carry,
                    &next_carry,
                    &transport,
                )
                .unwrap();
            assert!(new.matches(&next_theta, &next_carry));
            assert_eq!(new.reading().next_tick, variation.reading().next_tick);
            assert_eq!(new.reading().column_ticks, variation.reading().column_ticks);
            assert_eq!(new.coordinates(), variation.coordinates());
            variation = new;
            theta = next_theta;
            carry = next_carry;
        }
        assert_eq!(carry.change.states[0][1][0], rat(1, 6));
        // With the two actual translations held as controls, w=(f/(f+2))^2*(2/3).
        // At f=2 its derivative, expressed at the current coordinate f+2, is 1/12.
        assert_eq!(variation.columns()[0].states[0][1][0], rat(1, 12));
        let old_columns = variation.columns().to_vec();
        let singular = ExactRatMatrix::zero(parameters, parameters).unwrap();
        assert!(
            variation
                .rebased(&field, &current, &theta, &carry, &carry, &singular)
                .is_err()
        );
        assert_eq!(variation.columns(), old_columns);
    }
}
