//! Exact reference for an oriented passage along actual contact joins.
//!
//! The declared connection is the overlap of the producing contact columns. Each join composes
//! the existing paired reflection with reversal of the receiving branch. No phase angle is
//! supplied separately. The exact point differential and declared-grain forward enclosure are
//! exterior references. Native use must retain the producing map, chronology and full defect.
use super::*;
use num_traits::Signed;
use std::collections::BTreeMap;

struct ContactJoin {
    before: usize,
    after: usize,
    reflection: PairedJunctionLinearization,
}

/// Ordered source joins at one contact cut, with the actual forward carriers required by return.
pub struct CausalContactPropagation {
    contacts: Vec<Vec<Wave>>,
    joins: Vec<ContactJoin>,
    internal: Vec<Wave>,
    incoming_norm_upper: Rat,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct CausalContactPropagationCotangent {
    pub incoming_internal: Vec<Wave>,
    /// Dense cold projection of the overlap return. This does not prescribe dense native storage.
    pub contacts: Vec<Vec<Wave>>,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct CausalContactPropagationEnclosure {
    pub internal: NativeFieldCurrentBall,
    pub joins: Vec<(usize, usize)>,
    pub fractional_bits: u32,
    pub rounding_radius: Rat,
}

fn norm_upper(d: &[Wave]) -> Rat {
    d.iter().map(|v| v.real.abs() + v.imaginary.abs()).sum()
}

fn ordered_joins(
    births: &[NativeOperativeContactBirth],
    contacts: &[Vec<Wave>],
    internal: &[Wave],
) -> Result<Vec<(usize, usize)>, Error> {
    if births.len() != contacts.len()
        || internal.len() != contacts.len()
        || contacts.first().is_some_and(|d| d.is_empty())
        || contacts.iter().any(|d| d.len() != contacts[0].len())
    {
        return Err(Error::ShapeMismatch);
    }
    let mut received: BTreeMap<usize, usize> = BTreeMap::new();
    let mut joins = Vec::new();
    for (after, birth) in births.iter().enumerate() {
        if birth.source >= birth.receiving
            || after
                .checked_sub(1)
                .is_some_and(|i| births[i].receiving >= birth.receiving)
        {
            return Err(Error::ShapeMismatch);
        }
        if let Some(&before) = received.get(&birth.source) {
            joins.push((before, after));
        }
        received.insert(birth.receiving, after);
    }
    Ok(joins)
}

fn family_radius(
    contacts: &[Vec<Wave>],
    joins: impl Iterator<Item = (usize, usize)>,
    incoming_norm_upper: &Rat,
    contact_radius: &Rat,
    incoming_radius: &Rat,
) -> Result<Rat, Error> {
    if contact_radius.is_negative() || incoming_radius.is_negative() {
        return Err(Error::ShapeMismatch);
    }
    let overlap_errors = joins
        .map(|(before, after)| {
            (norm_upper(&contacts[before]) + norm_upper(&contacts[after])) * contact_radius
                + contact_radius * contact_radius
        })
        .sum::<Rat>();
    Ok(incoming_radius + (Rat::one() + Rat::one()) * overlap_errors * incoming_norm_upper)
}

impl CausalContactPropagation {
    /// If contact e ends at the actual source of f, their connection is g=d_e† d_f.
    /// In increasing receiving chronology, apply S_g diag(1,-1) to (b_e,b_f).
    /// The two factors are reflections, so their composition preserves the complete pair norm.
    /// An orphan source has no inferred join; zero overlap gives the identity passage.
    pub fn at(
        births: &[NativeOperativeContactBirth],
        contacts: Vec<Vec<Wave>>,
        internal: &[Wave],
    ) -> Result<Self, Error> {
        let mut joins = Vec::new();
        let mut current = internal.to_vec();
        for (before, after) in ordered_joins(births, &contacts, internal)? {
            let overlap = dot(&contacts[before], &contacts[after]);
            let reflection = PairedJunctionLinearization::at(
                vec![vec![overlap]],
                &[current[before].clone()],
                &[Wave::zero().subtract(&current[after])],
            )?;
            current[before] = reflection.outgoing()[0].clone();
            current[after] = reflection.internal()[0].clone();
            joins.push(ContactJoin {
                before,
                after,
                reflection,
            });
        }
        let incoming_norm_upper = norm_upper(internal);
        Ok(Self {
            contacts,
            joins,
            internal: current,
            incoming_norm_upper,
        })
    }

    pub fn internal(&self) -> &[Wave] {
        &self.internal
    }

    pub fn joins(&self) -> impl Iterator<Item = (usize, usize)> + '_ {
        self.joins.iter().map(|join| (join.before, join.after))
    }

    /// Evaluate the same unitary word at a declared dyadic grain, enclosing every omitted
    /// component. No enormous common denominator or point seal is required. This returns a
    /// forward enclosure; it does not advertise the derivative of quantization as a point map.
    pub fn at_enclosed(
        births: &[NativeOperativeContactBirth],
        contacts: &[Vec<Wave>],
        contact_radius: &Rat,
        internal: &NativeFieldCurrentBall,
        grain: u32,
    ) -> Result<CausalContactPropagationEnclosure, Error> {
        let joins = ordered_joins(births, contacts, &internal.center)?;
        let radius = family_radius(
            contacts,
            joins.iter().copied(),
            &norm_upper(&internal.center),
            contact_radius,
            &internal.radius,
        )?;
        let scale = num_bigint::BigInt::one() << grain;
        let mut omitted = num_bigint::BigInt::zero();
        let mut project = |value: &Rat| {
            let integer = (value.numer() * &scale) / value.denom();
            let projected = Rat::new(integer, scale.clone());
            if projected != *value {
                omitted += 1;
            }
            projected
        };
        let mut current = internal.center.clone();
        for &(before, after) in &joins {
            let overlap = dot(&contacts[before], &contacts[after]);
            let reflection = PairedJunctionLinearization::at(
                vec![vec![overlap]],
                &[current[before].clone()],
                &[Wave::zero().subtract(&current[after])],
            )?;
            for (at, value) in [
                (before, &reflection.outgoing()[0]),
                (after, &reflection.internal()[0]),
            ] {
                current[at] = Wave::new(project(&value.real), project(&value.imaginary));
            }
        }
        let rounding_radius = Rat::new(omitted, scale);
        Ok(CausalContactPropagationEnclosure {
            internal: NativeFieldCurrentBall {
                center: current,
                radius: radius + &rounding_radius,
            },
            joins,
            fractional_bits: grain,
            rounding_radius,
        })
    }

    /// Enclose the full input ball and Frobenius contact ball. For one join,
    /// ||U_g-U_h|| <= 2|g-h|. Telescope the unitary word; current uncertainty is not amplified.
    /// The supplied radii describe a possibly larger family than its complete causal preimage.
    pub fn enclosed_internal(
        &self,
        contact_radius: &Rat,
        incoming_radius: &Rat,
    ) -> Result<NativeFieldCurrentBall, Error> {
        Ok(NativeFieldCurrentBall {
            center: self.internal.clone(),
            radius: family_radius(
                &self.contacts,
                self.joins(),
                &self.incoming_norm_upper,
                contact_radius,
                incoming_radius,
            )?,
        })
    }

    /// Includes both terms of δ(d_e†d_f); changing morphology is not held fixed silently.
    pub fn pushforward(
        &self,
        internal: &[Wave],
        contacts: &[Vec<Wave>],
    ) -> Result<Vec<Wave>, Error> {
        if internal.len() != self.contacts.len()
            || contacts.len() != self.contacts.len()
            || contacts
                .iter()
                .zip(&self.contacts)
                .any(|(a, b)| a.len() != b.len())
        {
            return Err(Error::ShapeMismatch);
        }
        let mut current = internal.to_vec();
        for join in &self.joins {
            let (e, f) = (join.before, join.after);
            let overlap =
                dot(&contacts[e], &self.contacts[f]).add(&dot(&self.contacts[e], &contacts[f]));
            let tangent = join.reflection.pushforward(
                &[current[e].clone()],
                &[Wave::zero().subtract(&current[f])],
                &[vec![overlap]],
            )?;
            current[e] = tangent.outgoing[0].clone();
            current[f] = tangent.internal[0].clone();
        }
        Ok(current)
    }

    /// Reverse the actual forward word. Shared contacts accumulate all incident overlap returns.
    pub fn pullback(&self, covector: &[Wave]) -> Result<CausalContactPropagationCotangent, Error> {
        if covector.len() != self.contacts.len() {
            return Err(Error::ShapeMismatch);
        }
        let mut current = covector.to_vec();
        let mut contacts = self
            .contacts
            .iter()
            .map(|d| vec![Wave::zero(); d.len()])
            .collect::<Vec<_>>();
        for join in self.joins.iter().rev() {
            let (e, f) = (join.before, join.after);
            let returned = join
                .reflection
                .pullback(&[current[e].clone()], &[current[f].clone()])?;
            let overlap = &returned.contacts.contact(0)?[0];
            for j in 0..contacts[e].len() {
                contacts[e][j] =
                    contacts[e][j].add(&self.contacts[f][j].multiply(&overlap.conjugate()));
                contacts[f][j] = contacts[f][j].add(&self.contacts[e][j].multiply(overlap));
            }
            current[e] = returned.source[0].clone();
            current[f] = Wave::zero().subtract(&returned.incoming_internal[0]);
        }
        Ok(CausalContactPropagationCotangent {
            incoming_internal: current,
            contacts,
        })
    }
}

#[cfg(test)]
mod tests;
