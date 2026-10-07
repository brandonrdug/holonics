//! The stored pair contact's element relations in their descriptor chart (Refs #73 #62).
//!
//! `C w` is momentum, `K u` is elastic effort and `D w` is resistive effort. The energy is
//! `(u^T K u + w^T C w)/2`. This chart needs no inverse of C: a singular capacity is a lawful
//! descriptor relation. Positive storage/dissipation and admission of a signed stiffness remain
//! claims of the material's producing consumer, not consequences of this container.
//!
//! The native HNN contact now consumes this library relation. Its cached rows, certified inverse
//! chart and executed transpose are realizations of these forms, rather than second constitutive
//! owners. The existing `HNN/Propagation` transit identities and midpoint reference comparison
//! state the mathematical counterpart; this migration changes their owner, not their equations.

use num_traits::Zero;

use crate::holon::HolonError;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer};

/// The C, K and D element relations of one stored pair contact, at one producing material cut.
/// This is a read of the constitution, not its deposition statistics or a separate learned state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContactConstitution {
    storage: ExactRatMatrix,
    stiffness: ExactRatMatrix,
    dissipation: ExactRatMatrix,
}

impl ContactConstitution {
    /// Admit three symmetric forms on the same contact fibre. No definiteness is assumed.
    pub fn new(
        storage: ExactRatMatrix,
        stiffness: ExactRatMatrix,
        dissipation: ExactRatMatrix,
    ) -> Result<Self, HolonError> {
        let width = storage.rows();
        for form in [&storage, &stiffness, &dissipation] {
            if form.rows() != width || form.columns() != width {
                return Err(HolonError::Shape {
                    what: "stored contact forms on one fibre",
                    expected: width,
                    found: form.rows().max(form.columns()),
                });
            }
            if form != &form.transpose()? {
                return Err(HolonError::NotAdmitted);
            }
        }
        Ok(Self {
            storage,
            stiffness,
            dissipation,
        })
    }

    /// The actual constitutive forms, in their shared port chart.
    pub fn forms(&self) -> (&ExactRatMatrix, &ExactRatMatrix, &ExactRatMatrix) {
        (&self.storage, &self.stiffness, &self.dissipation)
    }

    /// The normalized descriptor-midpoint solve on these same forms.
    pub fn operator(&self, conductance: &Rat, step: &Rat) -> Result<ExactRatMatrix, HolonError> {
        let (c, k, d) = self.forms();
        contact_operator(c, k, d, conductance, step)
    }
}

/// `m = I + (G/(2h))(2C + hD + (h^2/2)K)`, the pair contact's normalized descriptor operator.
/// The native and card realizations share this assembly. Its callers admit positive h/G and
/// certify an inverse (or return its obstruction) in their own declared material/chart scope.
/// No inverse of C and no comparison-decrease certificate is supplied here.
pub fn contact_operator(
    storage: &ExactRatMatrix,
    stiffness: &ExactRatMatrix,
    dissipation: &ExactRatMatrix,
    conductance: &Rat,
    step: &Rat,
) -> Result<ExactRatMatrix, HolonError> {
    if step <= &Rat::zero() {
        return Err(HolonError::NonpositiveStep);
    }
    let gain = conductance / (integer(2) * step);
    Ok(ExactRatMatrix::identity(storage.rows())?.add(
        &storage
            .scaled(&integer(2))
            .add(&dissipation.scaled(step))?
            .add(&stiffness.scaled(&(step * step / integer(2))))?
            .scaled(&gain),
    )?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::One;

    #[test]
    fn incoherent_contact_forms_and_zero_hop_refuse_before_a_solve() {
        let one = ExactRatMatrix::identity(1).unwrap();
        let two = ExactRatMatrix::identity(2).unwrap();
        assert!(matches!(
            ContactConstitution::new(one.clone(), two, one.clone()),
            Err(HolonError::Shape { .. })
        ));
        let nonsymmetric = ExactRatMatrix::shaped(
            2,
            2,
            vec![
                vec![Rat::zero(), Rat::one()],
                vec![Rat::zero(), Rat::zero()],
            ],
        )
        .unwrap();
        assert_eq!(
            ContactConstitution::new(
                nonsymmetric,
                ExactRatMatrix::identity(2).unwrap(),
                ExactRatMatrix::identity(2).unwrap(),
            ),
            Err(HolonError::NotAdmitted),
        );
        let material = ContactConstitution::new(one.clone(), one.clone(), one).unwrap();
        assert_eq!(
            material.operator(&integer(2), &Rat::zero()),
            Err(HolonError::NonpositiveStep)
        );
    }
}
