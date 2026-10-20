//! Transient actual C/K/D parameter rays, read from the complete staged endpoint.
//!
//! A rebase can land old carry without writing a new BudgetedCarry quotient. The before/after
//! factors therefore own the displacement; a quotient is accounting evidence, not its definition.
//! These readers never advance statistics, deposit a second time or publish a constitution.

use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ChannelFactorDisplacement {
    pub(super) contact: usize,
    pub(super) family: usize,
    opening: ExactRatMatrix,
    pub(super) displacement: ExactRatMatrix,
}

pub(super) struct ChannelRayReading {
    pub(super) direction: ExactRatMatrix,
    pub(super) alignment: Rat,
    pub(super) moves: Moves,
}

impl ChannelFactorDisplacement {
    fn between(
        contact: usize,
        family: usize,
        opening: &ExactRatMatrix,
        endpoint: &ExactRatMatrix,
    ) -> Result<Option<Self>, HnnError> {
        if family >= 3
            || (opening.rows(), opening.columns()) != (endpoint.rows(), endpoint.columns())
        {
            return Err(refused(
                "an actual channel ray keeps its declared factor family and shape",
            ));
        }
        if opening == endpoint {
            return Ok(None);
        }
        Ok(Some(Self {
            contact,
            family,
            opening: opening.clone(),
            displacement: endpoint.subtract(opening)?,
        }))
    }

    /// Every changed parameter family, including a change with no fresh request or staged q.
    pub(super) fn read_all(
        opening: &Constitution,
        endpoint: &Constitution,
    ) -> Result<Vec<Self>, HnnError> {
        if opening.contacts.len() != endpoint.contacts.len() {
            return Err(refused(
                "an actual channel ray keeps the original contact topology",
            ));
        }
        let mut rays = Vec::new();
        for (contact, (before, after)) in
            opening.contacts.iter().zip(&endpoint.contacts).enumerate()
        {
            for (family, (a, b)) in [
                (&before.storage, &after.storage),
                (&before.stiffness, &after.stiffness),
                (&before.dissipation, &after.dissipation),
            ]
            .into_iter()
            .enumerate()
            {
                if let Some(ray) = Self::between(contact, family, a, b)? {
                    rays.push(ray);
                }
            }
        }
        Ok(rays)
    }

    pub(super) fn matches_stroke(&self, stroke: &BudgetedCarry) -> bool {
        self.displacement
            .entries()
            .iter()
            .enumerate()
            .all(|(entry, value)| {
                let q = stroke
                    .staged
                    .get(&(Carrier::Factor(self.family), entry))
                    .map(|(_, q)| q.clone())
                    .unwrap_or_else(BigInt::zero);
                *value == Rat::from_integer(q) * stroke.lattice.unit()
            })
            && stroke.staged.keys().all(|(carrier, entry)| {
                *carrier != Carrier::Factor(self.family)
                    || *entry < self.displacement.entries().len()
            })
    }

    /// Read D=P/eta and <G,D> on the original factor. No current statistic is updated or used
    /// as a substitute for the reached parameter covector. The caller must supply its actual
    /// certified eta; an absent or held rate cannot be relabelled as a unit step.
    pub(super) fn fixed_eta(
        &self,
        covector: &FactorGradient,
        eta: &Rat,
        hop: &Rat,
    ) -> Result<ChannelRayReading, HnnError> {
        let (contact, family, gradient) = match covector {
            FactorGradient::Storage { contact, gradient } => (*contact, 0, gradient),
            FactorGradient::Stiffness { contact, gradient } => (*contact, 1, gradient),
            FactorGradient::Dissipation { contact, gradient } => (*contact, 2, gradient),
            _ => {
                return Err(refused(
                    "an actual channel ray needs its original channel covector",
                ));
            }
        };
        if (contact, family) != (self.contact, self.family)
            || (gradient.rows(), gradient.columns())
                != (self.displacement.rows(), self.displacement.columns())
            || !eta.is_positive()
        {
            return Err(refused(
                "an actual channel ray binds its locus, shape, family and positive certified rate",
            ));
        }
        let direction = self.displacement.scaled(&(Rat::one() / eta));
        let alignment = gradient
            .entries()
            .iter()
            .zip(direction.entries())
            .map(|(g, d)| g * d)
            .sum();
        let moves = channel_factor_moves(
            self.family,
            &self.opening,
            schur_flat(direction.entries(), direction.columns()),
            hop,
        );
        Ok(ChannelRayReading {
            direction,
            alignment,
            moves,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn actual_channel_ray_uses_the_applied_noncollinear_endpoint_and_original_covector() {
        let before = ExactRatMatrix::new(vec![vec![rat(1, 1), rat(0, 1)]]).unwrap();
        let after = ExactRatMatrix::new(vec![vec![rat(0, 1), rat(1, 1)]]).unwrap();
        let ray = ChannelFactorDisplacement::between(0, 2, &before, &after)
            .unwrap()
            .unwrap();
        let gradient = FactorGradient::Dissipation {
            contact: 0,
            gradient: ExactRatMatrix::new(vec![vec![rat(-1, 1), rat(5, 2)]]).unwrap(),
        };
        let reading = ray.fixed_eta(&gradient, &rat(1, 2), &rat(1, 1)).unwrap();
        assert_eq!(
            reading.direction.to_rows(),
            vec![vec![rat(-2, 1), rat(2, 1)]]
        );
        assert_eq!(reading.alignment, rat(7, 1));
        // This is an output first-variation bound, never an asserted nonlinear score fall.
        assert!(
            reading
                .moves
                .own(&rat(2, 1), &rat(1, 2))
                .unwrap()
                .is_positive()
        );
        assert_eq!(before.to_rows(), vec![vec![rat(1, 1), rat(0, 1)]]);
        assert_eq!(after.to_rows(), vec![vec![rat(0, 1), rat(1, 1)]]);
    }

    #[test]
    fn actual_channel_ray_rate_reparametrization_preserves_the_same_physical_reading() {
        let before = ExactRatMatrix::new(vec![vec![rat(1, 1), Rat::zero()]]).unwrap();
        let after = ExactRatMatrix::new(vec![vec![Rat::zero(), rat(1, 1)]]).unwrap();
        for family in 0..3 {
            let ray = ChannelFactorDisplacement::between(0, family, &before, &after)
                .unwrap()
                .unwrap();
            let gradient = ExactRatMatrix::new(vec![vec![rat(-1, 1), rat(5, 2)]]).unwrap();
            let covector = match family {
                0 => FactorGradient::Storage {
                    contact: 0,
                    gradient,
                },
                1 => FactorGradient::Stiffness {
                    contact: 0,
                    gradient,
                },
                _ => FactorGradient::Dissipation {
                    contact: 0,
                    gradient,
                },
            };
            let eta = rat(1, 2);
            let other_eta = rat(1, 4);
            let a = ray.fixed_eta(&covector, &eta, &rat(3, 1)).unwrap();
            let b = ray.fixed_eta(&covector, &other_eta, &rat(3, 1)).unwrap();
            assert_eq!(a.direction.scaled(&eta), ray.displacement);
            assert_eq!(b.direction.scaled(&other_eta), ray.displacement);
            assert_eq!(&a.alignment * &eta, &b.alignment * &other_eta);
            // S(D)=8, the end norm product is6, energy2 and eta^2=1/4.
            // Storage weight16; stiffness/dissipation weight4*h^2=36 at hop3.
            assert_eq!(
                &eta * &eta * a.moves.own(&rat(2, 1), &eta).unwrap(),
                rat(if family == 0 { 384 } else { 864 }, 1)
            );
            assert_eq!(
                &eta * &eta * a.moves.own(&rat(2, 1), &eta).unwrap(),
                &other_eta * &other_eta * b.moves.own(&rat(2, 1), &other_eta).unwrap()
            );
        }
    }

    #[test]
    fn actual_channel_ray_reads_parameters_even_when_the_material_gram_agrees() {
        let before = ExactRatMatrix::new(vec![vec![rat(1, 1)]]).unwrap();
        let after = before.scaled(&rat(-1, 1));
        assert_eq!(gram(&before).unwrap(), gram(&after).unwrap());
        let ray = ChannelFactorDisplacement::between(2, 0, &before, &after)
            .unwrap()
            .unwrap();
        assert_eq!(ray.displacement.entries(), &[rat(-2, 1)]);
        let mut stroke = BudgetedCarry::new(Lattice::new(2), 1);
        stroke
            .staged
            .insert((Carrier::Factor(0), 0), (Rat::zero(), BigInt::from(-8)));
        assert!(ray.matches_stroke(&stroke));
        stroke
            .staged
            .insert((Carrier::Factor(0), 1), (Rat::zero(), BigInt::one()));
        assert!(!ray.matches_stroke(&stroke));
    }

    #[test]
    fn actual_channel_ray_refuses_foreign_shapes_roles_and_held_rates() {
        let before = ExactRatMatrix::zero(1, 1).unwrap();
        let after = ExactRatMatrix::new(vec![vec![Rat::one()]]).unwrap();
        assert!(
            ChannelFactorDisplacement::between(0, 0, &before, &ExactRatMatrix::zero(1, 2).unwrap())
                .is_err()
        );
        assert!(ChannelFactorDisplacement::between(0, 3, &before, &after).is_err());
        let ray = ChannelFactorDisplacement::between(0, 0, &before, &after)
            .unwrap()
            .unwrap();
        for covector in [
            FactorGradient::Storage {
                contact: 1,
                gradient: after.clone(),
            },
            FactorGradient::Dissipation {
                contact: 0,
                gradient: after.clone(),
            },
            FactorGradient::Storage {
                contact: 0,
                gradient: ExactRatMatrix::zero(1, 2).unwrap(),
            },
        ] {
            assert!(ray.fixed_eta(&covector, &Rat::one(), &Rat::one()).is_err());
        }
        let covector = FactorGradient::Storage {
            contact: 0,
            gradient: after,
        };
        for eta in [Rat::zero(), rat(-1, 1)] {
            assert!(ray.fixed_eta(&covector, &eta, &Rat::one()).is_err());
        }
    }
}
