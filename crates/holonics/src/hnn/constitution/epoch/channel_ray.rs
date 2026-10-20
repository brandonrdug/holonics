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

/// A fixed actual D ray together with its original fresh metadata. The wrapped
/// preparation keeps h', energy and covector-scale from the one preparation pass;
/// only alignment and first-variation moves are read on P/eta.
pub(super) struct ActualChannelRayFace {
    contact: usize,
    exponent: i64,
    prepared: FactorPrepared,
}

impl ActualChannelRayFace {
    pub(super) fn contact(&self) -> usize {
        self.contact
    }

    pub(super) fn exponent(&self) -> i64 {
        self.exponent
    }

    pub(super) fn prepared(&self) -> &FactorPrepared {
        &self.prepared
    }
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

    #[cfg(test)]
    pub(super) fn matches_stroke(&self, stroke: &BudgetedCarry) -> bool {
        self.matches_stroke_after_rebase(stroke, None)
    }

    /// P = rebase_delta + q * new_unit, read from the same published predecessor.
    /// The rebase witness does not create a staged q or replace the full endpoint ray.
    pub(super) fn matches_stroke_after_rebase(
        &self, stroke: &BudgetedCarry, rebase: Option<&ExactRatMatrix>,
    ) -> bool {
        if rebase.is_some_and(|delta| (delta.rows(), delta.columns()) !=
            (self.displacement.rows(), self.displacement.columns())) {
            return false;
        }
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
                *value == rebase.map_or_else(Rat::zero, |delta| delta.entries()[entry].clone())
                    + Rat::from_integer(q) * stroke.lattice.unit()
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

    pub(super) fn actual_face(
        &self,
        original: &FactorPrepared,
        request_index: usize,
        request: &FactorStep,
        certified: &StepReading,
        hop: &Rat,
    ) -> Result<ActualChannelRayFace, HnnError> {
        if self.family != 2
            || request.gradient.locus() != Locus::Channel(self.contact)
            || request.gradient.family() != Family::Factor(2)
            || certified.family != Family::Factor(2)
            || certified.step.step <= Rat::zero()
            || original.family != Family::Factor(2)
            || original.index != request_index
        {
            return Err(refused(
                "an actual channel D ray keeps its original request index and positive certified family",
            ));
        }
        let reading = self.fixed_eta(&request.gradient, &certified.step.step, hop)?;
        let mut prepared = original.clone();
        // Preserve the original post-advance h', energy and covector bound. Do
        // not fabricate a scale or call the statistic-advancing preparation.
        prepared.alignment = floor(&reading.alignment);
        prepared.moves = reading.moves;
        Ok(ActualChannelRayFace {
            contact: self.contact,
            exponent: certified.step.exponent,
            prepared,
        })
    }

    /// Exterior operands of a refused actual ray. Q is read independently from the staged
    /// integers, never defined as P-R; this reader neither certifies nor changes a candidate.
    pub(super) fn decomposition_readings(
        &self, covector: &FactorGradient, stroke: &BudgetedCarry,
        rebase: Option<&ExactRatMatrix>, eta: &Rat, hop: &Rat,
    ) -> Result<Vec<EpochStageReading>, HnnError> {
        let actual = self.fixed_eta(covector, eta, hop)?;
        let gradient = match covector {
            FactorGradient::Storage { gradient, .. }
            | FactorGradient::Stiffness { gradient, .. }
            | FactorGradient::Dissipation { gradient, .. } => gradient,
            _ => return Err(refused("an actual channel decomposition needs a channel covector")),
        };
        let rows = self.displacement.rows();
        let columns = self.displacement.columns();
        let rebase = match rebase {
            Some(delta) if (delta.rows(), delta.columns()) == (rows, columns) => delta.clone(),
            Some(_) => return Err(refused("an actual channel decomposition keeps its rebase shape")),
            None => ExactRatMatrix::zero(rows, columns)?,
        };
        let quotient = ExactRatMatrix::shaped(rows, columns, (0..rows).map(|row| {
            (0..columns).map(|column| {
                let entry = row * columns + column;
                let q = stroke.staged.get(&(Carrier::Factor(self.family), entry))
                    .map(|(_, q)| q.clone()).unwrap_or_else(BigInt::zero);
                Rat::from_integer(q) * stroke.lattice.unit()
            }).collect()
        }).collect())?;
        let residual = self.displacement.subtract(&rebase)?.subtract(&quotient)?;
        let pair = |matrix: &ExactRatMatrix| -> Rat {
            gradient.entries().iter().zip(matrix.entries()).map(|(g, p)| g * p).sum()
        };
        let mut readings = Vec::new();
        for (name, matrix) in [
            ("D_covector_G", gradient.clone()),
            ("D_opening_factor", self.opening.clone()),
            ("D_actual_displacement_P", self.displacement.clone()),
            ("D_rebase_displacement_R", rebase.clone()),
            ("D_fresh_applied_displacement_Q", quotient.clone()),
            ("D_actual_direction_P_over_eta", actual.direction),
            ("D_reconstruction_residual_P_minus_R_minus_Q", residual.clone()),
        ] {
            readings.push(EpochStageReading { name, value: EpochStageValue::RationalMatrix(matrix) });
        }
        for (name, value) in [
            ("D_pairing_G_P", pair(&self.displacement)),
            ("D_pairing_G_R", pair(&rebase)),
            ("D_pairing_G_Q", pair(&quotient)),
            ("D_pairing_G_P_over_eta", actual.alignment),
            ("D_pairing_reconstruction_residual", pair(&residual)),
            ("D_covector_squared_norm", pair(gradient)),
            ("D_original_certified_eta", eta.clone()),
        ] {
            readings.push(EpochStageReading { name, value: EpochStageValue::Ratio(value) });
        }
        readings.push(EpochStageReading {
            name: "D_decomposition_matches_staged_quotient",
            value: EpochStageValue::Index(usize::from(self.matches_stroke_after_rebase(stroke, Some(&rebase)))),
        });
        Ok(readings)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn actual_d_decomposition_distinguishes_positive_fresh_alignment_from_carry_cancellation() {
        let before = ExactRatMatrix::new(vec![vec![Rat::one(), Rat::zero()]]).unwrap();
        let endpoint = ExactRatMatrix::new(vec![vec![rat(7, 8), rat(1, 16)]]).unwrap();
        let ray = ChannelFactorDisplacement::between(0, 2, &before, &endpoint).unwrap().unwrap();
        let gradient = FactorGradient::Dissipation {
            contact: 0,
            gradient: ExactRatMatrix::new(vec![vec![rat(1, 3), rat(2, 3)]]).unwrap(),
        };
        let rebase = ExactRatMatrix::new(vec![vec![rat(-3, 16), Rat::zero()]]).unwrap();
        let mut stroke = BudgetedCarry::new(Lattice::new(8), 4);
        for entry in 0..2 {
            stroke.staged.insert((Carrier::Factor(2), entry), (Rat::zero(), BigInt::from(16)));
        }
        let saved = stroke.clone();
        let readings = ray.decomposition_readings(&gradient, &stroke, Some(&rebase), &rat(4, 1), &Rat::one()).unwrap();
        let ratio = |name| readings.iter().find_map(|r| match &r.value {
            EpochStageValue::Ratio(value) if r.name == name => Some(value.clone()), _ => None,
        }).unwrap();
        assert_eq!(ratio("D_pairing_G_R"), rat(-1, 16));
        assert_eq!(ratio("D_pairing_G_Q"), rat(1, 16));
        assert_eq!(ratio("D_pairing_G_P_over_eta"), Rat::zero());
        assert_eq!(ratio("D_covector_squared_norm") / rat(131, 128), rat(640, 1179));
        assert!(readings.iter().any(|r| r.name == "D_reconstruction_residual_P_minus_R_minus_Q"
            && r.value == EpochStageValue::RationalMatrix(ExactRatMatrix::zero(1, 2).unwrap())));
        assert_eq!(stroke, saved);
        stroke.staged.get_mut(&(Carrier::Factor(2), 0)).unwrap().1 += BigInt::one();
        let wrong = ray.decomposition_readings(&gradient, &stroke, Some(&rebase), &rat(4, 1), &Rat::one()).unwrap();
        assert!(wrong.iter().any(|r| r.name == "D_decomposition_matches_staged_quotient"
            && r.value == EpochStageValue::Index(0)));
        assert!(wrong.iter().any(|r| r.name == "D_pairing_reconstruction_residual"
            && r.value == EpochStageValue::Ratio(rat(-1, 768))));
    }

    #[test]
    fn rebased_actual_ray_matches_only_full_rebase_plus_refined_quotient() {
        let before = ExactRatMatrix::new(vec![vec![rat(1, 1), rat(0, 1)]]).unwrap();
        let after = ExactRatMatrix::new(vec![vec![rat(17, 16), rat(1, 32)]]).unwrap();
        let ray = ChannelFactorDisplacement::between(0, 2, &before, &after).unwrap().unwrap();
        let mut stroke = BudgetedCarry::new(Lattice::new(5), 8);
        stroke.staged.insert((Carrier::Factor(2), 1), (Rat::zero(), BigInt::one()));
        let rebase = ExactRatMatrix::new(vec![vec![rat(1, 16), rat(0, 1)]]).unwrap();
        assert!(!ray.matches_stroke(&stroke));
        assert!(ray.matches_stroke_after_rebase(&stroke, Some(&rebase)));
        assert!(!ray.matches_stroke_after_rebase(&stroke, Some(&rebase.scaled(&rat(2, 1)))));
        stroke.staged.insert((Carrier::Factor(2), 2), (Rat::zero(), BigInt::one()));
        assert!(!ray.matches_stroke_after_rebase(&stroke, Some(&rebase)));
        let malformed = ExactRatMatrix::zero(1, 1).unwrap();
        assert!(!ray.matches_stroke_after_rebase(&stroke, Some(&malformed)));
    }

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

    #[test]
    fn actual_d_face_binds_original_request_index_and_rejects_held_rates() {
        let opening = ExactRatMatrix::new(vec![vec![Rat::zero()]]).unwrap();
        let endpoint = ExactRatMatrix::new(vec![vec![Rat::one()]]).unwrap();
        let ray = ChannelFactorDisplacement::between(0, 2, &opening, &endpoint)
            .unwrap()
            .unwrap();
        let request = FactorStep {
            gradient: FactorGradient::Dissipation {
                contact: 0,
                gradient: ExactRatMatrix::new(vec![vec![Rat::one()]]).unwrap(),
            },
            energy: Rat::one(),
            covector: Rat::one(),
        };
        let original = FactorPrepared {
            index: 4,
            family: Family::Factor(2),
            scale: Rat::one(),
            alignment: Rat::one(),
            covector: Rat::one(),
            energy: Rat::one(),
            moves: channel_factor_moves(2, &opening, (Rat::one(), Rat::one()), &Rat::one()),
        };
        let make_reading = |step: Rat| StepReading {
            family: Family::Factor(2),
            step: CertifiedStep {
                exponent: 0,
                step,
                alignment: Rat::one(),
                curvature: Rat::one(),
                covector: Rat::one(),
            },
            gain: Rat::one(),
            moves: Rat::one(),
            bound: Rat::one(),
            readout: Rat::one(),
            amplitude: Rat::one(),
        };
        let positive = make_reading(Rat::one());
        assert!(ray.actual_face(&original, 4, &request, &positive, &Rat::one()).is_ok());
        assert!(ray.actual_face(&original, 5, &request, &positive, &Rat::one()).is_err());
        let mut wrong_original = original.clone();
        wrong_original.index = 5;
        assert!(ray.actual_face(&wrong_original, 4, &request, &positive, &Rat::one()).is_err());
        for held in [Rat::zero(), rat(-1, 1)] {
            let reading = make_reading(held);
            assert!(ray.actual_face(&original, 4, &request, &reading, &Rat::one()).is_err());
        }
    }
}
