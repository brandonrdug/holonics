//! A single receiving window's radial model at its producing map.
//!
//! This value does not accumulate across changes of the map. Class curvature is in
//! ln(2) units; turn curvature is rational and must not be silently put in those units.
//! Selection proposes a direction only. Publication still needs the ordinary joint
//! receiving-step certificate at the same producing comparison.
use super::*;
use crate::ratio::integer;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceivingWindowRay {
    pub class_alignment: Rat,
    pub class_variance: Rat,
    pub turn_alignment: Rat,
    pub turn_curvature: Rat,
}

impl ReceivingWindowRay {
    /// Read the unmetricized, actual comparison samples at their producing map.
    /// Soft targets require the producer's carried masses, as elsewhere in NormalLaw.
    pub fn read(samples: &[Sample], map: &ExactRatMatrix) -> Option<Self> {
        if map.rows() % 2 != 0
            || samples.iter().any(|sample| {
                sample.feature.len() != map.columns()
                    || sample.covector.len() != map.rows()
                    || sample.weight.is_negative()
            })
        {
            return None;
        }
        let (class_alignment, class_variance) = prequential_terms(samples, map)?;
        let mut turn_alignment = Rat::zero();
        let mut turn_curvature = Rat::zero();
        for sample in samples.iter().filter(|sample| !sample.weight.is_zero()) {
            if sample.weight.is_negative()
                || sample.feature.len() != map.columns()
                || sample.covector.len() != map.rows()
            {
                return None;
            }
            let masses = face_masses(sample)?;
            if masses.len().checked_mul(2)? != map.rows() {
                return None;
            }
            let observed: Vec<Rat> = masses
                .iter()
                .enumerate()
                .map(|(c, p)| p + &sample.covector[2 * c])
                .collect();
            if observed.iter().any(Signed::is_negative)
                || observed.iter().sum::<Rat>() != Rat::one()
            {
                return None;
            }
            let logits = map.apply(&sample.feature).ok()?;
            for (class, q) in observed.iter().enumerate() {
                let delta = &logits[2 * class + 1];
                turn_alignment += &sample.weight * &sample.covector[2 * class + 1] * delta;
                // Im logits are twice turns; Hessian of (q/2)(target-Im/2)^2 is q/4.
                turn_curvature += &sample.weight * q * delta * delta / integer(4);
            }
        }
        Some(Self {
            class_alignment,
            class_variance,
            turn_alignment,
            turn_curvature,
        })
    }

    /// Signed exponent j of the dyadic radial member x=2^j. There is no absolute
    /// prior floor here. An unresolved ln(2) comparison holds; zero curvature holds.
    /// This is the current-window quadratic surrogate, not a finite Face-code theorem.
    pub fn member(&self) -> Result<(i64, Option<PriorHeld>), HnnError> {
        if self.class_variance.is_negative() || self.turn_curvature.is_negative() {
            return Err(HnnError::Unadmitted {
                reason: "a receiving radial window has nonnegative curvature",
            });
        }
        if self.class_variance.is_zero() && self.turn_curvature.is_zero() {
            return Ok((0, Some(PriorHeld::NoCurvature)));
        }
        let ln2 = crate::hnn::executed::ln_two()?;
        let nonpositive = |r: Rat, t: Rat| {
            let low = &r + &t * &ln2.lower;
            let high = &r + &t * &ln2.upper;
            match (low.is_positive(), high.is_positive()) {
                (false, false) => Some(true),
                (true, true) => Some(false),
                _ => None,
            }
        };
        let a = &self.class_alignment + &self.turn_alignment;
        let u = &self.turn_curvature;
        let v = &self.class_variance;
        match nonpositive(&a + u, v.clone()) {
            None => return Ok((0, Some(PriorHeld::Undecided))),
            Some(true) => return Ok((-1, None)),
            Some(false) => {}
        }
        // Newton point (V+a)/V belongs to [3x/4,3x/2].
        let below = |x: &Rat| {
            nonpositive(
                integer(2) * (&a + u) - integer(3) * x * u,
                integer(2) * v - integer(3) * x * v,
            )
        };
        let above = |x: &Rat| {
            nonpositive(
                integer(3) * x * u - integer(4) * (&a + u),
                integer(3) * x * v - integer(4) * v,
            )
        };
        let mut x = Rat::one();
        let mut j = 0i64;
        match below(&x) {
            None => return Ok((0, Some(PriorHeld::Undecided))),
            Some(false) => loop {
                j = j.checked_add(1).ok_or(HnnError::CountOverflow)?;
                x *= integer(2);
                match below(&x) {
                    None => return Ok((0, Some(PriorHeld::Undecided))),
                    Some(true) => return Ok((j, None)),
                    Some(false) => {}
                }
            },
            Some(true) => {}
        }
        loop {
            match above(&x) {
                None => return Ok((0, Some(PriorHeld::Undecided))),
                Some(true) => return Ok((j, None)),
                Some(false) => {
                    j = j.checked_sub(1).ok_or(HnnError::CountOverflow)?;
                    x /= integer(2);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::integer;
    fn half() -> Rat {
        Rat::new(1.into(), 2.into())
    }
    #[test]
    fn receiving_window_ray_includes_turns_in_the_same_radial_proposal() {
        let map = rows_matrix(&[
            vec![integer(1)],
            vec![integer(0)],
            vec![integer(-1)],
            vec![integer(4)],
        ]);
        let sample = Sample {
            weight: Rat::one(),
            feature: vec![Rat::one()],
            covector: vec![-half(), integer(0), half(), integer(2)],
            masses: Some(vec![half(), half()]),
        };
        let ray = ReceivingWindowRay::read(&[sample], &map).unwrap();
        assert_eq!(ray.class_alignment, integer(-1));
        assert_eq!(ray.class_variance, integer(1));
        assert_eq!(ray.turn_alignment, integer(8));
        assert_eq!(ray.turn_curvature, integer(4));
        assert_eq!(ray.member().unwrap(), (1, None));
        let class_only = ReceivingWindowRay {
            turn_alignment: Rat::zero(),
            turn_curvature: Rat::zero(),
            ..ray
        };
        assert_eq!(class_only.member().unwrap(), (-1, None));
    }
    #[test]
    fn receiving_window_ray_has_no_unsigned_floor_or_historical_input() {
        let ray = ReceivingWindowRay {
            class_alignment: Rat::zero(),
            class_variance: Rat::zero(),
            turn_alignment: integer(15),
            turn_curvature: Rat::one(),
        };
        assert_eq!(ray.member().unwrap(), (4, None));
        let zero = ReceivingWindowRay {
            class_alignment: Rat::zero(),
            class_variance: Rat::zero(),
            turn_alignment: Rat::zero(),
            turn_curvature: Rat::zero(),
        };
        assert_eq!(zero.member().unwrap(), (0, Some(PriorHeld::NoCurvature)));
    }
}

fn integral_rows(rows: &[Vec<Rat>]) -> IntegralMatrix {
    let m = rows.len();
    let n = rows.first().map_or(0, Vec::len);
    let terms: Vec<(Rat, Chart, Chart)> = rows
        .iter()
        .enumerate()
        .map(|(i, row)| {
            let mut basis = vec![Rat::zero(); m];
            basis[i] = Rat::one();
            (Rat::one(), integral(&basis), integral(row))
        })
        .collect();
    outer_integral(
        m,
        n,
        &terms.iter().map(|(w, l, r)| (w, l, r)).collect::<Vec<_>>(),
    )
}

impl NormalLaw {
    /// One current-window proposal, evaluated on W_t. The candidate ridge is a metric;
    /// radial and ordinary forces form ONE direction certified later on that same window.
    /// No historical scalar is transported across an ordinary map update.
    pub(super) fn prepare_receiving_window(
        &self,
        samples: &[Sample],
        metric_samples: &[Sample],
        rule: &ChartRule,
        at: &mut BudgetedCarry,
    ) -> Result<Option<PreparedStep>, HnnError> {
        let Some(_) = self.receiving_prior else {
            return self.prepare(metric_samples, rule, at);
        };
        let ray = ReceivingWindowRay::read(samples, self.map());
        let (requested, held) = match ray {
            Some(ray) => ray.member()?,
            None => (0, Some(PriorHeld::Unread)),
        };
        // Internal chart coordinates retain the admitted unit-ridge margin. Operand charts
        // supply a physical subunit founding scale; no unsafe signed chart is fabricated.
        let k = self.chart.scale;
        let j = requested.min(i64::from(k));
        let held = if requested > i64::from(k) {
            Some(PriorHeld::Floor)
        } else {
            held
        };
        let to = u32::try_from(i64::from(k) - j).map_err(|_| HnnError::CountOverflow)?;
        let factor = if j >= 0 {
            Rat::from_integer(BigInt::one() << j as usize)
        } else {
            Rat::new(BigInt::one(), BigInt::one() << j.unsigned_abs() as usize)
        };
        let mut candidate = self.clone();
        let mut movement = PriorMove {
            from: k,
            to: k,
            held,
            certificate: None,
        };
        let mut factor = factor;
        if to != k {
            let ridge_delta = Rat::from_integer(BigInt::one() << to as usize)
                - Rat::from_integer(BigInt::one() << k as usize);
            for (i, row) in candidate.gram.iter_mut().enumerate() {
                row[i] += &ridge_delta;
            }
            match self.chart.moved(&candidate.gram, to, rule) {
                Ok((chart, _)) => {
                    movement.to = to;
                    movement.certificate = Some(chart.certificate().clone());
                    candidate.chart = chart;
                }
                Err(_) => {
                    candidate = self.clone();
                    factor = Rat::one();
                    movement.held = Some(PriorHeld::Chart);
                }
            }
        }
        let Some(mut prepared) = candidate.prepare(metric_samples, rule, at)? else {
            return Ok(None);
        };
        let radial = rate_matrix(&(&factor - Rat::one()), self.map())?;
        let mut rows = prepared.unit.to_rows();
        for (i, row) in rows.iter_mut().enumerate() {
            for (j, x) in row.iter_mut().enumerate() {
                *x += radial.get(i, j)?;
            }
        }
        prepared.unit = integral_rows(&rows);
        prepared.unit_norms = prepared.unit.schur_norms();
        // Receiving prepare_at recomputes full Fisher alignment/curvature on this combined
        // direction, including every cross effect. These generic values cover callers without
        // a recognized class metric; the same actual unmetricized samples are used.
        prepared.alignment = Rat::zero();
        prepared.moves = Rat::zero();
        for sample in samples {
            let moved = rows_matrix(&rows).apply(&sample.feature)?;
            prepared.alignment += &sample.weight
                * sample
                    .covector
                    .iter()
                    .zip(&moved)
                    .map(|(g, d)| g * d)
                    .sum::<Rat>();
            prepared.moves += sample.weight.abs() * moved.iter().map(|d| d * d).sum::<Rat>();
        }
        let ridge_delta = Rat::from_integer(BigInt::one() << movement.to as usize)
            - Rat::from_integer(BigInt::one() << movement.from as usize);
        let ridge_balance = rate_matrix(&ridge_delta, self.map())?;
        prepared.radial = Some(RadialPriorProposal {
            factor,
            direction: radial,
            movement,
            ridge_balance,
        });
        Ok(Some(prepared))
    }
}

#[cfg(test)]
mod joint_tests {
    use super::*;
    #[test]
    fn receiving_window_joint_direction_ignores_old_ray_and_reports_radial_balance() {
        let map = rows_matrix(&[
            vec![integer(1)],
            vec![integer(0)],
            vec![integer(-1)],
            vec![integer(0)],
        ]);
        let law = NormalLaw::with_receiving_prior(map.clone(), 2);
        let sample = Sample {
            weight: Rat::one(),
            feature: vec![Rat::one()],
            covector: vec![
                -Rat::new(1.into(), 2.into()),
                Rat::zero(),
                Rat::new(1.into(), 2.into()),
                Rat::zero(),
            ],
            masses: Some(vec![Rat::new(1.into(), 2.into()); 2]),
        };
        let samples = vec![sample];
        let rule = ChartRule::new(Lattice::new(20), 16);
        let mut carry = BudgetedCarry::new(Lattice::new(20), 1);
        let prepared = law
            .prepare_receiving_window(&samples, &samples, &rule, &mut carry)
            .unwrap()
            .unwrap();
        assert_eq!(
            prepared.radial.as_ref().unwrap().factor,
            Rat::new(1.into(), 2.into())
        );
        let direction = rows_matrix(&prepared.unit.to_rows());
        let eta = Rat::new(1.into(), 2.into());
        let (after, reading) = prepared.stepped(&eta, &mut carry).unwrap();
        let radial = reading.radial.unwrap();
        assert_eq!(
            radial.displacement,
            rate_matrix(&Rat::new((-1).into(), 4.into()), &map).unwrap()
        );
        assert_eq!(
            radial.gram_balance,
            radial
                .displacement
                .multiply(&rows_matrix(&after.gram))
                .unwrap()
        );
        assert_eq!(
            radial.ridge_balance,
            rate_matrix(&integer(4), &map).unwrap()
        );
        assert_eq!(reading.prior.unwrap().to, 3);
        assert_eq!(after.receiving_prior(), Some(2));
        // The actual map plus its carry equals old map + eta times the full direction
        // up to the separately released carry, whose exact accounting is owned by BudgetedCarry.
        for row in 0..map.rows() {
            let expected = map.get(row, 0).unwrap() + &eta * direction.get(row, 0).unwrap();
            let actual = after.map.get(row, 0).unwrap() + after.map_carry.at(row);
            let released: Rat = carry
                .released()
                .into_iter()
                .filter(|(carrier, index, _)| *carrier == Carrier::Map && *index == row)
                .map(|(_, _, value)| value)
                .sum();
            assert_eq!(actual + released, expected);
        }
    }
}
