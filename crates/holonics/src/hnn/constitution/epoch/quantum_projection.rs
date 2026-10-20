//! Finite alternatives on the existing receiving lattice, never a new solve or prior.
//! The normal owner checks both fall inequalities. The stage owner must additionally
//! replay its complete fresh-ray, joint, tube, storage and budget certification.
use super::*;

#[derive(Clone, Debug)]
pub(super) struct QuantumProjection {
    pub(super) row: usize,
    pub(super) column: usize,
    pub(super) sign: i8,
}

impl QuantumProjection {
    pub(super) fn represent(
        &self,
        law: &EpochLaw,
        flow: &EpochFlow,
        news: &EpochArray,
        canonical: &EpochArray,
    ) -> Result<EpochArray, HnnError> {
        if law.source_refinement
            || law.symmetry.is_some()
            || !canonical.is_zero()
            || self.row >= law.map.rows
            || self.column >= law.map.columns
            || !flow.support.contains(&self.column)
            || !matches!(self.sign, -1 | 1)
        {
            return Err(refused(
                "a quantum alternative keeps an unpaired reached receiving lattice after wholly-zero projection",
            ));
        }
        let index = self.row * law.map.columns + self.column;
        if news.values[index].signum() != BigInt::from(self.sign) {
            return Err(refused(
                "a quantum alternative follows its exact carried-news sign",
            ));
        }
        let mut values = vec![BigInt::zero(); law.map.values.len()];
        values[index] = BigInt::from(self.sign);
        EpochArray::new(law.map.rows, law.map.columns, law.map_lattice, values)
    }
}

/// Native canonical deposit provides Nstar and dynamic S; no second normal arithmetic.
pub(super) fn alternatives(
    law: &EpochLaw,
    flow: &EpochFlow,
    gamma: &EpochArray,
) -> Result<(Option<&'static str>, Vec<QuantumProjection>), HnnError> {
    if law.source_refinement {
        return Ok((
            Some("source refinement is outside receiving projection"),
            vec![],
        ));
    }
    if law.symmetry.is_some() {
        return Ok((
            Some("paired symmetry needs its own declared quantum orbit"),
            vec![],
        ));
    }
    if !gamma.scalar_ratio()?.is_positive() {
        return Ok((Some("no positive certified fresh gain"), vec![]));
    }
    let canonical = law.deposit(flow, gamma)?;
    if !canonical.step.is_zero() {
        return Ok((Some("canonical receiving projection is nonzero"), vec![]));
    }
    let mut options = Vec::new();
    for row in 0..law.map.rows {
        for column in 0..law.map.columns {
            let value = &canonical.successor.news.values[row * law.map.columns + column];
            if flow.support.contains(&column) && !value.is_zero() {
                options.push(QuantumProjection {
                    row,
                    column,
                    sign: if value.is_positive() { 1 } else { -1 },
                });
            }
        }
    }
    Ok((None, options))
}

/// Only fixed-alternative physical nonadmissibility may select the independently
/// certified zero successor. Structural, budget, storage and execution errors stay fatal.
pub(super) fn optional_refusal(failure: &EpochStageFailure, receiver: usize) -> bool {
    let e = &failure.evidence;
    if e.seal_formed || e.finite_probe_executed {
        return false;
    }
    let own = Some(Locus::ReceivingMap(receiver));
    let map = Some(Family::Map);
    let participants = !e.participating_families.is_empty()
        && e.participating_families
            .iter()
            .all(|p| *p == (Locus::ReceivingMap(receiver), Family::Map));
    match (&failure.error, e.condition) {
        (
            HnnError::Unadmitted {
                reason: "a moving actual epoch ray must descend its contemporary comparison",
            },
            EpochStageCondition::ActualRayAlignment,
        ) => e.phase == "actual_ray" && e.locus == own && e.family == map,
        (
            HnnError::Unadmitted {
                reason: "the actual epoch ray violates its own curvature bound",
            },
            EpochStageCondition::ActualRayCurvature,
        ) => e.phase == "actual_certificate" && e.locus == own && e.family == map,
        (
            HnnError::Unadmitted {
                reason: "the actual epoch rays violate the joint triangle bound",
            },
            EpochStageCondition::JointTriangle,
        ) => {
            e.phase == "actual_certificate"
                && e.locus.is_none()
                && e.family.is_none()
                && participants
        }
        (
            HnnError::Unadmitted {
                reason: "the actual epoch rays leave an executed pump tube",
            },
            EpochStageCondition::PumpTube,
        ) => {
            e.phase == "actual_certificate"
                && matches!(e.locus, Some(Locus::Resonator(_)))
                && e.family.is_none()
                && participants
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn array(rows: usize, columns: usize, exponent: u32, values: &[i64]) -> EpochArray {
        EpochArray::new(
            rows,
            columns,
            exponent,
            values.iter().copied().map(BigInt::from).collect(),
        )
        .unwrap()
    }
    fn fixture(news: i64) -> (EpochLaw, EpochFlow, EpochArray) {
        let mut law = EpochLaw::founded(1, 1, 2, 0).unwrap();
        law.gram = array(1, 1, 0, &[2]);
        law.news = array(1, 1, 3, &[news - 1]);
        let flow = EpochFlow {
            gram: array(1, 1, 0, &[1]),
            covector: array(1, 1, 3, &[1]),
            support: vec![0],
            partitions: vec![],
            cells: 1,
            partition_cells: 1,
            records: 1,
            partition_exponent: partition_exponent(2, 1, 0).unwrap(),
            receiver_grain: 2,
            epoch: 0,
        };
        (law, flow, array(1, 1, 0, &[1]))
    }
    #[test]
    fn outward_quantum_meets_both_native_normal_guards_and_retains_first_law() {
        let (law, flow, gamma) = fixture(7);
        let canonical = law.deposit(&flow, &gamma).unwrap();
        assert!(canonical.step.is_zero());
        assert_eq!(
            canonical.step.exponent, 0,
            "zero normalizes independently of the declared map lattice"
        );
        assert_eq!(law.map_lattice, 2);
        let (skip, options) = alternatives(&law, &flow, &gamma).unwrap();
        assert_eq!(skip, None);
        assert_eq!(options.len(), 1);
        let moved = law.deposit_quantum(&flow, &gamma, &options[0]).unwrap();
        assert_eq!(moved.step, array(1, 1, 2, &[1]));
        assert_eq!(
            moved.fall.scalar_ratio().unwrap(),
            Rat::new(1.into(), 8.into())
        );
        assert_eq!(moved.successor.gram, canonical.successor.gram);
        assert_eq!(
            moved
                .successor
                .map
                .multiply(&moved.successor.gram)
                .unwrap()
                .add(&moved.successor.news)
                .unwrap(),
            law.map
                .multiply(&canonical.successor.gram)
                .unwrap()
                .add(&canonical.successor.news)
                .unwrap()
        );
        assert_eq!(law.crossings, 0);
        assert_eq!(moved.successor.crossings, 1);
    }
    #[test]
    fn positive_fall_alone_does_not_weaken_unit_lower_guard() {
        let (law, flow, gamma) = fixture(6);
        let (_, options) = alternatives(&law, &flow, &gamma).unwrap();
        assert_eq!(options.len(), 1);
        assert!(matches!(
            law.deposit_quantum(&flow, &gamma, &options[0]),
            Err(HnnError::EpochStepNonDescending { .. })
        ));
    }
    #[test]
    fn support_zero_gain_nonzero_canonical_and_source_are_not_extended() {
        let (mut law, mut flow, gamma) = fixture(7);
        flow.support.clear();
        assert!(alternatives(&law, &flow, &gamma).unwrap().1.is_empty());
        flow.support.push(0);
        assert!(
            alternatives(&law, &flow, &array(1, 1, 0, &[0]))
                .unwrap()
                .0
                .is_some()
        );
        law.news = array(1, 1, 0, &[4]);
        assert!(alternatives(&law, &flow, &gamma).unwrap().0.is_some());
        law.source_refinement = true;
        assert!(alternatives(&law, &flow, &gamma).unwrap().0.is_some());
    }
    #[test]
    fn odd_phase_divisor_is_consumed_by_unchanged_normal_guard() {
        let (mut law, mut flow, gamma) = fixture(7);
        law.map = array(2, 1, 0, &[0, 0]);
        law.spectral = EpochSpectral::founded_zero(2, 1);
        law.news =
            EpochArray::with_row_divisors(2, 1, 3, vec![0.into(), 19.into()], vec![1, 3]).unwrap();
        flow.covector =
            EpochArray::with_row_divisors(2, 1, 3, vec![0.into(), 3.into()], vec![1, 3]).unwrap();
        let (_, options) = alternatives(&law, &flow, &gamma).unwrap();
        assert_eq!(options.len(), 1);
        assert_eq!(options[0].row, 1);
        let moved = law.deposit_quantum(&flow, &gamma, &options[0]).unwrap();
        assert_eq!(
            moved.fall.scalar_ratio().unwrap(),
            Rat::new(13.into(), 96.into())
        );
        law.news =
            EpochArray::with_row_divisors(2, 1, 3, vec![0.into(), 17.into()], vec![1, 3]).unwrap();
        assert!(matches!(
            law.deposit_quantum(&flow, &gamma, &options[0]),
            Err(HnnError::EpochStepNonDescending { .. })
        ));
    }

    #[test]
    fn large_unreached_old_news_is_never_an_option() {
        let (mut law, mut flow, gamma) = fixture(7);
        law.map = array(1, 2, 0, &[0, 0]);
        law.spectral = EpochSpectral::founded_zero(1, 2);
        law.news = array(1, 2, 3, &[-1, 800]);
        law.gram = array(2, 2, 0, &[2, 0, 0, 2]);
        flow.gram = array(2, 2, 0, &[1, 0, 0, 0]);
        flow.covector = array(1, 2, 3, &[1, 0]);
        assert_eq!(flow.support, vec![0]);
        let (skip, options) = alternatives(&law, &flow, &gamma).unwrap();
        assert_eq!(skip, None);
        assert!(options.is_empty());
    }

    #[test]
    fn options_are_row_major_and_paired_families_are_skipped() {
        let law = EpochLaw::founded(2, 2, 1, 1).unwrap();
        let mut law = EpochLaw {
            news: array(2, 2, 3, &[6, 6, 6, 6]),
            ..law
        };
        let flow = EpochFlow {
            gram: array(2, 2, 0, &[1, 0, 0, 1]),
            covector: array(2, 2, 3, &[1, 1, 1, 1]),
            support: vec![1, 0],
            partitions: vec![],
            cells: 1,
            partition_cells: 1,
            records: 2,
            partition_exponent: partition_exponent(1, 1, 0).unwrap(),
            receiver_grain: 1,
            epoch: 0,
        };
        let gain = array(1, 1, 0, &[1]);
        let (_, options) = alternatives(&law, &flow, &gain).unwrap();
        assert_eq!(
            options
                .iter()
                .map(|p| (p.row, p.column, p.sign))
                .collect::<Vec<_>>(),
            vec![(0, 0, 1), (0, 1, 1), (1, 0, 1), (1, 1, 1)]
        );
        law.symmetry =
            Some(PortSymmetry::from_parts(vec![1, 0], vec![Some(1), Some(0)], &[0]).unwrap());
        let (skip, options) = alternatives(&law, &flow, &gain).unwrap();
        assert_eq!(
            skip,
            Some("paired symmetry needs its own declared quantum orbit")
        );
        assert!(options.is_empty());
    }

    #[test]
    fn optional_refusal_requires_exact_typed_actual_ray_evidence() {
        let error = refused("a moving actual epoch ray must descend its contemporary comparison");
        let mut failure = EpochStageFailure {
            error,
            evidence: EpochStageRefusal::at(
                "actual_ray",
                EpochStageCondition::ActualRayAlignment,
                "alignment > 0",
                Some(Locus::ReceivingMap(2)),
                Some(Family::Map),
            ),
            normal_inputs_prepared: true,
        };
        assert!(optional_refusal(&failure, 2));
        assert!(!optional_refusal(&failure, 1));
        failure.evidence.condition = EpochStageCondition::EpochAdmission;
        assert!(!optional_refusal(&failure, 2));
        failure.evidence.condition = EpochStageCondition::ActualRayAlignment;
        failure.evidence.seal_formed = true;
        assert!(!optional_refusal(&failure, 2));
        failure.evidence.seal_formed = false;
        failure.evidence.finite_probe_executed = true;
        assert!(!optional_refusal(&failure, 2));
        failure.evidence.finite_probe_executed = false;
        for error in [
            HnnError::EpochStepNonDescending { crossing: 0 },
            HnnError::UncertifiedStorage,
            HnnError::ConstitutionBudget {
                bits: 2,
                budget: 1,
                commit: 0,
                loci: vec![],
            },
            refused("a structural native owner failure"),
        ] {
            failure.error = error;
            assert!(!optional_refusal(&failure, 2));
        }
    }
}
