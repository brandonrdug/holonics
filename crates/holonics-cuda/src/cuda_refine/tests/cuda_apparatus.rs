use super::super::*;

/// **The law is one law.** The cpu and the card must return the same partition for the same
/// `(classes, keys)`, on material built to make the table collide and to make many cells share
/// a pair — which is where a claim race shows up and where a wrong probe walks off.
///
/// `#[ignore]`d because it requires the mounted card; run with `-- --ignored`.
#[test]
#[ignore = "requires the RTX CUDA device"]
fn the_quotient_is_one_law_on_both_charts() {
    let mut card = CudaRefineExecutor::new().expect("the card mounts");
    // Deterministic material with heavy sharing: many cells per pair, several classes, and keys
    // chosen so distinct pairs land near each other under any probe.
    for cells in [1usize, 2, 31, 32, 33, 1024, 40_000] {
        let classes: Vec<u32> = (0..cells).map(|at| (at % 7) as u32 + 1).collect();
        let keys: Vec<u64> = (0..cells)
            .map(|at| ((at % 11) as u64) << 32 | (at % 5) as u64)
            .collect();
        let cpu = quotient_on_cpu(&classes, &keys);
        let device = card
            .quotient_on_device(&classes, &keys)
            .expect("the card quotients");
        assert_eq!(
            cpu.classes, device.classes,
            "class count at {cells} cells: cpu {} device {}",
            cpu.classes, device.classes
        );
        assert!(
            cpu.same_partition_as(&device),
            "the two charts must induce the same equivalence at {cells} cells"
        );
        assert_eq!(cpu.carrier, QuotientCarrier::Cpu);
        assert_eq!(device.carrier, QuotientCarrier::Device);
    }
}

/// The exact causal-adjoint receipt derives its own finite population and refuses a ragged
/// substitute before any card is mounted.
#[test]
fn causal_adjoint_pulled_incidence_has_no_authored_width() {
    let receipt = CausalAdjointPulledIncidence::found(vec![vec![5, 0], vec![0, 5]])
        .expect("returned covectors found the population");
    assert_eq!(receipt.factors(), 2);
    assert_eq!(receipt.nodes(), 2);
    assert!(matches!(
        CausalAdjointPulledIncidence::found(vec![vec![5], vec![0, 5]]),
        Err(CudaRefineError::CoupledComplexParametronShape)
    ));
}

#[test]
fn the_coupled_limb_chart_derives_only_the_carry_width_the_exact_sum_requires() {
    let receipt = CausalAdjointPulledIncidence::found(vec![vec![1]])
        .expect("one returned covector founds one factor");
    let large = BigInt::one() << 130usize;
    let interaction = CoupledComplexInteraction {
        output_factor: 0,
        left_factor: 0,
        right_factor: 0,
        contribution: ExactComplexWaveCurrent::new(
            Rat::from_integer(large.clone()),
            Rat::from_integer(-large),
        ),
    };
    let chart =
        derive_coupled_limb_chart(&receipt, &[ExactComplexWaveCurrent::one()], &[interaction])
            .expect("the exact multi-limb chart is derived");
    assert_eq!(chart.limb_count, 5, "2^130 plus one needs five u32 limbs");
    assert_eq!(chart.denominator, BigInt::one());
    assert_eq!(chart.mixed_real_limbs.len(), chart.limb_count);
    assert_eq!(chart.mixed_imaginary_limbs.len(), chart.limb_count);
}
