use super::*;
use crate::embedding_fiber::ResidentReadout;

fn phase(real: i64, imaginary: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(real, imaginary, 1).unwrap()
}
fn material() -> Vec<NativeJunctionSeed> {
    (0..4)
        .map(|_| NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        })
        .collect()
}
fn input(a: bool, b: bool) -> Vec<NativePhaseCurrent> {
    [!a, a, !b, b]
        .into_iter()
        .map(|v| phase(i64::from(v), 0))
        .collect()
}
fn assert_balanced(values: &[ExactComplexWaveCurrent]) {
    for bank in 0..3 {
        let at = |port: usize| if bank < 2 { 2 * port + bank } else { 8 + port };
        assert_eq!(
            values[at(0)].add(&values[at(1)]),
            values[at(2)].add(&values[at(3)])
        );
    }
}

#[test]
#[ignore = "requires CUDA; metric factorization preserves the exact full current and delayed-source decoder"]
fn balanced_solver_returns_the_same_exact_current_through_rechart_and_shared_source() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut full = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        material(),
        ResidentGrain(72),
    )
    .unwrap();
    let mut balanced = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        material(),
        ResidentGrain(72),
    )
    .unwrap();
    balanced
        .set_junction_solver(NativeFieldJunctionSolver::BalancedPairs)
        .unwrap();
    let mut fs = None;
    let mut bs = None;
    let mut fa = None;
    let mut ba = None;
    for at in 0..5 {
        if at == 3 {
            let gauge = [phase(0, 1), phase(0, -1), phase(-1, 0), phase(0, 1)];
            full.rechart(&gauge).unwrap();
            balanced.rechart(&gauge).unwrap();
        }
        let incoming = input(at % 2 == 0, at % 3 == 0);
        let mut fo = if at == 4 {
            NativeFieldOccurrence::through_anchor(fa.as_ref().unwrap(), incoming.clone())
        } else if let Some(source) = fs.take() {
            NativeFieldOccurrence::through(source, incoming.clone())
        } else {
            NativeFieldOccurrence::entering(incoming.clone())
        };
        let mut bo = if at == 4 {
            NativeFieldOccurrence::through_anchor(ba.as_ref().unwrap(), incoming)
        } else if let Some(source) = bs.take() {
            NativeFieldOccurrence::through(source, incoming)
        } else {
            NativeFieldOccurrence::entering(incoming)
        };
        let fstep = full.advance_resident(&mut fo).unwrap();
        let bstep = balanced.advance_resident(&mut bo).unwrap();
        assert_eq!(fstep.lineage, bstep.lineage);
        if at == 0 {
            fa = Some(full.retain_source(&fstep.source).unwrap());
            ba = Some(balanced.retain_source(&bstep.source).unwrap());
        }
        fs = Some(fstep.source);
        bs = Some(bstep.source);
        let reading = balanced.inspect_junction_enclosure(at).unwrap().unwrap();
        assert_eq!(reading.outgoing.center.len(), 12);
        assert_balanced(&reading.potential.center);
        assert_balanced(&reading.outgoing.center);
        assert_balanced(&reading.held_current.center);
    }
    assert_eq!(
        full.inspect_relation().unwrap(),
        balanced.inspect_relation().unwrap()
    );
    assert_eq!(
        full.inspect_held().unwrap(),
        balanced.inspect_held().unwrap()
    );
    assert_eq!(
        full.inspect_junction_covariance().unwrap(),
        balanced.inspect_junction_covariance().unwrap()
    );
    for at in 0..5 {
        assert_eq!(
            full.inspect_source(at).unwrap(),
            balanced.inspect_source(at).unwrap()
        );
    }
    assert_eq!(
        full.inspect_exact_junction(4).unwrap(),
        balanced.inspect_exact_junction(4).unwrap()
    );
    assert_eq!(
        full.inspect_internal_currents().unwrap(),
        balanced.inspect_internal_currents().unwrap()
    );
}

#[test]
#[ignore = "requires CUDA; complex unbalanced covariance uses the unchanged full factorization"]
fn balanced_policy_falls_back_without_changing_the_full_report() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut full = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        material(),
        ResidentGrain(72),
    )
    .unwrap();
    let mut balanced = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        material(),
        ResidentGrain(72),
    )
    .unwrap();
    balanced
        .set_junction_solver(NativeFieldJunctionSolver::BalancedPairs)
        .unwrap();
    let incoming = vec![phase(1, 1), phase(0, 0), phase(2, -1), phase(0, 1)];
    let first_full = full
        .advance_resident(&mut NativeFieldOccurrence::entering(incoming.clone()))
        .unwrap();
    let first_balanced = balanced
        .advance_resident(&mut NativeFieldOccurrence::entering(incoming))
        .unwrap();
    let next = vec![phase(1, -1), phase(1, 0), phase(-1, 1), phase(2, 0)];
    full.advance_resident(&mut NativeFieldOccurrence::through(
        first_full.source,
        next.clone(),
    ))
    .unwrap();
    balanced
        .advance_resident(&mut NativeFieldOccurrence::through(
            first_balanced.source,
            next,
        ))
        .unwrap();
    assert_eq!(
        full.inspect_junction(0).unwrap(),
        balanced.inspect_junction(0).unwrap()
    );
    assert_eq!(
        full.inspect_junction(1).unwrap(),
        balanced.inspect_junction(1).unwrap()
    );
    assert_eq!(
        full.inspect_junction_covariance().unwrap(),
        balanced.inspect_junction_covariance().unwrap()
    );
}

#[test]
#[ignore = "requires CUDA; one balanced factor carries a nonzero imaginary right-hand side"]
fn balanced_solver_carries_both_complex_components() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut real = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        material(),
        ResidentGrain(72),
    )
    .unwrap();
    let mut imaginary = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        material(),
        ResidentGrain(72),
    )
    .unwrap();
    real.set_junction_solver(NativeFieldJunctionSolver::BalancedPairs)
        .unwrap();
    imaginary
        .set_junction_solver(NativeFieldJunctionSolver::BalancedPairs)
        .unwrap();
    let mut rs = None;
    let mut is = None;
    for at in 0..4 {
        let values = input(at % 2 == 0, at % 3 == 0);
        let rotated = values
            .iter()
            .map(|value| NativePhaseCurrent::new(0, value.words()[0], 1).unwrap())
            .collect();
        let mut ro = match rs.take() {
            Some(source) => NativeFieldOccurrence::through(source, values),
            None => NativeFieldOccurrence::entering(values),
        };
        let mut io = match is.take() {
            Some(source) => NativeFieldOccurrence::through(source, rotated),
            None => NativeFieldOccurrence::entering(rotated),
        };
        rs = Some(real.advance_resident(&mut ro).unwrap().source);
        is = Some(imaginary.advance_resident(&mut io).unwrap().source);
    }
    assert_eq!(
        real.inspect_junction_covariance().unwrap(),
        imaginary.inspect_junction_covariance().unwrap()
    );
    let r = real.inspect_junction_enclosure(3).unwrap().unwrap();
    let i = imaginary.inspect_junction_enclosure(3).unwrap().unwrap();
    assert!(i
        .outgoing
        .center
        .iter()
        .any(|value| value.imaginary != Rat::from_integer(0.into())));
    for (left, right) in [
        (&r.potential, &i.potential),
        (&r.outgoing, &i.outgoing),
        (&r.held_current, &i.held_current),
        (&r.potential_prefix, &i.potential_prefix),
    ] {
        assert_eq!(left.radius, right.radius);
        for (a, b) in left.center.iter().zip(&right.center) {
            assert_eq!(b.real, -&a.imaginary);
            assert_eq!(b.imaginary, a.real);
        }
    }
}
