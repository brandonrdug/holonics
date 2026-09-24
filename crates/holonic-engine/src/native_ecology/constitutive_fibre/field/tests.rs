use super::*;
use crate::embedding_fiber::ResidentReadout;

fn phase(a: i64, b: i64, d: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(a, b, d).unwrap()
}
fn decoded(values: &ResidentSectionRest) -> Vec<ExactComplexWaveCurrent> {
    values
        .intervals
        .chunks_exact(3)
        .map(|v| phase(v[0].0, v[1].0, v[2].0).current())
        .collect()
}

/// Host/device parity (constitutive-field scattering kernel): every port current and held
/// successor equals the exact junction law and conserves the admittance-weighted energy.
#[test]
#[ignore = "requires CUDA; complete independent port currents and actual held successor"]
fn field_scattering_returns_both_branches_with_weighted_energy() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let seeds = vec![
        NativeJunctionSeed {
            incoming_admittance: 2,
            held_admittance: 5,
            incoming_transport: phase(3, 4, 5),
            initial_held: phase(1, 2, 3),
        },
        NativeJunctionSeed {
            incoming_admittance: 3,
            held_admittance: 1,
            incoming_transport: phase(0, 1, 1),
            initial_held: phase(-2, 1, 4),
        },
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 2,
            incoming_transport: phase(-1, 0, 1),
            initial_held: phase(2, -1, 3),
        },
    ];
    let mut body = NativeConstitutiveField::found(&surface, seeds.clone()).unwrap();
    let incoming = vec![phase(2, -1, 7), phase(3, 2, 5), phase(-1, 4, 3)];
    let step = body
        .advance(&mut NativeFieldOccurrence::entering(incoming.clone()))
        .unwrap();
    for (i, seed) in seeds.iter().enumerate() {
        let a = seed
            .incoming_transport
            .current()
            .multiply(&incoming[i].current());
        let h = seed.initial_held.current();
        let ya = Rat::from_integer(seed.incoming_admittance.into());
        let yh = Rat::from_integer(seed.held_admittance.into());
        let v = a
            .scaled(&ya)
            .add(&h.scaled(&yh))
            .scaled(&(Rat::from_integer(2.into()) / (&ya + &yh)));
        assert_eq!(step.outgoing[i], v.subtract(&a));
        assert_eq!(step.held_successor[i], v.subtract(&h));
        assert_eq!(
            &ya * a.norm_square() + &yh * h.norm_square(),
            &ya * step.outgoing[i].norm_square() + &yh * step.held_successor[i].norm_square()
        );
    }
    assert_eq!(decoded(&body.inspect_held().unwrap()), step.held_successor);
    let source = body.inspect_source(0).unwrap();
    let den = source.intervals[12].0;
    for i in 0..3 {
        assert_eq!(
            phase(
                source.intervals[4 * i].0,
                source.intervals[4 * i + 1].0,
                den
            )
            .current(),
            step.outgoing[i]
        );
        assert_eq!(
            phase(
                source.intervals[4 * i + 2].0,
                source.intervals[4 * i + 3].0,
                den
            )
            .current(),
            step.held_successor[i]
        );
    }
    let again = body
        .advance(&mut NativeFieldOccurrence::entering(incoming))
        .unwrap();
    assert_ne!(again.outgoing, step.outgoing);
    assert_eq!(again.lineage.predecessor_state, Some(0));
    assert_eq!(body.inspect_source(0).unwrap(), source);
}
