use super::*;
use crate::embedding_fiber::ResidentReadout;
use crate::resident_section::SeriesAperture;

fn phase(r: i64, i: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(r, i, 1).unwrap()
}
fn make<'c>(s: &'c ResidentSurface<'c>) -> NativeConstitutiveField<'c> {
    let seed = vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero()
        };
        2
    ];
    let mut f =
        NativeConstitutiveField::found_with_enclosed_junction(s, seed, ResidentGrain(72)).unwrap();
    f.enable_material_transport_source(NativeMaterialTransportSource::OperativeContextual)
        .unwrap();
    f
}
fn populate(f: &mut NativeConstitutiveField<'_>) -> NativeFieldEmission {
    let mut last = None;
    let mut anchor = None;
    for (at, v) in [
        [(1, 1), (0, 1)],
        [(0, 1), (1, 0)],
        [(1, 0), (0, -1)],
        [(0, 0), (1, 1)],
        [(1, 0), (0, 0)],
    ]
    .into_iter()
    .enumerate()
    {
        let incoming = v.into_iter().map(|(r, i)| phase(r, i)).collect();
        let mut event = if at == 2 {
            NativeFieldOccurrence::through_anchor(anchor.as_ref().unwrap(), incoming)
        } else if let Some(s) = last.take() {
            NativeFieldOccurrence::through(s, incoming)
        } else {
            NativeFieldOccurrence::entering(incoming)
        };
        let next = f.advance_resident(&mut event).unwrap();
        if at == 0 {
            anchor = Some(f.retain_source(&next.source).unwrap());
        }
        last = Some(next.source);
    }
    last.unwrap()
}
fn returned<'c>(f: &NativeConstitutiveField<'c>) -> NativeMaterialContactResponse<'c> {
    let r = f
        .normalized_material_return(4, 2, SeriesAperture(32))
        .unwrap()
        .unwrap();
    let q = f
        .pull_back_material_source(&r, NativeMaterialPullbackMetric::RelativeEntropy)
        .unwrap();
    f.material_contact_response(q).unwrap()
}

fn enclosed(actual: &[ExactComplexWaveCurrent], center: &[ExactComplexWaveCurrent], radius: &Rat) {
    let error: Rat = actual
        .iter()
        .zip(center)
        .map(|(a, b)| a.subtract(b).norm_square())
        .sum();
    assert!(
        error <= radius * radius,
        "squared error {error} exceeds radius squared {}",
        radius * radius
    );
}
fn decode(
    s: &ResidentSurface<'_>,
    v: &ResidentSection<'_>,
    g: u32,
) -> Vec<ExactComplexWaveCurrent> {
    let w = wides(&s.detach_section(v, 64).unwrap().intervals).unwrap();
    let scale = BigInt::one() << g;
    w.chunks_exact(2)
        .map(|v| {
            ExactComplexWaveCurrent::new(
                Rat::new(v[0].into(), scale.clone()),
                Rat::new(v[1].into(), scale.clone()),
            )
        })
        .collect()
}

/// Material-contact-response parity: the device paired adjoint (source, internal, potential and
/// contact covectors) contains the exact host `PairedJunctionLinearization::pullback` of the
/// producing map at the same query.
#[test]
#[ignore = "requires CUDA; paired adjoint of the material contact response"]
fn material_contact_response_contains_the_exact_producer_pullback() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field = make(&surface);
    let _next = populate(&mut field);
    let census = field.census();
    let response = returned(&field);
    assert_eq!(field.census().section_read_outs, census.section_read_outs);
    let reading = response.inspect().unwrap();
    let k = response.query.contacts;
    let d = 6 * field.nodes();
    let map = decode(&surface, &response._producing.map, 72)
        .chunks(d / 2)
        .take(k)
        .map(|v| v.to_vec())
        .collect::<Vec<_>>();
    let raw = wides(
        &surface
            .detach_section(&response._forward, 64)
            .unwrap()
            .intervals,
    )
    .unwrap();
    let scale = BigInt::one() << 72u32;
    let waves = |v: &[i128]| {
        v.chunks_exact(2)
            .map(|v| {
                ExactComplexWaveCurrent::new(
                    Rat::new(v[0].into(), scale.clone()),
                    Rat::new(v[1].into(), scale.clone()),
                )
            })
            .collect::<Vec<_>>()
    };
    let incoming = waves(&raw[4 * (d + 1)..4 * (d + 1) + d]);
    let before = field.history[2]
        .resident
        .operative
        .as_ref()
        .unwrap();
    let mut internal = decode(&surface, &before.b, 72);
    internal.truncate(before.count);
    internal.resize(k, ExactComplexWaveCurrent::zero());
    let producer = PairedJunctionLinearization::at(map, &incoming, &internal).unwrap();
    let midpoint = |xs: &[holonics::exact_value::ExactInterval]| {
        xs.chunks_exact(2)
            .map(|v| {
                ExactComplexWaveCurrent::new(
                    (&v[0].lower + &v[0].upper) / Rat::from_integer(2.into()),
                    (&v[1].lower + &v[1].upper) / Rat::from_integer(2.into()),
                )
            })
            .collect::<Vec<_>>()
    };
    let reference = producer
        .pullback(
            &midpoint(&reading.query.outgoing_current),
            &midpoint(&reading.query.internal_current),
        )
        .unwrap();
    enclosed(
        &reference.source,
        &reading.incoming_source.center,
        &reading.incoming_source.radius,
    );
    enclosed(
        &reference.incoming_internal,
        &reading.incoming_internal.center,
        &reading.incoming_internal.radius,
    );
    enclosed(
        &reference.potential_covector,
        &reading.contact_covector.port_factors[0],
        &reading.potential_covector_radius,
    );
    let mut expected = Vec::new();
    let mut actual = Vec::new();
    for i in 0..k {
        expected.extend(reference.contacts.contact(i).unwrap());
        actual.extend(reading.contact(i).unwrap());
    }
    enclosed(&expected, &actual, &reading.contact_covector_radius);
    let norm: Rat = actual.iter().map(|v| v.norm_square()).sum();
    assert!(norm > &reading.contact_covector_radius * &reading.contact_covector_radius);
}
