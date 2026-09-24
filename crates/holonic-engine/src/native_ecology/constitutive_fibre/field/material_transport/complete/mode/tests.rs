use super::*;
use crate::embedding_fiber::ResidentReadout;
fn phase(r: i64, i: i64, d: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(r, i, d).unwrap()
}
fn seed(n: usize) -> Vec<NativeJunctionSeed> {
    vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        };
        n
    ]
}
fn dark<'c>(
    s: &'c ResidentSurface<'c>,
    gap: bool,
    n: usize,
) -> (
    NativeConstitutiveField<'c>,
    NativeFieldContinuation,
    NativeFieldSourceAnchor,
) {
    let mut b =
        NativeConstitutiveField::found_with_enclosed_junction(s, seed(n), ResidentGrain(72))
            .unwrap();
    b.enable_material_transport_source(NativeMaterialTransportSource::CompleteCurrent)
        .unwrap();
    let input = |p| {
        let mut v = vec![phase(0, 0, 1); n];
        v[0] = p;
        v
    };
    let first = b
        .advance_resident(&mut NativeFieldOccurrence::entering(input(phase(1, 0, 1))))
        .unwrap();
    let source = b.retain_source(&first.source).unwrap();
    let mut birth = None;
    for i in 0..2 {
        let next = b
            .advance_resident(&mut NativeFieldOccurrence::through_anchor(
                &source,
                input(phase(1, 0, 1)),
            ))
            .unwrap();
        if i == 0 {
            birth = Some(b.retain_source(&next.source).unwrap());
            if gap {
                b.advance_resident(&mut NativeFieldOccurrence::entering(input(phase(0, 1, 1))))
                    .unwrap();
            }
        }
    }
    b.advance_resident(&mut NativeFieldOccurrence::entering(input(phase(
        -9, 0, 10,
    ))))
    .unwrap();
    b.advance_resident(&mut NativeFieldOccurrence::entering(input(phase(0, 0, 1))))
        .unwrap();
    let last = b
        .advance_resident(&mut NativeFieldOccurrence::entering(input(phase(0, 0, 1))))
        .unwrap();
    (b, last, birth.unwrap())
}
fn column(
    matrix: &[Vec<ExactComplexWaveCurrent>],
    l: usize,
    r: usize,
) -> Vec<ExactComplexWaveCurrent> {
    matrix
        .iter()
        .map(|row| {
            row[l]
                .subtract(&row[r])
                .scaled(&Rat::new(1.into(), 2.into()))
        })
        .collect()
}
fn assert_ball(b: &NativeFieldCurrentBall, v: &[ExactComplexWaveCurrent]) {
    assert!(b.contains(v), "{b:?} does not contain {v:?}");
}

/// Parity law (material mode): device mode coefficient, projection, full current and remainder
/// balls contain the exact host values, with remainder = full − projected mode.
#[test]
#[ignore = "requires CUDA; factor chronology before/between/after births and reversed orientation survive"]
fn mode_coefficients_match_the_existing_full_operator_and_preserve_the_source_remainder() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let (mut b, last, birth) = dark(&s, true, 1);
    let source = b.retain_source(&last.source).unwrap();
    let at = last.lineage.occurrence;
    let exact_source = b.inspect_exact_junction(at).unwrap().unwrap();
    let internal = b.inspect_internal_currents().unwrap().unwrap();
    let mut x = exact_source.outgoing;
    x.extend(internal.iter().map(|x| x.current.clone()));
    let q = internal[0].current.subtract(&internal[1].current);
    b.advance_resident(&mut NativeFieldOccurrence::through_anchor(
        &source,
        vec![phase(1, 1, 1)],
    ))
    .unwrap();
    // A later return at source 1 uses a column where the left mode member existed and the right
    // did not. Read-only source addresses do not manufacture an available receiving capability.
    b.advance_resident(&mut NativeFieldOccurrence::through_anchor(
        &birth,
        vec![phase(-1, 0, 1)],
    ))
    .unwrap();
    let record = b
        .read_material_mode(&source, 1, 3)
        .unwrap()
        .inspect()
        .unwrap();
    let exact = b
        .inspect_exact_complete_material_transport(b.occurrence_count() - 1)
        .unwrap()
        .unwrap();
    x.resize(exact.coefficients[0].len(), ExactComplexWaveCurrent::zero());
    let full = apply(&exact.coefficients, &x);
    let k = column(&exact.coefficients, 3, 4);
    let projected = k.iter().map(|k| k.multiply(&q)).collect::<Vec<_>>();
    assert_ball(&record.current_coefficient, &k);
    assert_ball(&record.current_mode, &projected);
    assert_ball(&record.current_full, &full);
    assert_ball(&record.current_remainder, &subtract(&full, &projected));
    let reverse = b
        .read_material_mode(&source, 3, 1)
        .unwrap()
        .inspect()
        .unwrap();
    assert_eq!(reverse.numerical_modes, record.numerical_modes);
    assert_eq!(
        reverse.numerical_coefficients[1],
        record.numerical_coefficients[1]
            .iter()
            .map(|v| v.negated())
            .collect::<Vec<_>>()
    );
    assert_eq!(
        b.read_material_mode(&source, 1, 3)
            .unwrap()
            .inspect()
            .unwrap()
            .numerical_modes,
        record.numerical_modes
    );
    assert!(b.read_material_mode_at(1, 1, 3).is_err());
    drop(b);
}
