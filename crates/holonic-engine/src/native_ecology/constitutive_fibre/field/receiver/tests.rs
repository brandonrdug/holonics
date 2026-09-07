use super::*;
use crate::embedding_fiber::ResidentReadout;

fn calibrated_receiver(centers: &[i128], radius: i128, exact_words: bool) -> Vec<i64> {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let dimension = centers.len();
    let stride = dimension + 1;
    let mode = if exact_words { 1 } else { 2 };
    let mut values = vec![0i64; if exact_words { 4 * stride } else { 12 * stride }];
    if exact_words {
        for part in 0..4 {
            values[part * stride + dimension] = 1;
        }
        for (i, value) in centers.iter().enumerate() {
            values[stride + i] = i64::try_from(*value).unwrap();
        }
    } else {
        for (i, value) in centers.iter().copied().chain([radius]).enumerate() {
            let at = 2 * (stride + i);
            values[at] = value as i64;
            values[at + 1] = (value >> 64) as i64;
        }
    }
    let report = surface
        .mount_section_rest(
            &ResidentSectionRest::found(
                1,
                values.len(),
                ResidentGrain(0),
                64,
                values.into_iter().map(|v| (v, v)).collect(),
            )
            .unwrap(),
        )
        .unwrap();
    let output = surface.fresh_section(1, 4, ResidentGrain(0)).unwrap();
    let mut passage = surface.begin_passage(&[vec![]]).unwrap();
    {
        let lane = passage.open(0, &[]).unwrap();
        surface
            .record_field_differential_receiver(
                &lane,
                &report,
                dimension,
                mode,
                0,
                dimension / 4,
                &output,
            )
            .unwrap();
    }
    passage.close(0, &output, 64).unwrap();
    let reading = passage.finish().unwrap().launch().unwrap();
    assert!(reading.obstruction.is_empty());
    surface
        .read_out(&output)
        .unwrap()
        .into_iter()
        .map(|(lo, hi)| {
            assert_eq!(lo, hi);
            lo
        })
        .collect()
}

#[test]
#[ignore = "requires CUDA; exact signs and a real-current tie with differing imaginary carriers"]
fn differential_word_receiver_keeps_exact_ties() {
    let currents = [0, 7, 2, -13, 2, 0, 0, 0, 1, 9, 1, -8];
    assert_eq!(calibrated_receiver(&currents, 0, true), vec![1, 2, 4, 4]);
}

#[test]
#[ignore = "requires CUDA; ball half-spaces are certified without choosing a center"]
fn differential_enclosure_does_not_seal_a_center_sign() {
    let currents = [0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 1, 0];
    assert_eq!(calibrated_receiver(&currents, 1, false), vec![1, 2, 4, 0]);
}

#[test]
#[ignore = "requires CUDA; packed signed-wide extremes use complete unsigned-256 squares"]
fn differential_receiver_keeps_the_complete_wide_gap() {
    assert_eq!(
        calibrated_receiver(&[i128::MIN, 0, i128::MAX, 0], i128::MAX, false),
        vec![1, 0, 0, 0]
    );
    assert_eq!(
        calibrated_receiver(&[0, 0, i128::MAX, 0], i128::MAX, false),
        vec![0, 0, 1, 0]
    );
}

#[test]
#[ignore = "requires CUDA; terminal current observation leaves the native owner and source available"]
fn differential_current_reading_preserves_continuation() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let material = vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        };
        2
    ];
    let mut body = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        material,
        ResidentGrain(72),
    )
    .unwrap();
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::unit(),
            NativePhaseCurrent::zero(),
        ]))
        .unwrap();
    let zero = body.read_differential_pairs(0, 4, 1).unwrap().unwrap();
    assert_eq!((zero.unresolved, zero.exact_zero), (1, 1));
    // Invalid receiver declarations refuse before opening a capture and leave future use lawful.
    assert!(matches!(
        body.read_differential_pairs(0, 6, 1),
        Err(ConstitutiveFibreError::Shape)
    ));
    let next = body
        .advance_resident(&mut NativeFieldOccurrence::through(
            first.source,
            vec![NativePhaseCurrent::zero(), NativePhaseCurrent::unit()],
        ))
        .unwrap();
    let before = body.inspect_junction(1).unwrap();
    let reading = body.read_differential_pairs(1, 4, 1).unwrap().unwrap();
    let cold = body
        .inspect_junction_enclosure(1)
        .unwrap()
        .unwrap()
        .outgoing;
    let margin = &cold.center[5].real - &cold.center[4].real;
    let certain = &margin * &margin > Rat::from_integer(2.into()) * &cold.radius * &cold.radius;
    assert_eq!(reading.unresolved == 0, certain);
    if certain {
        assert_eq!(reading.positive == 1, margin > Rat::from_integer(0.into()));
    }
    assert_eq!(body.occurrence_count(), 2);
    assert_eq!(body.inspect_junction(1).unwrap(), before);
    body.advance_resident(&mut NativeFieldOccurrence::through(
        next.source,
        vec![NativePhaseCurrent::unit(), NativePhaseCurrent::zero()],
    ))
    .unwrap();
    assert_eq!(body.occurrence_count(), 3);
}
