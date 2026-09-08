use super::*;
use crate::embedding_fiber::ResidentReadout;
use crate::exact_value::CertifiedSeries;

pub(super) fn phase(r: i64, i: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(r, i, 1).unwrap()
}
pub(super) fn seed(nodes: usize) -> Vec<NativeJunctionSeed> {
    vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        };
        nodes
    ]
}
fn contains(outer: &ExactInterval, inner: &ExactInterval) {
    assert!(
        outer.lower <= inner.lower && inner.upper <= outer.upper,
        "{outer:?} does not contain {inner:?}"
    );
}

#[test]
#[ignore = "requires CUDA; source-qualified nonlinear receiver and its independently enclosed adjoint"]
fn normalized_receiver_returns_through_the_actual_prediction() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(2), ResidentGrain(72))
            .unwrap();
    field.enable_material_transport().unwrap();
    let first = field
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![
            phase(1, 0),
            phase(0, 1),
        ]))
        .unwrap();
    let anchor = field.retain_source(&first.source).unwrap();
    assert!(
        field
            .normalized_material_return(0, 2, SeriesAperture(32))
            .unwrap()
            .is_none()
    );
    let second = field
        .advance_resident(&mut NativeFieldOccurrence::through(
            first.source,
            vec![phase(1, 0), phase(0, 0)],
        ))
        .unwrap();
    let before = field.census();
    let receiver = field
        .normalized_material_return(1, 2, SeriesAperture(32))
        .unwrap()
        .unwrap();
    assert_eq!(field.census().section_read_outs, before.section_read_outs);
    let reading = receiver.inspect().unwrap();
    assert_eq!(reading.source.occurrence, 0);
    assert_eq!(reading.receiving.occurrence, 1);
    assert_eq!(reading.receiving.received_from, Some(0));
    let half = Rat::new(1.into(), 2.into());
    assert!(
        reading
            .prediction
            .iter()
            .all(|p| *p == ExactInterval::point(half.clone()))
    );
    // Independent exact rational Taylor enclosure: the material owner retains the unit input,
    // so q0=exp(1)/(1+exp(1)). The half above belongs only to the uniform prediction.
    let observed = field
        .inspect_material_transport(1)
        .unwrap()
        .unwrap()
        .observed;
    assert_eq!(
        observed.center[0],
        ExactComplexWaveCurrent::new(Rat::one(), Rat::zero())
    );
    let exp = CertifiedSeries::exponential_enclosure(&Rat::one(), 64).unwrap();
    let q = ExactInterval::new(
        &exp.lower / (Rat::one() + &exp.lower),
        &exp.upper / (Rat::one() + &exp.upper),
    )
    .unwrap();
    contains(&reading.observation[0], &q);
    let r = q.translated(&(-&half));
    contains(&reading.returned_difference[0], &r);
    contains(
        &reading.potential_pullback[0],
        &ExactInterval::new(&r.lower * &half, &r.upper * &half).unwrap(),
    );
    assert!(reading.potential_pullback[0].lower > Rat::zero());
    assert!(reading.potential_pullback[1].upper < Rat::zero());
    assert!(
        field
            .normalized_material_return(1, 3, SeriesAperture(32))
            .is_err()
    );
    // Another occurrence changes the ecology, never the producing reports held by this return.
    field
        .advance_resident(&mut NativeFieldOccurrence::through(
            second.source,
            vec![phase(0, 1), phase(1, 0)],
        ))
        .unwrap();
    let old = receiver.inspect().unwrap();
    assert_eq!(reading.prediction, old.prediction);
    assert_eq!(reading.potential_pullback, old.potential_pullback);
    field
        .advance_resident(&mut NativeFieldOccurrence::through_anchor(
            &anchor,
            vec![phase(0, 0), phase(1, 0)],
        ))
        .unwrap();
    let delayed = field
        .normalized_material_return(3, 2, SeriesAperture(32))
        .unwrap()
        .unwrap()
        .inspect()
        .unwrap();
    assert_eq!(delayed.source.occurrence, 0);
    assert_eq!(delayed.receiving.occurrence, 3);
    assert!(delayed.potential_pullback[0].upper < Rat::zero());
}

fn raw_return(pred: &[i128], pr: i128, obs: &[i128], qr: i128, group: usize) -> Vec<i128> {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let nodes = pred.len() / 2;
    let mount = |values: Vec<i128>| {
        let words: Vec<_> = values
            .into_iter()
            .flat_map(|v| [v as i64, (v >> 64) as i64])
            .map(|v| (v, v))
            .collect();
        surface
            .mount_section_rest(
                &ResidentSectionRest::found(1, words.len(), ResidentGrain(0), 64, words).unwrap(),
            )
            .unwrap()
    };
    let prediction = mount(pred.iter().copied().chain([pr]).collect());
    let observation = mount(
        std::iter::repeat_n(0, 2 * (2 * nodes + 1))
            .chain(obs.iter().copied())
            .chain([qr])
            .collect(),
    );
    let output = surface
        .fresh_section(1, 20 * nodes, ResidentGrain(0))
        .unwrap();
    let mut passage = surface.begin_passage(&[vec![]]).unwrap();
    {
        let lane = passage.open(0, &[]).unwrap();
        surface
            .record_field_normalized_receiver(
                &lane,
                &prediction,
                &observation,
                nodes,
                group,
                72,
                SeriesAperture(32),
                &output,
            )
            .unwrap();
    }
    passage.close(0, &output, 64).unwrap();
    let receipt = passage.finish().unwrap().launch().unwrap();
    assert!(receipt.obstruction.is_empty(), "{:?}", receipt.obstruction);
    material_transport::wides(&surface.detach_section(&output, 64).unwrap().intervals).unwrap()
}

#[test]
#[ignore = "requires CUDA; exact common gauge, imaginary residue and non-dyadic normalization"]
fn normalized_receiver_keeps_its_gauge_and_declared_groups() {
    let unit = 1i128 << 72;
    let p = [0, 7 * unit, unit, -3 * unit, 2 * unit, 11 * unit];
    let q = [5 * unit, -9 * unit, 6 * unit, unit, 7 * unit, -4 * unit];
    let values = raw_return(&p, 0, &q, 0, 3);
    for row in values.chunks_exact(10) {
        assert_eq!(&row[0..2], &row[2..4]);
        assert!(row[4..].iter().all(|v| *v == 0));
    }
    let values = raw_return(
        &[0, 0, 0, 0, 0, 0, 0, 0],
        0,
        &[unit, 0, 0, 0, 0, 0, unit, 0],
        0,
        2,
    );
    assert!(values[6] > 0 && values[16] < 0 && values[26] < 0 && values[36] > 0);
}

#[test]
#[ignore = "requires CUDA; wide uncertainty yields a complete open receiver instead of a point seal"]
fn normalized_receiver_retains_open_current_balls() {
    let values = raw_return(&[0, 0, 0, 0], 1i128 << 80, &[0, 0, 0, 0], 0, 2);
    for row in values.chunks_exact(10) {
        assert_eq!(row[0], 0);
        assert_eq!(row[1], 1i128 << 72);
        assert!(row[4] < 0 && row[5] > 0);
        assert!(row[6] < 0 && row[7] > 0);
    }
}
