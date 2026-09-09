use super::*;
use crate::embedding_fiber::ResidentReadout;
use crate::resident_section::SeriesAperture;
use num_traits::Zero;

fn packet(word: usize) -> Vec<NativePhaseCurrent> {
    (0..6)
        .map(|i| {
            if (word >> (i / 2)) & 1 == i % 2 {
                NativePhaseCurrent::unit()
            } else {
                NativePhaseCurrent::zero()
            }
        })
        .collect()
}
fn make<'c>(surface: &'c ResidentSurface<'c>) -> NativeConstitutiveField<'c> {
    let seed = vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero()
        };
        6
    ];
    let mut f =
        NativeConstitutiveField::found_with_enclosed_junction(surface, seed, ResidentGrain(72))
            .unwrap();
    f.enable_material_transport_chart(
        NativeMaterialTransportSource::OperativeContextual,
        NativeMaterialTarget::TensorProduct { factor_width: 2 },
    )
    .unwrap();
    f
}
fn point(r: i64, i: i64, d: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(r, i, d).unwrap()
}

#[test]
#[ignore = "requires CUDA; tensor phase, separate material codomain, actual observation and adjoint"]
fn packet_target_retains_joint_phase_and_restarts_with_its_own_codomain() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field = make(&surface);
    assert_eq!(field.nodes(), 6);
    assert_eq!(field.material_target_dimension(), Some(8));
    let incoming = vec![
        point(1, 0, 3),
        point(0, 1, 1),
        point(2, 0, 1),
        point(-1, 0, 1),
        point(1, 1, 1),
        point(1, -1, 1),
    ];
    let before = field.census();
    let first = field
        .advance_resident(&mut NativeFieldOccurrence::entering(incoming.clone()))
        .unwrap();
    assert_eq!(field.census().section_read_outs, before.section_read_outs);
    let observed = field
        .inspect_contextual_material_transport(0)
        .unwrap()
        .unwrap()
        .observed;
    let exact = (0..8)
        .map(|word| {
            (0..3).fold(ExactComplexWaveCurrent::one(), |v, i| {
                v.multiply(&incoming[2 * i + ((word >> i) & 1)].current())
            })
        })
        .collect::<Vec<_>>();
    assert!(observed.contains(&exact));
    assert!(observed.radius > Rat::zero());
    assert!(exact.iter().any(|z| !z.imaginary.is_zero()));
    let anchor = field.retain_source(&first.source).unwrap();
    let second = field
        .advance_resident(&mut NativeFieldOccurrence::through(first.source, packet(7)))
        .unwrap();
    let r = field
        .normalized_material_return(1, 8, SeriesAperture(32))
        .unwrap()
        .unwrap()
        .inspect()
        .unwrap();
    for (i, q) in r.observation.iter().enumerate() {
        assert_eq!(q.lower, Rat::from_integer((i == 7).into()));
        assert_eq!(q.upper, q.lower);
    }
    assert_eq!(
        field.read_material_packet(1).unwrap().unwrap().selected,
        Some(7)
    );
    let third = field
        .advance_resident(&mut NativeFieldOccurrence::through(
            second.source,
            packet(1),
        ))
        .unwrap();
    let returned = field
        .normalized_material_return(2, 8, SeriesAperture(32))
        .unwrap()
        .unwrap();
    let before = field.census();
    let query = field
        .pull_back_material_source(&returned, NativeMaterialPullbackMetric::RelativeEntropy)
        .unwrap();
    assert_eq!(field.census().section_read_outs, before.section_read_outs);
    let reading = query.inspect().unwrap();
    assert!(
        reading
            .outgoing_current
            .iter()
            .chain(&reading.internal_current)
            .any(|v| v.lower > Rat::zero() || v.upper < Rat::zero()),
        "the target coordinate beyond the root extent must return"
    );
    let response = field.material_contact_response(query).unwrap();
    field
        .apply_material_contact_realization(&response, NativeContactRealization::DyadicDeposit)
        .unwrap();
    let fourth = field
        .advance_resident(&mut NativeFieldOccurrence::through_anchor(
            &anchor,
            packet(6),
        ))
        .unwrap();
    let report = field
        .inspect_contextual_material_transport(3)
        .unwrap()
        .unwrap();
    assert_eq!(report.source_occurrence, Some(0));
    assert_eq!(report.reference_receiving_occurrence, Some(1));
    assert_eq!(report.observed.center.len(), 8);
    assert_eq!(report.visible_source.center.len(), 12);
    let saved = field
        .rest(&[Some(&fourth.source)], &[Some(&anchor)])
        .unwrap();
    let mut bytes = vec![];
    saved.write(&mut bytes).unwrap();
    let restored = NativeFieldRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    assert_eq!(
        restored.material_target(),
        Some(NativeMaterialTarget::TensorProduct { factor_width: 2 })
    );
    let expected = field
        .advance_resident(&mut NativeFieldOccurrence::through(
            fourth.source,
            packet(2),
        ))
        .unwrap();
    let expected = field.rest(&[Some(&expected.source)], &[]).unwrap();
    drop(third);
    drop(anchor);
    drop(response);
    drop(field);
    let (mut field, mut sources, _) = NativeConstitutiveField::remount(&surface, restored).unwrap();
    let result = field
        .advance_resident(&mut NativeFieldOccurrence::through(
            sources[0].take().unwrap(),
            packet(2),
        ))
        .unwrap();
    assert_eq!(field.rest(&[Some(&result.source)], &[]).unwrap(), expected);
}

#[test]
#[ignore = "requires CUDA; joint coordinate support differs from independent marginal decoding"]
fn packet_target_receiver_keeps_the_joint_support() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    // The exact mean of three packet basis states. Its dyadic enclosure has three possible
    // maximizers. The independent-bit mean would instead select the absent coordinate seven.
    let scale = 1i128 << 72;
    let mut values = vec![0i128; 17];
    for at in [3, 5, 6] {
        values[2 * at] = scale / 3;
    }
    values[16] = 1;
    let words = values
        .into_iter()
        .flat_map(|x| [x as i64, (x >> 64) as i64])
        .map(|x| (x, x))
        .collect::<Vec<_>>();
    let input = surface
        .mount_section_rest(
            &ResidentSectionRest::found(1, words.len(), ResidentGrain(0), 64, words).unwrap(),
        )
        .unwrap();
    let output = surface.fresh_section(1, 10, ResidentGrain(0)).unwrap();
    let scratch = surface.fresh_section(1, 16, ResidentGrain(0)).unwrap();
    let mut passage = surface.begin_passage(&[vec![]]).unwrap();
    {
        let lane = passage.open(0, &[]).unwrap();
        surface
            .record_field_material_packet_receiver(&lane, &input, 8, &scratch, &output)
            .unwrap();
    }
    passage.close(0, &output, 64).unwrap();
    let result = passage.finish().unwrap().launch().unwrap();
    assert!(result.obstruction.is_empty());
    let result = surface.read_out(&output).unwrap();
    assert_eq!(result[0], (3, 3));
    assert_eq!(result[1], (-1, -1));
    assert_eq!(
        result[2..]
            .iter()
            .enumerate()
            .filter_map(|(i, v)| (v.0 == 1).then_some(i))
            .collect::<Vec<_>>(),
        vec![3, 5, 6]
    );
}

// Independent finite active-set reference: enumerate all faces of the maximum cone,
// rather than using the device's sorted pooling algorithm.
fn ball_maxima_reference(centres: &[i128], radius: i128) -> Vec<usize> {
    let rat = |v: i128| Rat::from_integer(v.into());
    (0..centres.len())
        .filter(|&candidate| {
            (0usize..1usize << centres.len())
                .filter(|mask| mask & (1 << candidate) != 0)
                .any(|mask| {
                    let count = mask.count_ones();
                    let mean = centres
                        .iter()
                        .enumerate()
                        .filter(|(j, _)| mask & (1 << j) != 0)
                        .map(|(_, v)| rat(*v))
                        .sum::<Rat>()
                        / rat(count.into());
                    if centres.iter().enumerate().any(|(j, v)| {
                        j != candidate
                            && if mask & (1 << j) != 0 {
                                rat(*v) < mean
                            } else {
                                rat(*v) > mean
                            }
                    }) {
                        return false;
                    }
                    let distance = centres
                        .iter()
                        .enumerate()
                        .filter(|(j, _)| mask & (1 << j) != 0)
                        .map(|(_, v)| {
                            let d = rat(*v) - &mean;
                            &d * &d
                        })
                        .sum::<Rat>();
                    distance <= rat(radius) * rat(radius)
                })
        })
        .collect()
}

#[test]
#[ignore = "requires CUDA; complete joint ball receiver against exact active-set enumeration"]
fn packet_target_receiver_transports_the_joint_ball_without_box_relaxation() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut cases = vec![
        (vec![3, 0], 2),
        (vec![5, 5, 0], 4),
        (vec![5, 5, 0], 5),
        (vec![4, 4, -3], 0),
        (vec![-8], 0),
    ];
    for seed in 0..24i128 {
        let centres = (0..5i128)
            .map(|i| ((seed * 7 + i * 11 + i * i * seed) % 17) - 8)
            .collect::<Vec<_>>();
        for radius in [0, 1, 3, 6] {
            cases.push((centres.clone(), radius));
        }
    }
    // A huge common potential gauge and nonzero imaginary phase do not change the face.
    cases.push((
        vec![(1i128 << 100) + 5, (1i128 << 100) + 5, 1i128 << 100],
        4,
    ));
    for (centres, radius) in cases {
        let targets = centres.len();
        let mut values = centres
            .iter()
            .enumerate()
            .flat_map(|(i, v)| [*v, 17 * i as i128 - 31])
            .collect::<Vec<_>>();
        values.push(radius);
        let words = values
            .into_iter()
            .flat_map(|x| [x as i64, (x >> 64) as i64])
            .map(|x| (x, x))
            .collect::<Vec<_>>();
        let input = surface
            .mount_section_rest(
                &ResidentSectionRest::found(1, words.len(), ResidentGrain(0), 64, words).unwrap(),
            )
            .unwrap();
        let scratch = surface
            .fresh_section(1, 2 * targets, ResidentGrain(0))
            .unwrap();
        let output = surface
            .fresh_section(1, targets + 2, ResidentGrain(0))
            .unwrap();
        let mut passage = surface.begin_passage(&[vec![]]).unwrap();
        {
            let lane = passage.open(0, &[]).unwrap();
            surface
                .record_field_material_packet_receiver(&lane, &input, targets, &scratch, &output)
                .unwrap();
        }
        passage.close(0, &output, 64).unwrap();
        let receipt = passage.finish().unwrap().launch().unwrap();
        assert!(
            receipt.obstruction.is_empty(),
            "{centres:?}, radius {radius}: {:?}",
            receipt.obstruction
        );
        let result = surface.read_out(&output).unwrap();
        assert!(result.iter().all(|(a, b)| a == b));
        let candidates = result[2..]
            .iter()
            .enumerate()
            .filter_map(|(i, v)| (v.0 == 1).then_some(i))
            .collect::<Vec<_>>();
        assert_eq!(
            candidates,
            ball_maxima_reference(&centres, radius),
            "{centres:?}, radius {radius}"
        );
        assert_eq!(result[0].0, candidates.len() as i64);
        assert_eq!(
            result[1].0,
            if candidates.len() == 1 {
                candidates[0] as i64
            } else {
                -1
            }
        );
    }
}
