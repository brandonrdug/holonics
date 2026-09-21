use super::*;

#[test]
#[ignore = "requires CUDA; homogeneous feature is one at the packet grain, not one carrier unit"]
fn homogeneous_feature_retains_the_declared_unit_and_radius() {
    let readout=ResidentReadout::new().unwrap();
    let surface=ResidentSurface::on(&readout).unwrap();
    let raw=surface.mount_section_rest(&ResidentSectionRest::found(1,2,ResidentGrain(0),64,vec![(3,3),(-2,-2)]).unwrap()).unwrap();
    let source=ResidentNormalEnclosureSection::from_points(ResidentConstitutiveSection::integers(&raw).unwrap(),ResidentGrain(16)).unwrap();
    let expanded=source.append_homogeneous().unwrap();
    let before=source.row(0).unwrap().inspect().unwrap();
    let after=expanded.row(0).unwrap().inspect().unwrap();
    assert_eq!(after.center[0],before.center[0]);
    assert_eq!(after.center[1],ExactComplexWaveCurrent::one());
    assert_eq!(after.radius,before.radius);
}
use crate::embedding_fiber::ResidentReadout;

fn points<'c>(
    s: &'c ResidentSurface<'c>,
    rows: usize,
    width: usize,
    v: &[i64],
) -> ResidentSection<'c> {
    s.mount_section_rest(
        &ResidentSectionRest::found(
            rows,
            width,
            ResidentGrain(0),
            i64::BITS,
            v.iter().map(|x| (*x, *x)).collect(),
        )
        .unwrap(),
    )
    .unwrap()
}
#[test]
#[ignore = "requires CUDA; whole-section normal integration equals the complete sequential geometry and retains both actual operator cuts"]
fn section_integrates_once_and_preserves_the_common_producing_operators() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let source = points(
        &s,
        3,
        7,
        &[
            1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3,
        ],
    );
    let observed = points(&s, 3, 3, &[1, 0, 1, 0, -1, 1, 1, 1, 2]);
    let x = ResidentConstitutiveSection::rationals(&source).unwrap();
    let y = ResidentConstitutiveSection::rationals(&observed).unwrap();
    let mut body = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(u32::BITS)).unwrap();
    let mut reference = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(u32::BITS)).unwrap();
    let before = s.census();
    let returned = body.receive_section(x, y).unwrap();
    assert_eq!(s.census().section_read_outs, before.section_read_outs);
    assert_eq!(body.observations(), 3);
    assert_eq!(returned.predecessor_observations, 0);
    assert_eq!(returned.successor_observations, 3);
    for row in 0..x.rows() {
        reference
            .receive(x.row(row).unwrap(), y.row(row).unwrap())
            .unwrap();
    }
    assert_eq!(body.state_wire().unwrap(), reference.state_wire().unwrap());
    let field = returned.inspect_forward().unwrap();
    for row in 0..x.rows() {
        let single = reference
            .read(x.row(row).unwrap())
            .unwrap()
            .inspect_before()
            .unwrap()
            .forward;
        assert_eq!(single.center, field[row].center);
        assert_eq!(single.radius, field[row].radius);
        assert!(returned
            .before(row)
            .unwrap()
            .inspect()
            .unwrap()
            .center
            .iter()
            .all(|v| v.norm_square().is_zero()));
    }
    assert!(returned.forward(x.rows()).is_err());
    assert!(x.row(x.rows()).is_err());
    let producing = serde_json::to_value(returned.inspect_after_operator().unwrap()).unwrap();
    body.receive(x.row(0).unwrap(), y.row(0).unwrap()).unwrap();
    assert_eq!(
        serde_json::to_value(returned.inspect_after_operator().unwrap()).unwrap(),
        producing
    );
    assert_ne!(
        serde_json::to_value(body.inspect().unwrap()).unwrap(),
        producing
    );
}

#[test]
#[ignore = "requires CUDA; a malformed later row cannot commit an earlier section prefix"]
fn a_late_section_refusal_preserves_every_old_moment() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let source = points(&s, 2, 6, &[1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]);
    let bad = s
        .mount_section_rest(
            &ResidentSectionRest::found(
                2,
                2,
                ResidentGrain(0),
                i64::BITS,
                vec![(1, 1), (0, 0), (0, 1), (0, 0)],
            )
            .unwrap(),
        )
        .unwrap();
    let mut body = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(u32::BITS)).unwrap();
    let before = body.state_wire().unwrap();
    assert!(body
        .receive_section(
            ResidentConstitutiveSection::integers(&source).unwrap(),
            ResidentConstitutiveSection::integers(&bad).unwrap()
        )
        .is_err());
    assert_eq!(body.state_wire().unwrap(), before);
    assert_eq!(body.observations(), 0);
    let good = points(&s, 2, 2, &[1, 0, 0, 1]);
    body.receive_section(
        ResidentConstitutiveSection::integers(&source).unwrap(),
        ResidentConstitutiveSection::integers(&good).unwrap(),
    )
    .unwrap();
    assert_eq!(body.observations(), 2);
}

#[test]
#[ignore = "requires CUDA; the generic difference receiver retains separate source and observed denominators and all comparands"]
fn rational_current_path_produces_its_exact_local_difference_field() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let path = points(&s, 4, 3, &[3, 2, 6, 3, -2, 4, -1, 3, 3, 10, 1, 5]);
    let input = ResidentConstitutiveSection::rationals(&path).unwrap();
    let reads = s.census().section_read_outs;
    let field = input.differences(&s).unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    assert_eq!(field.original().rows(), 4);
    assert_eq!(field.source().rows(), 2);
    let values = |v: ResidentConstitutiveSection<'_, '_>| {
        s.read_out(v.section)
            .unwrap()
            .into_iter()
            .map(|(a, b)| {
                assert_eq!(a, b);
                a
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(
        values(field.source()),
        vec![3, -10, 9, -6, 6, 4, 12, -13, 18, -4, 12, 9, -6, 12]
    );
    assert_eq!(values(field.observed()), vec![-13, 18, 12, 35, -12, 15]);
    let mut body = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(u32::BITS)).unwrap();
    body.receive_section(field.source(), field.observed())
        .unwrap();
    assert_eq!(body.observations(), 2);
}

#[test]
#[ignore = "requires CUDA; bounded observation batches preserve every normal statistic and fit the same endpoint once"]
fn enclosed_batch_has_the_sequential_endpoint_without_input_retention() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let grain = ResidentGrain(72);
    let ball = |v: [i64; 3], radius: i128| {
        let scale = 1i128 << grain.0;
        let values = [
            v[0] as i128 * scale / v[2] as i128,
            v[1] as i128 * scale / v[2] as i128,
            radius,
        ]
        .into_iter()
        .flat_map(|x| [x as i64, (x >> 64) as i64])
        .map(|x| (x, x))
        .collect::<Vec<_>>();
        s.mount_section_rest(
            &ResidentSectionRest::found(1, 6, ResidentGrain(0), 64, values).unwrap(),
        )
        .unwrap()
    };
    let xs = [
        ball([1, 1, 1], 1i128 << 68),
        ball([2, -1, 1], 1i128 << 69),
        ball([-1, 0, 1], 0),
    ];
    let ys = [
        ball([2, 1, 1], 1i128 << 68),
        ball([-1, 3, 1], 0),
        ball([1, -2, 1], 1i128 << 67),
    ];
    let pairs = xs
        .iter()
        .zip(&ys)
        .map(|(x, y)| {
            (
                ResidentNormalEnclosureView {
                    surface: &s,
                    section: x,
                    offset: 0,
                    width: 2,
                    grain,
                },
                ResidentNormalEnclosureView {
                    surface: &s,
                    section: y,
                    offset: 0,
                    width: 2,
                    grain,
                },
            )
        })
        .collect::<Vec<_>>();
    let mut batch = ResidentNormalMaterial::found_features(&s, 1, 1, grain).unwrap();
    let mut serial = ResidentNormalMaterial::found_features(&s, 1, 1, grain).unwrap();
    let before = s.census().section_read_outs;
    batch.receive_many(&pairs).unwrap();
    assert_eq!(s.census().section_read_outs, before);
    for &(x, y) in &pairs {
        serial.receive(x, y).unwrap();
    }
    assert_eq!(batch.state_wire().unwrap(), serial.state_wire().unwrap());
    assert_eq!(batch.observations(), 3);
    let before = batch.rest().unwrap();
    batch.receive_many(&[]).unwrap();
    assert_eq!(batch.rest().unwrap(), before);
    let wrong = [(
        pairs[0].0,
        ResidentNormalEnclosureView {
            grain: ResidentGrain(64),
            ..pairs[0].1
        },
    )];
    assert!(batch.receive_many(&wrong).is_err());
    assert_eq!(batch.rest().unwrap(), before);
}

/// Wide (paired-word) carrier packing, as the normal state and every enclosure use it.
fn wide_words<'c>(surface: &'c ResidentSurface<'c>, values: &[i128]) -> ResidentSection<'c> {
    let words = values
        .iter()
        .flat_map(|v| {
            let bytes = v.to_le_bytes();
            [
                i64::from_le_bytes(bytes[..8].try_into().unwrap()),
                i64::from_le_bytes(bytes[8..].try_into().unwrap()),
            ]
        })
        .map(|v| (v, v))
        .collect();
    surface
        .mount_section_rest(
            &ResidentSectionRest::found(1, values.len() * 2, ResidentGrain(0), 64, words).unwrap(),
        )
        .unwrap()
}

fn balls_meet(left: &NativeFieldCurrentBall, right: &NativeFieldCurrentBall) -> bool {
    let separation: Rat = left
        .center
        .iter()
        .zip(&right.center)
        .map(|(a, b)| {
            let re = &a.real - &b.real;
            let im = &a.imaginary - &b.imaginary;
            &re * &re + &im * &im
        })
        .sum();
    let reach = &left.radius + &right.radius;
    separation <= &reach * &reach
}

#[test]
#[ignore = "requires CUDA; the row-sectioned applied condition agrees with the single-row owner, encloses the point section and re-enters as a source"]
fn enclosed_condition_rows_agree_row_by_row_and_re_enter_as_the_next_source() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let grain = ResidentGrain(16);
    let scale = 1i128 << grain.0;
    let normal = ResidentNormalMaterial::found_features(&s, 3, 1, grain).unwrap();
    // Explicit coefficient fixture: A(h)=i+(1-i)h, c(h)=2h. The test covers its realised
    // action over a section of rows, not a fitted-learning claim.
    let rest = normal.rest().unwrap();
    let mut state = wides(&rest.state().intervals).unwrap();
    state[..6].copy_from_slice(&[0, scale, 2 * scale, 0, scale, -scale]);
    let view = ResidentNormalMaterialView { prior: None,
        surface: &s,
        state: Rc::new(wide_words(&s, &state)),
        source_chart: NormalSourceChart::Features { source_complex: 3 },
        targets: 1,
        grain,
        observations: 0,
    };
    let source_words = points(&s, 2, 3, &[1, 0, 1, 0, -2, 1]);
    let condition_words = points(&s, 2, 3, &[1, 1, 1, 1, 0, 2]);
    let source_points = ResidentConstitutiveSection::rationals(&source_words).unwrap();
    let condition_points = ResidentConstitutiveSection::rationals(&condition_words).unwrap();
    let source = ResidentNormalEnclosureSection::from_points(source_points, grain).unwrap();
    let reads = s.census().section_read_outs;
    let reaction = view
        .read_applied_bilinear_enclosed_section(&source, condition_points, false)
        .unwrap();
    let incoming = view
        .read_applied_bilinear_enclosed_section(&source, condition_points, true)
        .unwrap();
    // One enclosure section re-enters as the next source with its radius intact, and the
    // whole chain stays resident: no row was read back to the host to make it a point.
    let again = reaction
        .reapply_bilinear(&view, condition_points, true)
        .unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    assert_eq!(reaction.rows(), 2);
    assert_eq!(reaction.components(), 2);
    assert_eq!(again.components(), 2);
    let value = |re: i64, im: i64| {
        ExactComplexWaveCurrent::new(Rat::from_integer(re.into()), Rat::from_integer(im.into()))
    };
    // y = i·s + 2·h + (1-i)·h·s, then the identity path x + y on the shared source.
    let expected = [
        (value(4, 3), value(5, 3)),
        (value(2, -1), value(2, -3)),
    ];
    for (row, (reacted, incame)) in expected.iter().enumerate() {
        let single = view
            .read_applied_bilinear(source.row(row).unwrap(), condition_points.row(row).unwrap())
            .unwrap()
            .inspect()
            .unwrap();
        let sectioned = reaction.row(row).unwrap().inspect().unwrap();
        assert_eq!(sectioned.center, single.center);
        assert_eq!(sectioned.radius, single.radius);
        assert_eq!(sectioned.center, vec![reacted.clone()]);
        let single = view
            .read_applied_bilinear_identity(
                source.row(row).unwrap(),
                condition_points.row(row).unwrap(),
            )
            .unwrap()
            .inspect()
            .unwrap();
        let sectioned = incoming.row(row).unwrap().inspect().unwrap();
        assert_eq!(sectioned.center, single.center);
        assert_eq!(sectioned.radius, single.radius);
        assert_eq!(sectioned.center, vec![incame.clone()]);
    }
    // At zero radius the same rows are the point-section owner's rows.
    let point_section = view
        .read_applied_bilinear_section(source_points, condition_points)
        .unwrap();
    for row in 0..2 {
        assert_eq!(
            point_section.row(row).unwrap().inspect().unwrap().center,
            reaction.row(row).unwrap().inspect().unwrap().center
        );
    }
    // A source row that is not dyadic enters as a genuine enclosure; the returned ball still
    // holds the exact point-section value, which is what refinement re-entry depends on.
    let thirds = points(&s, 2, 3, &[1, 0, 3, 0, -2, 1]);
    let thirds_points = ResidentConstitutiveSection::rationals(&thirds).unwrap();
    let thirds_source = ResidentNormalEnclosureSection::from_points(thirds_points, grain).unwrap();
    assert!(!thirds_source.row(0).unwrap().inspect().unwrap().radius.is_zero());
    let enclosed = view
        .read_applied_bilinear_enclosed_section(&thirds_source, condition_points, false)
        .unwrap();
    let exact = view
        .read_applied_bilinear_section(thirds_points, condition_points)
        .unwrap();
    for row in 0..2 {
        assert!(balls_meet(
            &enclosed.row(row).unwrap().inspect().unwrap(),
            &exact.row(row).unwrap().inspect().unwrap()
        ));
    }
    // A condition row that is itself an enclosure adds its own transported term, and the
    // result still holds the value the exact point condition produces.
    let condition_enclosure =
        ResidentNormalEnclosureSection::from_points(condition_points, grain).unwrap();
    let paired = view
        .read_applied_bilinear_enclosed_pair(&source, &condition_enclosure, false)
        .unwrap();
    for row in 0..2 {
        assert!(balls_meet(
            &paired.row(row).unwrap().inspect().unwrap(),
            &reaction.row(row).unwrap().inspect().unwrap()
        ));
    }
    let uncertain_condition = points(&s, 2, 3, &[1, 1, 3, 1, 0, 2]);
    let uncertain_condition = ResidentNormalEnclosureSection::from_points(
        ResidentConstitutiveSection::rationals(&uncertain_condition).unwrap(),
        grain,
    )
    .unwrap();
    let widened = view
        .read_applied_bilinear_enclosed_pair(&source, &uncertain_condition, false)
        .unwrap();
    assert!(
        widened.row(0).unwrap().inspect().unwrap().radius
            > paired.row(0).unwrap().inspect().unwrap().radius
    );
    // Shape, parity and chart refusals. None of them silently restricts or pads an operand.
    let single_row = points(&s, 1, 3, &[1, 1, 1]);
    assert!(view
        .read_applied_bilinear_enclosed_section(
            &source,
            ResidentConstitutiveSection::rationals(&single_row).unwrap(),
            false
        )
        .is_err());
    let odd = points(&s, 2, 2, &[1, 1, 1, 1]);
    assert!(view
        .read_applied_bilinear_enclosed_section(
            &source,
            ResidentConstitutiveSection::rationals(&odd).unwrap(),
            false
        )
        .is_err());
    let wide_source = points(&s, 2, 5, &[1, 0, 0, 0, 1, 0, 0, 1, 0, 1]);
    let wide_source = ResidentNormalEnclosureSection::from_points(
        ResidentConstitutiveSection::rationals(&wide_source).unwrap(),
        grain,
    )
    .unwrap();
    assert!(view
        .read_applied_bilinear_enclosed_section(&wide_source, condition_points, false)
        .is_err());
    let coarse = ResidentNormalEnclosureSection::from_points(source_points, ResidentGrain(20)).unwrap();
    assert!(view
        .read_applied_bilinear_enclosed_section(&coarse, condition_points, false)
        .is_err());
}
