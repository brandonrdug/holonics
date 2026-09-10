use super::*;
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
