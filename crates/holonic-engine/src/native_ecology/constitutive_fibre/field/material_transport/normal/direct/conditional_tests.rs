use super::*;
use crate::embedding_fiber::ResidentReadout;
use num_traits::{One, Zero};

fn mount<'c>(surface: &'c ResidentSurface<'c>, values: &[i128]) -> ResidentSection<'c> {
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

#[test]
#[ignore = "requires CUDA; exact conditional affine map on a nonzero joint source ball"]
fn conditional_joint_map_preserves_shared_radius_and_affine_tail() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let grain = ResidentGrain(16);
    let scale = 1i128 << grain.0;
    let normal = ResidentNormalMaterial::found_features(&surface, 3, 1, grain).unwrap();
    // Explicit mathematical coefficient fixture: A(h)=i+(1-i)h, c(h)=2h.
    // The test covers its realised action, not a fitted-learning claim.
    let rest = normal.rest().unwrap();
    let mut words = wides(&rest.state().intervals).unwrap();
    words[..6].copy_from_slice(&[0, scale, 2 * scale, 0, scale, -scale]);
    let view = ResidentNormalMaterialView {
        surface: &surface,
        state: Rc::new(mount(&surface, &words)),
        source_chart: NormalSourceChart::Features { source_complex: 3 },
        targets: 1,
        grain,
        observations: 0,
    };
    let source_section = mount(&surface, &[scale, 2 * scale, 3 * scale, 4 * scale, scale]);
    let source = ResidentNormalEnclosureView {
        surface: &surface,
        section: &source_section,
        offset: 0,
        width: 4,
        grain,
    };
    let external_section = mount(&surface, &[-scale, 0, scale / 2]);
    let external = ResidentNormalEnclosureView {
        surface: &surface,
        section: &external_section,
        offset: 0,
        width: 2,
        grain,
    };
    for (h, den) in [(0, 1), (1, 1), (1, 2)] {
        let condition = surface
            .mount_section_rest(
                &ResidentSectionRest::found(
                    1,
                    3,
                    ResidentGrain(0),
                    64,
                    vec![(h, h), (0, 0), (den, den)],
                )
                .unwrap(),
            )
            .unwrap();
        let condition = ResidentConstitutiveCurrent::rational(&condition).unwrap();
        let reads = surface.census().section_read_outs;
        let out = view
            .read_applied_bilinear_joint(source, 2, condition, external)
            .unwrap();
        assert_eq!(surface.census().section_read_outs, reads);
        let ball = out.inspect().unwrap();
        assert_eq!(ball.radius, Rat::new(3.into(), 2.into()));
        let z = |re: i64, im: i64| {
            ExactComplexWaveCurrent::new(Rat::from_integer(re.into()), Rat::from_integer(im.into()))
        };
        assert_eq!(
            ball.center,
            if h == 0 {
                vec![z(-3, 1), z(3, 4)]
            } else if den == 1 {
                vec![z(2, 2), z(3, 4)]
            } else {
                vec![
                    ExactComplexWaveCurrent::new(
                        Rat::new((-1).into(), 2.into()),
                        Rat::new(3.into(), 2.into()),
                    ),
                    z(3, 4),
                ]
            }
        );
        // Several points on the COMMON radius-one sphere, including mixed directions,
        // transformed exactly. Independent external uncertainty is zero in these points.
        for (ds, db) in [
            (z(1, 0), z(0, 0)),
            (z(0, 0), z(0, 1)),
            (
                ExactComplexWaveCurrent::new(Rat::new(3.into(), 5.into()), Rat::zero()),
                ExactComplexWaveCurrent::new(Rat::zero(), Rat::new(4.into(), 5.into())),
            ),
        ] {
            let delta = if h == 0 {
                z(0, 1).multiply(&ds)
            } else if den == 1 {
                ds
            } else {
                ExactComplexWaveCurrent::new(
                    Rat::new(1.into(), 2.into()),
                    Rat::new(1.into(), 2.into()),
                )
                .multiply(&ds)
            };
            assert!(ball.contains(&[ball.center[0].add(&delta), ball.center[1].add(&db)]));
        }
    }
    // Zero A removes boundary uncertainty but must not discard the uncertain interior.
    words[..6].fill(0);
    let zero = ResidentNormalMaterialView {
        state: Rc::new(mount(&surface, &words)),
        ..view
    };
    let h = surface
        .mount_section_rest(
            &ResidentSectionRest::found(1, 2, ResidentGrain(0), 64, vec![(0, 0), (0, 0)]).unwrap(),
        )
        .unwrap();
    let condition = ResidentConstitutiveCurrent::integers(&h).unwrap();
    let ball = zero
        .read_applied_bilinear_joint(source, 2, condition, external)
        .unwrap()
        .inspect()
        .unwrap();
    assert_eq!(ball.radius, Rat::new(3.into(), 2.into()));
    assert_eq!(ball.center[0].real, -Rat::one());
    assert!(zero
        .read_applied_bilinear_joint(source, 6, condition, external)
        .is_err());
    assert!(zero
        .read_applied_bilinear_joint(source, 1, condition, external)
        .is_err());
}
