use super::*;
use crate::native::GeometricFieldSpec;
use num_rational::BigRational as Rat;
use num_traits::{Signed, Zero};
#[path = "../../../../examples/support/linked_torus_field.rs"]
mod linked_torus_field;

fn spec() -> FieldSessionSpec {
    FieldSessionSpec {
        symbols: vec!["a".into(), "b".into(), "c".into()],
        section_symbols: 4,
        context_symbols: 2,
        region_offsets: vec![],
        source_chart: FieldSourceChart::GeometricRegions,
        geometry: Some(linked_torus_field::linked_torus_field_spec(1, 2, 1).unwrap()),
        codec: FieldTextCodec::UnicodeScalars,
        fractional_bits: 48,
    }
}
fn request(retain: bool) -> FieldSectionRequest {
    FieldSectionRequest {
        text: String::new(),
        partial: Some(vec![Some("a".into()), None, Some("b".into()), None]),
        output_symbols: Some(4),
        context: vec!["c".into()],
        commit: false,
        retain_comparison: retain,
    }
}
#[test]
fn geometric_chart_consumes_actual_analytic_arcs_and_refuses_a_false_binding() {
    let mut s = spec();
    let layout = s.geometry.as_ref().unwrap().compile().unwrap();
    assert_eq!(layout.rows, 7);
    assert_eq!(layout.condition_complex, 3);
    assert_eq!(
        layout
            .groups
            .iter()
            .map(|g| g.receivers.len())
            .sum::<usize>(),
        7
    );
    assert_eq!(s.extents().unwrap(), (1, 3, 15));
    s.region_offsets = vec![-1, 0, 1];
    assert!(s.chart().is_err());
    s.region_offsets.clear();
    let geometry = s.geometry.as_mut().unwrap();
    geometry.arcs[0].to = geometry.arcs[0].from;
    assert!(s.chart().is_err());
}
#[test]
#[ignore = "requires CUDA; geometric participation/refinement, observed material and retained comparison all use the public session"]
fn public_geometric_session_updates_and_reopens_the_same_receiving_chart() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("geometric.session");
    let spec = spec();
    let expected = with_field_session(&spec, |s| {
        let first = s.request(&request(true))?;
        assert_eq!(first["symbols"][0], "a");
        assert_eq!(first["symbols"][2], "b");
        assert_eq!(first["geometric_rows"], 7);
        assert_eq!(first["refinement_steps"], 2);
        for direction in ["forward", "reverse"] {
            assert_eq!(first["placement"][format!("{direction}_cells")], 7);
            assert_eq!(first["placement"][format!("{direction}_disjoint")], true);
            assert_eq!(first["placement"][format!("{direction}_complete")], true);
        }
        assert_eq!(first["placement"]["cover"]["execution_observed"], false);
        let comparison = first["comparison"].as_u64().unwrap();
        assert!(s.observe(comparison, "short", 8).is_err());
        let update = s.observe(comparison, "aabb", 8)?;
        assert_eq!(update["returned"]["material_deposited"], true);
        let next = s.request(&request(true))?;
        assert_eq!(next["producing_epoch"], 1);
        s.checkpoint(&path, &HnaStreamState::default())?;
        Ok(next)
    })
    .unwrap();
    NativeFieldSavedSession::open(&path)
        .unwrap()
        .with_session(|s, _| {
            let actual = s.request(&request(false))?;
            for field in [
                "text",
                "symbols",
                "selections",
                "producing_epoch",
                "geometric_rows",
                "refinement_steps",
            ] {
                assert_eq!(actual[field], expected[field], "{field}");
            }
            let id = expected["comparison"].as_u64().unwrap();
            s.observe(id, "aabb", 8)?;
            assert!(s.observe(id, "aabb", 8).is_err());
            Ok(())
        })
        .unwrap();
}
fn seed<'c>(
    session: &NativeFieldSession<'c>,
    layout: &CompiledFieldGeometry,
    delta: i64,
) -> Rc<ResidentNormalEnclosureSection<'c>> {
    let d = 6;
    let mut values = Vec::new();
    for row in 0..layout.rows {
        let q = [
            ((row + 1) as i64) * 512 + if row == 0 { delta } else { 0 },
            512,
            ((row % 3) as i64 - 1) * 512,
            256,
            0,
            0,
            4096,
        ];
        values.extend(q.into_iter().map(|x| (x, x)));
    }
    let raw = session
        .surface
        .mount_section_rest(
            &ResidentSectionRest::found(layout.rows, d + 1, ResidentGrain(0), 64, values).unwrap(),
        )
        .unwrap();
    Rc::new(
        ResidentNormalEnclosureSection::from_points(
            ResidentConstitutiveSection::rationals(&raw).unwrap(),
            ResidentGrain(48),
        )
        .unwrap(),
    )
}
fn loss(field: &ResidentNormalEnclosureSection<'_>) -> Rat {
    (0..field.rows())
        .flat_map(|r| field.row(r).unwrap().inspect().unwrap().center)
        .map(|x| x.norm_square())
        .sum::<Rat>()
        / Rat::from_integer(2.into())
}
#[test]
#[ignore = "requires CUDA; full nonlinear two-step input adjoint checked after actual shared-material learning"]
fn geometric_word_paired_return_matches_a_directional_source_comparison() {
    with_field_session(&spec(), |s| {
        s.observe_source(&request(false), "aabb", 8)?;
        let layout = s.spec.geometry.as_ref().unwrap().compile()?;
        let held = vec![false; layout.rows * 3];
        let observed = vec![true; layout.rows * 3];
        let raw = s
            .surface
            .mount_section_rest(
                &ResidentSectionRest::found(
                    layout.rows,
                    6,
                    ResidentGrain(0),
                    64,
                    vec![(0, 0); layout.rows * 6],
                )
                .map_err(invalid)?,
            )
            .map_err(invalid)?;
        let target = ResidentNormalEnclosureSection::from_points(
            ResidentConstitutiveSection::integers(&raw)?,
            ResidentGrain(48),
        )?;
        let x = seed(s, &layout, 0);
        let (_, g) = s
            .body
            .observe_geometric_rows(&layout, x, &target, &held, &observed, 0, false)?;
        let plus = seed(s, &layout, 1);
        let minus = seed(s, &layout, -1);
        let plus_output = s.body.preview_geometric_rows(&layout, plus, &held)?;
        let lp = loss(plus_output.as_ref());
        let minus_output = s.body.preview_geometric_rows(&layout, minus, &held)?;
        let lm = loss(minus_output.as_ref());
        let central = (lp - lm) * Rat::from_integer(2048.into());
        let received = g.row(0)?.inspect()?;
        let error = (central + &received.center[0].real).abs();
        assert!(
            error < Rat::new(1.into(), 100000.into()),
            "paired directional error {error}, source radius {}",
            received.radius
        );
        assert!(received.radius >= Rat::zero());
        Ok(())
    })
    .unwrap();
}
