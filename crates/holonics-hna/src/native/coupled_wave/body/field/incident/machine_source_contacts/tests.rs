use super::*;
use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::native_ecology::constitutive_fibre::{
    ResidentConstitutiveSection, ResidentNormalEnclosureSection,
};
use holonic_engine::resident_section::{ResidentGrain, ResidentSectionRest, ResidentSurface};
use num_traits::Zero;
use std::rc::Rc;

#[test]
fn contact_kind_wire_roundtrip_retains_direction_and_semantics() {
    let contact = GeneratorSourceContact {
        from: 2,
        to: 5,
        kind: GeneratorSourceContactKind::RecordedReply,
    };
    let encoded = serde_json::to_string(&contact).unwrap();
    let decoded: GeneratorSourceContact = serde_json::from_str(&encoded).unwrap();
    assert_eq!(decoded, contact);
}

#[test]
#[ignore = "requires CUDA; validates N×G×C layout, empty kinds, multiplicity, and full adjoint"]
fn resident_contact_layout_preserves_empty_kind_and_reverses_full_source_chart() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let rows = 3usize;
    let components = 12usize;
    let mut intervals = Vec::new();
    for row in 0..rows {
        for component in 0..components {
            let value = ((row * 100 + 1) * (component + 1)) as i64;
            intervals.push((value, value));
        }
        intervals.push((1, 1));
    }
    let raw = surface
        .mount_section_rest(
            &ResidentSectionRest::found(rows, components + 1, ResidentGrain(0), 64, intervals)
                .unwrap(),
        )
        .unwrap();
    let encoded = Rc::new(
        ResidentNormalEnclosureSection::from_points(
            ResidentConstitutiveSection::rationals(&raw).unwrap(),
            ResidentGrain(24),
        )
        .unwrap(),
    );
    let kinds = [
        GeneratorSourceContactKind::IntraPart,
        GeneratorSourceContactKind::DirectJoin,
    ];
    let contacts = [
        GeneratorSourceContact {
            from: 0,
            to: 2,
            kind: GeneratorSourceContactKind::IntraPart,
        },
        GeneratorSourceContact {
            from: 1,
            to: 2,
            kind: GeneratorSourceContactKind::IntraPart,
        },
        GeneratorSourceContact {
            from: 0,
            to: 2,
            kind: GeneratorSourceContactKind::IntraPart,
        },
    ];
    let chart = GeneratorSourceContacts::new(encoded, &[1, 3], 4, &kinds, &contacts)
        .unwrap()
        .unwrap();
    let event = chart.output(2).unwrap();
    assert_eq!(event.rows(), 4);
    assert_eq!(event.components(), 24);
    let faces = event.inspect_rows().unwrap();
    for site in 0..4 {
        let expected = (0..12)
            .map(|channel| {
                let value = if channel < 6 && (site == 1 || site == 3) {
                    500 * (channel + 1 + if site == 3 { 6 } else { 0 }) as i64
                } else {
                    0
                };
                holonic_engine::ExactComplexWaveCurrent::new(
                    relational_geometry::Rat::from_integer(value.into()),
                    relational_geometry::Rat::zero(),
                )
            })
            .collect::<Vec<_>>();
        assert!(faces[site].contains(&expected));
    }
    let event_outputs = (0..rows)
        .map(|event| chart.output(event).unwrap())
        .collect::<Vec<_>>();
    let event_refs = event_outputs.iter().collect::<Vec<_>>();
    let all = ResidentNormalEnclosureSection::concatenate_rows(&event_refs).unwrap();
    let returned = chart.pull_back(&all).unwrap();
    assert_eq!(returned.rows(), rows);
    assert_eq!(returned.components(), components);
    for (row, factor) in [-1000i64, -500, 1500].into_iter().enumerate() {
        let expected = (0..6)
            .map(|coordinate| {
                holonic_engine::ExactComplexWaveCurrent::new(
                    relational_geometry::Rat::from_integer((factor * (2 * coordinate + 1)).into()),
                    relational_geometry::Rat::from_integer((factor * (2 * coordinate + 2)).into()),
                )
            })
            .collect::<Vec<_>>();
        assert!(
            returned
                .row(row)
                .unwrap()
                .inspect()
                .unwrap()
                .contains(&expected)
        );
    }
}
