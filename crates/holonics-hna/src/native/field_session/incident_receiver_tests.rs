use super::*;
use crate::native::section_input::SymbolCurrentChart;
use holonic_engine::{
    ExactComplexWaveCurrent,
    codec_recovery::SymbolAlphabet,
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        BoundaryMaterialSeed, NativeNormalPrior, ResidentConstitutiveSection,
        ResidentNormalEnclosureSection, ResidentNormalMaterial,
    },
    resident_section::{ResidentGrain, ResidentSectionRest, ResidentSurface, SeriesAperture},
};
use num_rational::BigRational as Rat;

#[test]
fn response_aperture_refuses_overflow_without_trimming() {
    assert!(validate_response_len(4, 4).is_ok());
    assert!(validate_response_len(4, 5).is_err());
    assert!(validate_response_len(4, 0).is_err());
}

#[test]
#[ignore = "requires CUDA; native text receiver compares direct CE return without an extra softmax Jacobian"]
fn direct_ce_return_is_target_minus_probability_and_stages_bias_covector() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let chart = SymbolCurrentChart::declared(SymbolAlphabet::from_chars(&['a', 'b']).unwrap());
    let boundary = BoundaryMaterial::found(
        &surface,
        chart,
        1,
        1,
        ResidentGrain(16),
        BoundaryMaterialSeed::new(0x51, 16),
    )
    .unwrap();
    let mut receiver = IncidentTextReceiver::found(&surface, boundary).unwrap();
    let text_prior = NativeNormalPrior::from_coefficients(vec![
        vec![
            ExactComplexWaveCurrent::new(Rat::from_integer(1.into()), Rat::from_integer(1.into())),
            ExactComplexWaveCurrent::zero(),
        ],
        vec![
            ExactComplexWaveCurrent::new(
                Rat::from_integer(2.into()),
                Rat::from_integer((-1).into()),
            ),
            ExactComplexWaveCurrent::zero(),
        ],
    ])
    .unwrap();
    receiver.text = ResidentNormalMaterial::found_features_with_prior(
        &surface,
        2,
        2,
        ResidentGrain(16),
        text_prior,
    )
    .unwrap();
    let support_prior = NativeNormalPrior::from_coefficients(vec![
        vec![ExactComplexWaveCurrent::zero(); 2],
        vec![ExactComplexWaveCurrent::zero(); 2],
    ])
    .unwrap();
    receiver.support = ResidentNormalMaterial::found_features_with_prior(
        &surface,
        2,
        2,
        ResidentGrain(16),
        support_prior,
    )
    .unwrap();
    let raw = surface
        .mount_section_rest(
            &ResidentSectionRest::found(1, 2, ResidentGrain(0), 64, vec![(0, 0), (0, 0)]).unwrap(),
        )
        .unwrap();
    let boundary_rows = ResidentNormalEnclosureSection::from_points(
        ResidentConstitutiveSection::integers(&raw).unwrap(),
        ResidentGrain(16),
    )
    .unwrap();
    let forward = receiver.forward(&boundary_rows, SeriesAperture(1)).unwrap();
    let live_before = receiver.text.inspect().unwrap();
    let returned = receiver
        .compare(&forward, &[1], 1, SeriesAperture(16), 0)
        .unwrap();
    let live_after = receiver.text.inspect().unwrap();
    assert_eq!(live_before.cross_source, live_after.cross_source);
    let q = returned
        .text_covector
        .unwrap()
        .row(0)
        .unwrap()
        .inspect()
        .unwrap();
    assert_eq!(q.center[0].real, Rat::new(1.into(), 2.into()));
    assert_eq!(q.center[0].imaginary, Rat::from_integer(1.into()));
    assert!(q.radius <= Rat::new(1.into(), (1i64 << 16).into()));
    assert_ne!(q.center[0].real, Rat::new(1.into(), 4.into()));
    let staged = returned.successor.text.unwrap().inspect().unwrap();
    assert_eq!(
        staged.cross_source[0][1].real,
        Rat::new((-1).into(), 2.into())
    );
    assert_eq!(staged.cross_source[1][1].real, Rat::new(1.into(), 2.into()));
    let support = returned.successor.support.inspect().unwrap();
    assert_eq!(
        support.cross_source[0][1].real,
        Rat::new((-1).into(), 2.into())
    );
    assert_eq!(
        support.cross_source[1][1].real,
        Rat::new(1.into(), 2.into())
    );
}

#[test]
#[ignore = "requires CUDA; nominal receiver selection stays ordered when normalized enclosure midpoints tie"]
fn nominal_text_and_support_selection_use_logits_under_broad_radius() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let chart = SymbolCurrentChart::declared(SymbolAlphabet::from_chars(&['a', 'b']).unwrap());
    let boundary = BoundaryMaterial::found(
        &surface,
        chart,
        1,
        2,
        ResidentGrain(16),
        BoundaryMaterialSeed::new(0x51, 16),
    )
    .unwrap();
    let mut receiver = IncidentTextReceiver::found(&surface, boundary).unwrap();
    let text_prior = NativeNormalPrior::from_coefficients(vec![
        vec![ExactComplexWaveCurrent::zero(); 2],
        vec![
            ExactComplexWaveCurrent::new(Rat::from_integer(1.into()), Rat::from_integer(0.into())),
            ExactComplexWaveCurrent::zero(),
        ],
    ])
    .unwrap();
    receiver.text = ResidentNormalMaterial::found_features_with_prior(
        &surface,
        2,
        2,
        ResidentGrain(16),
        text_prior,
    )
    .unwrap();
    let support_prior = NativeNormalPrior::from_coefficients(vec![
        vec![ExactComplexWaveCurrent::zero(); 3],
        vec![
            ExactComplexWaveCurrent::zero(),
            ExactComplexWaveCurrent::new(Rat::from_integer(1.into()), Rat::from_integer(0.into())),
            ExactComplexWaveCurrent::zero(),
        ],
        vec![ExactComplexWaveCurrent::zero(); 3],
    ])
    .unwrap();
    receiver.support = ResidentNormalMaterial::found_features_with_prior(
        &surface,
        3,
        3,
        ResidentGrain(16),
        support_prior,
    )
    .unwrap();
    let scale = 1i64 << 16;
    let packet = ResidentSectionRest::found(
        2,
        6,
        ResidentGrain(0),
        64,
        vec![
            (scale, scale),
            (0, 0),
            (0, 0),
            (0, 0),
            (0, 0),
            (0, 0),
            (scale, scale),
            (0, 0),
            (0, 0),
            (0, 0),
            (100 * scale, 100 * scale),
            (0, 0),
        ],
    )
    .unwrap();
    let boundary_rows =
        ResidentNormalEnclosureSection::remount(&surface, packet, 2, 2, ResidentGrain(16)).unwrap();
    let before = surface.census().section_read_outs;
    let rows = boundary_rows.inspect_rows().unwrap();
    assert_eq!(surface.census().section_read_outs, before + 1);
    assert_eq!(rows[0].radius, Rat::from_integer(0.into()));
    assert_eq!(rows[1].radius, Rat::from_integer(100.into()));
    assert_eq!(rows[0].center[0].real, Rat::from_integer(1.into()));
    let before = surface.census().section_read_outs;
    let radii = boundary_rows.inspect_radii().unwrap();
    assert_eq!(surface.census().section_read_outs, before + 1);
    assert_eq!(
        radii,
        rows.iter()
            .map(|row| row.radius.clone())
            .collect::<Vec<_>>()
    );
    let forward = receiver.forward(&boundary_rows, SeriesAperture(1)).unwrap();
    let centre = forward
        .text_face
        .participation()
        .row(1)
        .unwrap()
        .inspect()
        .unwrap();
    assert_eq!(
        centre.center[0], centre.center[1],
        "the normalized midpoint ties"
    );
    let text = receiver.select_text_receipts(&forward).unwrap();
    let support = receiver.select_support_receipt(&forward).unwrap();
    assert_eq!(text[0].selected, 1);
    assert_eq!(text[1].selected, 1);
    assert_eq!(support.selected, 1);
    assert!(text[0].robust);
    assert!(!text[1].robust);
    assert!(!support.robust);
}
