use super::*;
use crate::native::section_input::SymbolCurrentChart;
use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::{
    codec_recovery::SymbolAlphabet,
    native_ecology::constitutive_fibre::{
        BoundaryMaterialSeed, ResidentConstitutiveSection, ResidentNormalEnclosureSection,
    },
    resident_section::{ResidentGrain, ResidentSectionRest, ResidentSurface, SeriesAperture},
};

fn boundary<'c>(surface: &'c ResidentSurface<'c>) -> BoundaryMaterial<'c> {
    BoundaryMaterial::found(
        surface,
        SymbolCurrentChart::declared(SymbolAlphabet::from_chars(&['a', 'b']).unwrap()),
        1,
        1,
        ResidentGrain(16),
        BoundaryMaterialSeed::new(0x51, 16),
    )
    .unwrap()
}

fn phase_rows<'c>(
    surface: &'c ResidentSurface<'c>,
    rows: usize,
) -> ResidentNormalEnclosureSection<'c> {
    let scale = 1_i64 << 16;
    let values = (0..rows)
        .flat_map(|row| {
            [
                (((row as i64) + 1) * scale, ((row as i64) + 1) * scale),
                (((row as i64) + 2) * scale, ((row as i64) + 2) * scale),
                (scale, scale),
            ]
        })
        .collect();
    let raw = surface
        .mount_section_rest(
            &ResidentSectionRest::found(rows, 3, ResidentGrain(0), 64, values).unwrap(),
        )
        .unwrap();
    ResidentNormalEnclosureSection::from_points(
        ResidentConstitutiveSection::rationals(&raw).unwrap(),
        ResidentGrain(16),
    )
    .unwrap()
}

#[test]
#[ignore = "requires CUDA; phase rows share one support normal chart and return packed boundary covectors"]
fn phase_receiver_uses_aperture_rows_with_one_shared_support_parameter_chart() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut receiver = GeneratorTextReceiver::found(&surface, boundary(&surface)).unwrap();
    let phases = phase_rows(&surface, 3);
    let forward = receiver.forward(&phases, SeriesAperture(16)).unwrap();
    assert_eq!(forward.text_features.rows(), 3);
    assert_eq!(forward.support_features.rows(), 3);
    assert_eq!(forward.text_logits.rows(), 3);
    assert_eq!(forward.support_logits.rows(), 3);
    assert_eq!(forward.support_logits.components(), 4);
    assert_eq!(receiver.inner().support_material().targets(), 2);
    assert_eq!(receiver.select_text(&forward).unwrap().len(), 2);
    assert_eq!(receiver.select_stop(&forward).unwrap().len(), 3);
    let stop = receiver.choose_stop(&forward).unwrap();
    assert!(stop <= 2);

    let frozen_before = receiver
        .compare(&forward, &[0, 1], SeriesAperture(16), 4)
        .unwrap()
        .boundary_covector
        .inspect_rows()
        .unwrap();
    let more = receiver
        .forward(&phase_rows(&surface, 5), SeriesAperture(16))
        .unwrap();
    assert_eq!(more.support_features.rows(), 5);
    assert_eq!(receiver.inner().support_material().source_complex(), 2);
    assert_eq!(receiver.inner().support_material().targets(), 2);
    let empty = receiver
        .compare(&forward, &[], SeriesAperture(16), 4)
        .unwrap();
    assert!(empty.text_covector.is_none());
    assert!(empty.successor.text.is_none());
    receiver.publish(empty.successor);

    let returned = receiver
        .compare(&forward, &[0, 1], SeriesAperture(16), 4)
        .unwrap();
    assert!(
        returned
            .text_covector
            .as_ref()
            .is_some_and(|v| v.rows() == 2)
    );
    assert_eq!(
        returned.boundary_covector.inspect_rows().unwrap(),
        frozen_before
    );
    assert_eq!(returned.boundary_covector.rows(), 1);
    assert_eq!(returned.boundary_covector.components(), 6);
    assert!(returned.successor.text.is_some());
    assert!(returned.successor.text_cohorts.is_empty());
    receiver.publish(returned.successor);
    assert_eq!(receiver.inner().support_material().targets(), 2);
}

#[test]
#[ignore = "requires CUDA; receiver constructor chart validation"]
fn phase_receiver_rejects_single_row_and_wrong_boundary_aperture() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let bad_boundary = BoundaryMaterial::found(
        &surface,
        SymbolCurrentChart::declared(SymbolAlphabet::from_chars(&['a', 'b']).unwrap()),
        1,
        2,
        ResidentGrain(16),
        BoundaryMaterialSeed::new(0x51, 16),
    )
    .unwrap();
    assert!(GeneratorTextReceiver::found(&surface, bad_boundary).is_err());
}
