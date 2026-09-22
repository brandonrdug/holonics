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
use num_traits::{Signed, Zero};

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

fn phase_rows_shifted<'c>(
    surface: &'c ResidentSurface<'c>,
    rows: usize,
) -> ResidentNormalEnclosureSection<'c> {
    let scale = 1_i64 << 16;
    let values = (0..rows)
        .flat_map(|row| {
            [
                (((row as i64) + 3) * scale, ((row as i64) + 3) * scale),
                (-scale, -scale),
                (2 * scale, 2 * scale),
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
    // A target Holon read through the same receiver at shifted phase rows.
    let target = receiver
        .forward(&phase_rows_shifted(&surface, 3), SeriesAperture(16))
        .unwrap();
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
        .compare(
            &forward,
            Some(&target),
            &[0, 1],
            &[0, 0, 0],
            SeriesAperture(16),
            4,
        )
        .unwrap()
        .0
        .boundary_covector
        .inspect_rows()
        .unwrap();
    let more = receiver
        .forward(&phase_rows(&surface, 5), SeriesAperture(16))
        .unwrap();
    assert_eq!(more.support_features.rows(), 5);
    assert_eq!(receiver.inner().support_material().source_complex(), 2);
    assert_eq!(receiver.inner().support_material().targets(), 2);
    let (empty, empty_faces) = receiver
        .compare(&forward, None, &[], &[0, 0, 0], SeriesAperture(16), 4)
        .unwrap();
    assert!(empty_faces.text.is_none());
    assert_eq!(empty_faces.stop.rows(), 1);
    assert!(empty.text_covector.is_none());
    assert!(empty.successor.text.is_none());
    receiver.publish(empty.successor);

    let (returned, faces) = receiver
        .compare(
            &forward,
            Some(&target),
            &[0, 1],
            &[0, 0, 0],
            SeriesAperture(16),
            4,
        )
        .unwrap();
    // The ratio covector: real slot q - p, imaginary slot (1/2) q Delta at the target class,
    // zero on the unsupported class; the target Holon's phases differ from the produced ones.
    let text = faces.text.as_ref().unwrap();
    assert_eq!(faces.classes, 2);
    let covector = text.ratio_covector().unwrap().inspect_rows().unwrap();
    assert!(
        covector
            .iter()
            .enumerate()
            .any(|(row, c)| !c.center[[0usize, 1][row]].imaginary.is_zero())
    );
    for (row, class) in [0usize, 1].into_iter().enumerate() {
        assert!(covector[row].center[1 - class].imaginary.abs() <= covector[row].radius);
    }
    assert_eq!(text.read_phase().unwrap().len(), 2);
    assert_eq!(faces.stop.rows(), 3);
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
