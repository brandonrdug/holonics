use super::*;
use crate::dimensional_wave::ExactWavePhaseTransport;
use crate::embedding_fiber::ResidentReadout;
use num_traits::Zero;

fn enclosure<'c>(
    surface: &'c ResidentSurface<'c>,
    centers: &[[i64; 2]],
    radii: &[i64],
    grain: ResidentGrain,
) -> ResidentNormalEnclosureSection<'c> {
    assert_eq!(centers.len(), radii.len());
    let scale = 1i128 << grain.0;
    let values = centers
        .iter()
        .zip(radii)
        .flat_map(|(center, radius)| {
            [
                i128::from(center[0]) * scale,
                i128::from(center[1]) * scale,
                i128::from(*radius) * scale,
            ]
            .into_iter()
            .flat_map(|word| [word as i64, (word >> 64) as i64])
            .map(|word| (word, word))
        })
        .collect();
    let width = 2;
    let section = surface
        .mount_section_rest(
            &ResidentSectionRest::found(
                centers.len(),
                2 * (width + 1),
                ResidentGrain(0),
                64,
                values,
            )
            .unwrap(),
        )
        .unwrap();
    ResidentNormalEnclosureSection::from_resident(surface, section, centers.len(), width, grain)
        .unwrap()
}

fn dot(left: &NativeFieldCurrentBall, right: &NativeFieldCurrentBall) -> Rat {
    left.center
        .iter()
        .zip(&right.center)
        .map(|(left, right)| &left.real * &right.real + &left.imaginary * &right.imaginary)
        .sum()
}

#[test]
#[ignore = "requires CUDA; one resident row table concatenates every enclosure packet and radius"]
fn concatenate_rows_retains_every_row_and_radius() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let grain = ResidentGrain(8);
    let first = enclosure(&surface, &[[1, 2], [3, 4]], &[2, 3], grain);
    let second = enclosure(&surface, &[[5, 6]], &[7], grain);
    let joined = ResidentNormalEnclosureSection::concatenate_rows(&[&first, &second]).unwrap();
    assert_eq!(joined.rows(), 3);
    for (row, expected) in [([1, 2], 2), ([3, 4], 3), ([5, 6], 7)]
        .into_iter()
        .enumerate()
    {
        let actual = joined.row(row).unwrap().inspect().unwrap();
        assert_eq!(
            actual.center[0].real,
            Rat::from_integer(expected.0[0].into())
        );
        assert_eq!(
            actual.center[0].imaginary,
            Rat::from_integer(expected.0[1].into())
        );
        assert_eq!(actual.radius, Rat::from_integer(expected.1.into()));
    }
}

#[test]
#[ignore = "requires CUDA; phased gather and transpose retain repeated-address adjoint equality"]
fn phased_gather_and_transpose_match_exact_inner_product() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let grain = ResidentGrain(8);
    let source = enclosure(&surface, &[[1, 2], [3, 4]], &[0, 0], grain);
    let probe = enclosure(&surface, &[[5, 6], [7, 8], [9, 10]], &[0, 0, 0], grain);
    let addresses = [1, 0, 1];
    let phases = vec![
        ExactWavePhaseTransport::new(Rat::from_integer(0.into()), Rat::from_integer(1.into()))
            .unwrap(),
        ExactWavePhaseTransport::new(Rat::from_integer((-1).into()), Rat::from_integer(0.into()))
            .unwrap(),
        ExactWavePhaseTransport::identity(),
    ];
    let gathered = source.gather_phase_rows(&addresses, &phases, 2).unwrap();
    let transposed = probe.scatter_phase_adjoint(&addresses, &phases, 2).unwrap();
    let left: Rat = (0..3)
        .map(|row| {
            dot(
                &gathered.row(row).unwrap().inspect().unwrap(),
                &probe.row(row).unwrap().inspect().unwrap(),
            )
        })
        .sum();
    let right: Rat = (0..2)
        .map(|row| {
            dot(
                &source.row(row).unwrap().inspect().unwrap(),
                &transposed.row(row).unwrap().inspect().unwrap(),
            )
        })
        .sum();
    assert_eq!(left, right);
}

#[test]
#[ignore = "requires CUDA; held refinement preserves held coordinates and phase transpose coefficients"]
fn held_refinement_preserves_held_coordinates() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let grain = ResidentGrain(8);
    let generated = enclosure(&surface, &[[4, 2]], &[3], grain);
    let seed = enclosure(&surface, &[[1, 3]], &[5], grain);
    let refined = generated.held_refinement(&seed, &[true], 4).unwrap();
    let actual = refined.row(0).unwrap().inspect().unwrap();
    assert_eq!(actual.center[0].real, Rat::from_integer(1.into()));
    assert_eq!(actual.center[0].imaginary, Rat::from_integer(3.into()));
    assert_eq!(actual.radius, Rat::from_integer(5.into()));
    let free = generated
        .held_refinement(&seed, &[false], 2)
        .unwrap()
        .row(0)
        .unwrap()
        .inspect()
        .unwrap();
    assert_eq!(free.center[0].real, Rat::new(7.into(), 4.into()));
    assert_eq!(free.center[0].imaginary, Rat::new(11.into(), 4.into()));
    assert_eq!(free.radius, Rat::new(9.into(), 2.into()));
}

#[test]
#[ignore = "requires CUDA; enclosed bilinear features and both pullback arms agree with exact centre controls"]
fn enclosed_bilinear_features_and_pullback_match_controls() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let grain = ResidentGrain(8);
    let source = enclosure(&surface, &[[1, 0]], &[1], grain);
    let condition = enclosure(&surface, &[[2, 0]], &[1], grain);
    let features = source.bilinear_enclosed_features(&condition).unwrap();
    let feature_ball = features.row(0).unwrap().inspect().unwrap();
    assert_eq!(feature_ball.center[0].real, Rat::from_integer(1.into()));
    assert_eq!(feature_ball.center[1].real, Rat::from_integer(2.into()));
    assert_eq!(feature_ball.center[2].real, Rat::from_integer(2.into()));
    assert!(feature_ball.radius > Rat::zero());

    let covector = {
        let scale = 1i128 << grain.0;
        let values = [1i128, 0, 2, 0, 3, 0, 1]
            .into_iter()
            .flat_map(|value| {
                let word = value * scale;
                [word as i64, (word >> 64) as i64].map(|word| (word, word))
            })
            .collect();
        let section = surface
            .mount_section_rest(
                &ResidentSectionRest::found(1, 14, ResidentGrain(0), 64, values).unwrap(),
            )
            .unwrap();
        ResidentNormalEnclosureSection::from_resident(&surface, section, 1, 6, grain).unwrap()
    };
    let (source_pullback, condition_pullback) = source
        .bilinear_enclosed_pullback(&condition, &covector)
        .unwrap();
    let source_ball = source_pullback.row(0).unwrap().inspect().unwrap();
    let condition_ball = condition_pullback.row(0).unwrap().inspect().unwrap();
    assert_eq!(source_ball.center[0].real, Rat::from_integer(7.into()));
    assert_eq!(condition_ball.center[0].real, Rat::from_integer(5.into()));
    assert!(source_ball.radius > Rat::zero());
    assert!(condition_ball.radius > Rat::zero());
}

#[test]
#[ignore = "requires CUDA; a trained resident normal map and its enclosure transpose preserve the exact inner product"]
fn trained_normal_map_transpose_matches_inner_product() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let grain = ResidentGrain(8);
    let raw_source = surface
        .mount_section_rest(
            &ResidentSectionRest::found(1, 2, ResidentGrain(0), 64, vec![(1, 1), (0, 0)]).unwrap(),
        )
        .unwrap();
    let raw_observed = surface
        .mount_section_rest(
            &ResidentSectionRest::found(1, 2, ResidentGrain(0), 64, vec![(2, 2), (0, 0)]).unwrap(),
        )
        .unwrap();
    let mut material = ResidentNormalMaterial::found_features(&surface, 1, 1, grain).unwrap();
    material
        .receive_section(
            ResidentConstitutiveSection::integers(&raw_source).unwrap(),
            ResidentConstitutiveSection::integers(&raw_observed).unwrap(),
        )
        .unwrap();
    let view = material.retained_view();
    let source = ResidentConstitutiveSection::integers(&raw_source).unwrap();
    let forward = view.read_applied_section(source).unwrap();
    let covector = enclosure(&surface, &[[3, 0]], &[1], grain);
    let transpose = view.pull_back_enclosed_section(&covector).unwrap();
    let left = dot(
        &forward.row(0).unwrap().inspect().unwrap(),
        &covector.row(0).unwrap().inspect().unwrap(),
    );
    let right = transpose.row(0).unwrap().inspect().unwrap().center[0]
        .real
        .clone();
    assert_eq!(left, right);
}

#[test]
#[ignore = "requires CUDA/sanitizer; row flags use a full SLOT_WORDS receipt on a non-warp-sized gather"]
fn phased_gather_large_signed_rows_preserves_row_receipts() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let rows = 1231usize;
    let centers: Vec<[i64; 2]> = (0..rows).map(|i| [i as i64, -(i as i64)]).collect();
    let radii = vec![1; rows];
    let source = enclosure(&surface, &centers, &radii, ResidentGrain(8));
    let addresses: Vec<usize> = (0..rows).rev().collect();
    let minus = ExactWavePhaseTransport::new(Rat::from_integer((-1).into()), Rat::zero()).unwrap();
    let gathered = source
        .gather_phase_rows(&addresses, &vec![minus; rows], 2)
        .unwrap();
    assert_eq!(gathered.rows(), rows);
    assert_eq!(
        gathered.row(0).unwrap().inspect().unwrap().radius,
        Rat::from_integer(1.into())
    );
}
