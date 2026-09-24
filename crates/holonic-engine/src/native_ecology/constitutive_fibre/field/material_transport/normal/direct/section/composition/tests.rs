use super::*;
use crate::dimensional_wave::ExactWavePhaseTransport;
use crate::embedding_fiber::ResidentReadout;

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
    let transposed = probe.scatter_phase_adjoint(&addresses, &phases, 4).unwrap();
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
    assert!(transposed.row(2).unwrap().inspect().unwrap().center[0].is_zero());
    assert!(transposed.row(3).unwrap().inspect().unwrap().center[0].is_zero());
}
