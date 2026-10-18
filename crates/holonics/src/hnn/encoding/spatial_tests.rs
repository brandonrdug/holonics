//! Receiver-relative retention tests: an exterior image decoder does not certify its moment.
use super::observed::PairedObservation;
use crate::geometry::spatial::{Grid, PlacedRaster, Raster};
use crate::hnn::constitution::Constitution;
use crate::hnn::field::{Current, Field, FieldDeclaration};
use crate::hnn::moment::{PairPort, SourceMoment};
use crate::hnn::paired::{PairedCarrier, PairingDeclaration};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer};

fn fixture(offsets: Vec<usize>) -> (Field, Constitution, PairedObservation) {
    let mut declaration = FieldDeclaration::campaign_one(1 << 17);
    declaration.alphabet = 4;
    declaration.sources = vec![0, 1];
    declaration.offsets = offsets;
    declaration.receivers[0].aperture = 1;
    declaration.receivers[0].depth = 2;
    declaration.lattice.clear();
    let field = Field::declare(declaration.by_lattice_rule()).unwrap();
    let pairing = PairingDeclaration::Family {
        table: vec![(0, 1), (1, 0), (2, 3), (3, 2)],
    };
    let mut material = Constitution::initial(&field, 1 << 40).unwrap();
    for &ring in field.sources() {
        let width = field.ring(ring).width();
        let free = ExactRatMatrix::shaped(
            width,
            4,
            (0..width)
                .map(|r| {
                    (0..4)
                        .map(|c| integer(i64::from((r == 2 && c == 0) || (r == 4 && c == 2))))
                        .collect()
                })
                .collect(),
        )
        .unwrap();
        let source = PairedCarrier::complete_port(&field, ring, &pairing, &free).unwrap();
        let carrier = PairedCarrier::admit(&field, ring, &pairing, &source).unwrap();
        material = material
            .with_symmetric_source(ring, source, carrier.symmetry())
            .unwrap();
    }
    let boundary = PairedObservation::admit(&field, &material, &pairing).unwrap();
    (field, material, boundary)
}
fn image(ones: &[usize]) -> Raster {
    Raster::new(
        Grid::new(4, 4).unwrap(),
        (0..16).map(|i| u8::from(ones.contains(&i))).collect(),
    )
    .unwrap()
}
fn ingest(
    field: &Field,
    material: &Constitution,
    boundary: &PairedObservation,
    image: &Raster,
) -> (SourceMoment, Current) {
    let mut current = Current::at_rest(field);
    let placed =
        PlacedRaster::encode(image, [field.ring(0).period(), field.ring(1).period()]).unwrap();
    assert_eq!(placed.decode().unwrap(), *image);
    let encoded = boundary.encode_raster(field, &current, &placed).unwrap();
    let mut moment = SourceMoment::open_with(field, &current, material).unwrap();
    let mut fed = 0;
    while fed < encoded.len() {
        let taken = moment
            .ingest(
                field,
                &mut current,
                &encoded.part(fed..encoded.len()).unwrap(),
            )
            .unwrap();
        assert!(taken.cells > 0);
        fed += taken.cells;
    }
    (moment, current)
}
fn first_equal(field: &Field, left: &SourceMoment, right: &SourceMoment) -> bool {
    field.sources().iter().all(|&g| {
        (0..field.ring(g).period() as usize)
            .all(|p| left.phase_counts(g, p).unwrap() == right.phase_counts(g, p).unwrap())
    })
}
fn pairs_equal(field: &Field, left: &SourceMoment, right: &SourceMoment) -> bool {
    field.sources().iter().all(|&g| {
        field.offsets().iter().all(|&offset| {
            (0..field.ring(g).period() as usize).all(|p| {
                left.offset_counts(g, offset, p).unwrap()
                    == right.offset_counts(g, offset, p).unwrap()
            })
        })
    })
}

#[test]
fn axis_marginals_and_axial_pairs_do_not_certify_full_image_retention() {
    // Two different interior diagonal arrangements; same row/column populations and boundaries.
    let left = image(&[5, 10]);
    let right = image(&[6, 9]);
    assert_ne!(left, right);
    let (field, material, boundary) = fixture(vec![1, 2, 8]);
    let (l, lc) = ingest(&field, &material, &boundary, &left);
    let (r, rc) = ingest(&field, &material, &boundary, &right);
    assert_eq!(lc, rc);
    assert!(first_equal(&field, &l, &r));
    assert!(pairs_equal(&field, &l, &r));
    assert_eq!(
        l, r,
        "the entire retained moment aliases this pair, not just its first marginals"
    );
    assert_eq!(
        l.open_storage(&field, &material, &lc).unwrap(),
        r.open_storage(&field, &material, &rc).unwrap()
    );
    println!(
        "spatial retention: distinct 4x4 interior diagonal swap aliases at axial offsets [1,2,8], including actual native storage"
    );
}

#[test]
fn existing_diagonal_pair_port_separates_the_alias_without_a_joint_period_matrix() {
    let left = image(&[5, 10]);
    let right = image(&[6, 9]);
    let (field, material, boundary) = fixture(vec![1, 2, 6, 8, 10]);
    let (l, lc) = ingest(&field, &material, &boundary, &left);
    let (r, rc) = ingest(&field, &material, &boundary, &right);
    assert!(first_equal(&field, &l, &r));
    assert!(
        !pairs_equal(&field, &l, &r),
        "diagonal offsets retain a reached distinction"
    );
    // Initially all pair outputs are zero: retained evidence is not automatically expressed.
    assert_eq!(
        l.open_storage(&field, &material, &lc).unwrap(),
        r.open_storage(&field, &material, &rc).unwrap()
    );
    // A declared TEST receiver of the (1,1) diagonal conjunction, not a digit classifier or
    // learned coefficient. This existing tensor PairPort proves the retained distinction reaches
    // the actual native injection; its future learned value is left to deposition.
    let width = field.ring(0).width();
    let mut outputs = vec![vec![integer(0); width]; width];
    outputs[0][0] = integer(1);
    let mut reads: Vec<Vec<Rat>> = vec![vec![integer(0); 4]; width];
    reads[0][1] = integer(1);
    let pair = PairPort::new(outputs, reads.clone(), reads).unwrap();
    let reading = material.with_pair(0, 10, pair).unwrap();
    assert_ne!(
        l.open_storage(&field, &reading, &lc).unwrap(),
        r.open_storage(&field, &reading, &rc).unwrap()
    );
    println!(
        "spatial retention: diagonal offsets [6,10] separate retained counts; existing PairPort expresses the difference at native storage; zero initial pair outputs do not"
    );
}
