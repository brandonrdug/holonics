//! Exact occurrence-placement host/GPU parity, separate from the MNIST learning claim.
use holonics::geometry::{RatVec3, screw::ScrewGenerator};
use holonics::hnn::constitution::Constitution;
use holonics::hnn::encoding::{observed::PairedObservation, placement::OccurrencePlacement};
use holonics::hnn::field::{ContactDeclaration, CribDeclaration, ReceiverDeclaration};
use holonics::hnn::paired::{PairedCarrier, PairingDeclaration};
use holonics::hnn::{Current, Field, FieldDeclaration, RingDeclaration, SourceMoment};
use holonics::ratio::{integer, rat};
use holonics_cuda::hnn::{Card, ResidentMoment};
use num_bigint::BigInt;
fn field() -> Field {
    let rings = [5, 7, 11]
        .into_iter()
        .map(|period| RingDeclaration {
            period,
            screw: ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
            placements: (0..period)
                .map(|node| FieldDeclaration::quarter_turn(node, period))
                .collect(),
            lock: vec![0],
            reflector: (0..period)
                .map(|p| ((period - p) % period) as usize)
                .collect(),
            admittance: integer(2),
            initial: 0,
        })
        .collect();
    Field::declare(
        FieldDeclaration {
            rings,
            // [agent-inferred, adoption, October 5] `Field::declare` reaches every ring from a
            // source ring: the helix's rings joined in a chain on their common nodes. The moment's
            // ingest reads no contact.
            contacts: [(0usize, 1usize, 2usize), (1, 2, 3)]
                .into_iter()
                .map(|(from, to, nodes)| ContactDeclaration {
                    from,
                    to,
                    channel: (0..nodes).map(|node| (node, node)).collect(),
                    admittance: integer(2),
                    exponent: integer(0),
                })
                .collect(),
            loops: Vec::new(),
            sources: vec![0, 1],
            offsets: vec![1, 3],
            alphabet: 4,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![ReceiverDeclaration {
                ring: 2,
                aperture: 1,
                tolerance: rat(1, 16),
                depth: 2,
                prior: holonics::compression::landmark::context::StopPrior::half(),
                mass: 1,
                base: holonics::compression::landmark::context::BaseMeasure::Even,
                receiving_prior: 0,
            }],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 16,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .unwrap()
}

#[test]
fn occurrence_placement_keeps_repeated_intensity_sites_slices_and_winding_on_cuda() {
    let field = field();
    let pairing = PairingDeclaration::Family {
        table: vec![(0, 1), (1, 0), (2, 3), (3, 2)],
    };
    let mut material = Constitution::initial(&field, 1 << 40).unwrap();
    for &ring in field.sources() {
        let width = field.ring(ring).width();
        let free = holonics::ratio::linear::ExactRatMatrix::shaped(
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
    let turn = BigInt::from(1u64) << 80usize;
    let opening = Current::at(
        &field,
        field
            .rings()
            .iter()
            .map(|r| &turn * r.period() + r.period() - 1)
            .collect(),
    )
    .unwrap();
    let positions: Vec<_> = (0..420)
        .map(|at| vec![(at / 2) % 5, ((at / 2) / 5) % 7])
        .collect();
    let placement = OccurrencePlacement::at(&field, &opening, &positions).unwrap();
    // Every intensity class is identical; only occurrence placement changes.
    let encoded = boundary
        .encode_placed(&vec![0; positions.len()], &placement)
        .unwrap();
    assert_ne!(encoded.advance(1), encoded.advance(2));
    let card = Card::open(0).expect("a CUDA card with the occurrence-major kernel");
    let mut baseline = None;
    for lanes in [Some(1), Some(2), Some(32), None] {
        for chunk in [encoded.len(), 41] {
            let mut current = opening.clone();
            let mut host = SourceMoment::open(&field, &opening);
            let mut device = ResidentMoment::open(&card, &field, &opening).unwrap();
            let empty = encoded.part(0..0).unwrap();
            assert_eq!(
                device.ingest_in(&empty, lanes).unwrap().0,
                host.ingest(&field, &mut current, &empty).unwrap()
            );
            let mut fed = 0;
            let mut carries = 0;
            while fed < encoded.len() {
                let part = encoded.part(fed..(fed + chunk).min(encoded.len())).unwrap();
                let expected = host.ingest(&field, &mut current, &part).unwrap();
                let (actual, _) = device.ingest_in(&part, lanes).unwrap();
                assert_eq!(actual, expected);
                assert!(actual.cells > 0);
                fed += actual.cells;
                carries += usize::from(actual.carry_out);
                assert_eq!(device.lift(), current.lift());
                assert_eq!(current.lift(), placement.arrivals()[fed - 1]);
            }
            assert!(carries > 0);
            assert_eq!(device.cells(), host.cells());
            assert_eq!(device.window().unwrap(), host.window());
            let counts = device.counts().unwrap();
            for &ring in field.sources() {
                for phase in 0..field.ring(ring).period() as usize {
                    assert_eq!(
                        counts.phase_counts(ring, phase).unwrap(),
                        host.phase_counts(ring, phase).unwrap()
                    );
                    for &offset in field.offsets() {
                        assert_eq!(
                            counts.offset_counts(ring, offset, phase).unwrap(),
                            host.offset_counts(ring, offset, phase).unwrap()
                        );
                    }
                }
            }
            if let Some((ref saved_counts, ref saved_lift)) = baseline {
                assert_eq!(&counts, saved_counts);
                assert_eq!(current.lift(), saved_lift);
            } else {
                baseline = Some((counts, current.lift().to_vec()));
            }
        }
    }
}
