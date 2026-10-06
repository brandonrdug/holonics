//! Exact device parity of the existing located-transport source owner, not scientific validation.
//! The fixture is the already admitted 2026100962 terrain from the located encoding's unit test.
//! Only its emitted cells enter location/encoding; no generating advance or key enters ingestion.

use holonics::compression::keys::transport::{CarryHelix, SteppedTerrain, TransportLocation};
use holonics::geometry::RatVec3;
use holonics::geometry::screw::ScrewGenerator;
use holonics::hnn::encoding::{Encoded, Encoding, PassageChart};
use holonics::hnn::field::{ContactDeclaration, CribDeclaration, ReceiverDeclaration};
use holonics::hnn::{Current, Field, FieldDeclaration, RingDeclaration, SourceMoment};
use holonics::holarchy::terrain::Draw;
use holonics::ratio::{integer, rat};
use holonics_cuda::hnn::{Card, ResidentMoment};
use num_bigint::BigInt;

fn field() -> Field {
    let rings = [2, 3, 5]
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
            // The five encoded classes inject into the period-five source; the other rings are
            // the located helix's hidden clock, not folded source ports.
            sources: vec![2],
            offsets: vec![1, 3],
            alphabet: 5,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![ReceiverDeclaration {
                ring: 2,
                aperture: 5,
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
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn located_ingest_keeps_the_actual_phase_winding_and_offset_counts_across_tiles() {
    let field = field();
    let helix = CarryHelix::new(vec![2, 3, 5]).unwrap();
    let mut draw = Draw::new(2_026_100_962);
    let terrain = SteppedTerrain::draw(helix.clone(), &mut draw);
    // Preserve the existing fixture's draw order: every opening once, two joint turns each.
    let mut keys: Vec<u64> = (0..helix.period()).collect();
    let passages: Vec<Vec<usize>> = (0..helix.period())
        .map(|_| terrain.passage(keys.remove(draw.below(keys.len())), 60))
        .collect();
    let location = TransportLocation::locate(helix, 5, &passages).unwrap();
    let chart = PassageChart::located(&location, &passages).unwrap();
    let encoding = Encoding::found(&chart).unwrap();
    let encoded = Encoded::through(&encoding, &chart, &field, &passages).unwrap();
    assert!(
        encoded.iter().any(|passage| {
            (0..passage.len()).any(|at| passage.advance(at).unwrap().iter().any(|&digit| digit > 1))
        }),
        "the fixture must exercise a located digit beyond the identity lock fit"
    );
    let card = Card::open(0).expect("a CUDA card with the HNN kernels built");
    for lanes in [Some(1), Some(2), Some(32), None] {
        // The nonzero high winding is invisible to the phase wire and must survive every
        // receipt. This is an exact interior clock read, not a reset-state surrogate.
        let turn = BigInt::from(1u64) << 80usize;
        let opening =
            Current::at(&field, vec![&turn * 2 + 1, &turn * 3 + 2, &turn * 5 + 4]).unwrap();
        let mut current = opening.clone();
        let mut host = SourceMoment::open(&field, &opening);
        let mut device = ResidentMoment::open(&card, &field, &opening).unwrap();
        let empty = encoded[0].part(0..0).unwrap();
        assert_eq!(
            device.ingest_in(&empty, lanes).unwrap().0,
            host.ingest(&field, &mut current, &empty).unwrap()
        );
        assert_eq!(device.lift(), opening.lift());
        let mut carries = 0usize;
        for passage in encoded.iter().take(2) {
            let mut fed = 0;
            // One request has an incomplete last tile; the next continues the same moment,
            // including its offsets, instead of reopening at rest.
            while fed < passage.len() {
                let end = (fed + 41).min(passage.len());
                let part = passage.part(fed..end).unwrap();
                let expected = host.ingest(&field, &mut current, &part).unwrap();
                let (actual, _) = device.ingest_in(&part, lanes).unwrap();
                assert_eq!(actual, expected);
                assert_eq!(device.lift(), current.lift());
                carries += usize::from(actual.carry_out);
                fed += actual.cells;
                assert!(actual.cells > 0);
                let phases = device.phases().unwrap();
                for (g, &phase) in phases.iter().enumerate() {
                    assert_eq!(u64::from(phase), current.phase(&field, g).unwrap());
                }
            }
        }
        assert!(carries > 1);
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
    }
}
