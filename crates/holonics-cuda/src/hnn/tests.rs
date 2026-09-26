//! The resident HNN's tests. The fast tests prove the host-side laws (the lattice coordinates and
//! the layouts derived from a census) without a card. The parity tests are `#[ignore]`: each runs
//! a kernel family on the card and requires exact equality with its host owner, refusals
//! included. Run them alone on the card:
//!
//! ```text
//! flock .local/gpu.lock cargo test -p holonics-cuda -- --include-ignored --test-threads=1
//! ```

use std::time::Instant;

use holonics::geometry::RatVec3;
use holonics::geometry::screw::ScrewGenerator;
use holonics::hnn::constitution::CAMPAIGN_ONE_BUDGET;
use holonics::hnn::field::{CribDeclaration, ReceiverDeclaration};
use holonics::hnn::{
    Constitution, ConstitutionRead, ContactDeclaration, Current, Field, FieldDeclaration, Lattice,
    Locus, ReceivingPhases, RingDeclaration, SourceMoment, Steps,
};
use holonics::ratio::linear::ExactRatMatrix;
use holonics::ratio::{Rat, integer, rat};
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};

use super::card::{READ_SHARED_PER_THREAD, ingest_shared};
use super::*;
use crate::cuda::{Dim3, MemoryInfo};

// -------------------------------------------------------------------------------------------
// fixtures

/// SplitMix64: exact, deterministic, no float.
pub(super) struct Draw(pub(super) u64);

impl Draw {
    pub(super) fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    pub(super) fn below(&mut self, bound: usize) -> usize {
        (self.next() % bound as u64) as usize
    }

    /// A signed integer of magnitude below `2^bits`.
    pub(super) fn signed(&mut self, bits: u32) -> i64 {
        let magnitude = (self.next() >> (64 - bits)) as i64;
        if self.next() & 1 == 1 {
            -magnitude
        } else {
            magnitude
        }
    }

    /// A value of `2^(−exponent)ℤ` whose coordinate has magnitude below `2^bits`.
    fn lattice_value(&mut self, exponent: u32, bits: u32) -> Rat {
        Rat::new(BigInt::from(self.signed(bits)), BigInt::from(1) << exponent)
    }

    fn lattice_matrix(
        &mut self,
        rows: usize,
        columns: usize,
        exponent: u32,
        bits: u32,
    ) -> ExactRatMatrix {
        ExactRatMatrix::shaped(
            rows,
            columns,
            (0..rows)
                .map(|_| {
                    (0..columns)
                        .map(|_| self.lattice_value(exponent, bits))
                        .collect()
                })
                .collect(),
        )
        .unwrap()
    }
}

/// The RTX 4080 SUPER's census as its driver reports it (`the_card_opens_with_its_census`).
pub(super) fn census() -> DeviceCensus {
    DeviceCensus {
        name: "fixture".into(),
        compute_capability: (8, 9),
        multiprocessors: 80,
        warp: 32,
        max_threads_per_block: 1024,
        max_threads_per_multiprocessor: 1536,
        max_blocks_per_multiprocessor: 24,
        max_grid: Dim3 {
            x: 2_147_483_647,
            y: 65_535,
            z: 65_535,
        },
        shared_per_block: 49_152,
        shared_per_block_optin: 101_376,
        shared_per_multiprocessor: 102_400,
        registers_per_block: 65_536,
        registers_per_multiprocessor: 65_536,
        memory: MemoryInfo {
            free_bytes: 0,
            total_bytes: 0,
        },
    }
}

pub(super) fn entry(
    name: &'static str,
    max_threads_per_block: u32,
    static_shared: u32,
) -> EntryCensus {
    EntryCensus {
        name,
        max_threads_per_block,
        registers: 32,
        static_shared,
        local_octets: 0,
    }
}

/// A closing ring of `period` on the unit circle's quarter turns about `e_z`, pitch 0.
fn ring(period: u64, lock: Vec<u64>, initial: u64) -> RingDeclaration {
    RingDeclaration {
        period,
        screw: ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
        placements: (0..period)
            .map(|node| FieldDeclaration::quarter_turn(node, period))
            .collect(),
        lock,
        reflector: (0..period)
            .map(|p| ((period - p) % period) as usize)
            .collect(),
        admittance: integer(2),
        initial,
    }
}

fn contact(from: usize, to: usize, nodes: usize, exponent: i64) -> ContactDeclaration {
    ContactDeclaration {
        from,
        to,
        channel: (0..nodes).map(|node| (node, node)).collect(),
        admittance: integer(2),
        exponent: integer(exponent),
    }
}

/// A small chain for the ingest's laws: periods 2, 3, 2 (locks `{0}`, `{0, 2}`, `∅`), two source
/// rings, `|A| = 4`, `Δ = {1, 3}` (a window of three cells).
fn chain() -> Field {
    Field::declare(
        FieldDeclaration {
            rings: vec![
                ring(2, vec![0], 0),
                ring(3, vec![0, 2], 0),
                ring(2, vec![], 0),
            ],
            contacts: vec![contact(0, 1, 2, 2), contact(1, 2, 2, 0)],
            loops: Vec::new(),
            sources: vec![0, 1],
            offsets: vec![1, 3],
            alphabet: 4,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![ReceiverDeclaration {
                ring: 2,
                aperture: 2,
                tolerance: rat(1, 16),
            }],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 20,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .unwrap()
}

pub(super) fn card() -> Card {
    Card::open(0).expect("a CUDA card at ordinal 0 with the HNN kernels built")
}

fn as_rats(counts: &[u64]) -> Vec<Rat> {
    counts
        .iter()
        .map(|count| Rat::from_integer(BigInt::from(*count)))
        .collect()
}

/// The gather realizing `P^k` on a ring's realified coordinates, read off the host's own rotation
/// (`Ring::rotate` of the index vector): coordinate `j` of `P^k v` is `v[gather[j]]`.
fn rotation_gather(field: &Field, ring: usize, k: &BigInt) -> Vec<usize> {
    let width = field.ring(ring).width();
    let indices: Vec<Rat> = (0..width)
        .map(|index| Rat::from_integer(BigInt::from(index)))
        .collect();
    field
        .ring(ring)
        .rotate(&indices, k)
        .iter()
        .map(|index| index.to_integer().to_usize().unwrap())
        .collect()
}

/// The host's exact oracle of one read: the integer sums and their l1 bounds, at exponent 0 on both
/// sides (the words themselves).
fn oracle(a: &LatticeCoordinates, x: &LatticeCoordinates) -> Vec<(BigInt, BigInt)> {
    let mut out = Vec::new();
    for b in 0..x.rows() {
        for i in 0..a.rows() {
            let (mut sum, mut bound) = (BigInt::zero(), BigInt::zero());
            for j in 0..a.columns() {
                let p = BigInt::from(a.words()[i * a.columns() + j])
                    * BigInt::from(x.words()[b * x.columns() + j]);
                bound += p.abs();
                sum += p;
            }
            out.push((sum, bound));
        }
    }
    out
}

// -------------------------------------------------------------------------------------------
// fast tests: the host-side laws

/// The coordinates of a lattice-carried array are its entries times `2^L`, exactly, down to the
/// signed minimum; an entry off the lattice or beyond the word is refused by position.
#[test]
fn lattice_coordinates_are_the_lattice_points() {
    let lattice = Lattice::new(3);
    let matrix = ExactRatMatrix::shaped(
        2,
        3,
        vec![
            vec![rat(1, 8), rat(-3, 4), integer(5)],
            vec![Rat::zero(), rat(-1, 2), rat(7, 8)],
        ],
    )
    .unwrap();
    let coordinates = LatticeCoordinates::of_matrix(&matrix, lattice).unwrap();
    assert_eq!(coordinates.words(), &[1, -6, 40, 0, -4, 7]);
    assert_eq!(coordinates.exponent(), 3);

    let minimum = Rat::new(BigInt::from(i64::MIN), BigInt::from(8));
    let words = LatticeCoordinates::of_vectors(&[vec![minimum.clone()]], lattice).unwrap();
    assert_eq!(words.words(), &[i64::MIN]);

    let off = ExactRatMatrix::shaped(1, 2, vec![vec![rat(1, 8), rat(1, 3)]]).unwrap();
    assert!(matches!(
        LatticeCoordinates::of_matrix(&off, lattice),
        Err(DeviceError::OffLattice {
            row: 0,
            column: 1,
            exponent: 3
        })
    ));
    let beyond = minimum - rat(1, 8);
    assert!(matches!(
        LatticeCoordinates::of_vectors(&[vec![integer(0), beyond]], lattice),
        Err(DeviceError::Word {
            row: 0,
            column: 1,
            bits: 64
        })
    ));
}

/// The read's layout covers each row with the least power of two of at least a warp, within the
/// entry's, the device's and the shared ceilings; a wider row is split over its threads; a grid
/// the census cannot carry is refused.
#[test]
fn read_layout_is_derived_from_the_census() {
    let census = census();
    let read = entry("hnn_lattice_read", 1024, 4);
    // R P v on campaign 1: 512 rows of 22 columns, two receiving epochs.
    let r = read_layout(&census, &read, 512, 22, 2).unwrap();
    assert_eq!(
        (r.grid, r.block),
        (Dim3 { x: 512, y: 2, z: 1 }, Dim3::x(32))
    );
    assert_eq!(r.shared, 32 * READ_SHARED_PER_THREAD);
    assert_eq!(
        r.realization,
        Realization::EntryPerBlock {
            entries: 1024,
            threads: 32,
            per_thread: 1
        }
    );
    // E_0 M_0[c]: 10 rows of 256 columns, five phases.
    let e = read_layout(&census, &read, 10, 256, 5).unwrap();
    assert_eq!(
        e.realization,
        Realization::EntryPerBlock {
            entries: 50,
            threads: 256,
            per_thread: 1
        }
    );
    // A row wider than the block's ceiling loops.
    let wide = read_layout(&census, &read, 3, 5000, 1).unwrap();
    assert_eq!(
        wide.realization,
        Realization::EntryPerBlock {
            entries: 3,
            threads: 1024,
            per_thread: 5
        }
    );
    // The shared words bound the block: (49,152 − 4) / 32 = 1,535 threads, so 1,024; with a
    // static surface of 40,000 octets, 286, so 256.
    let crowded = read_layout(
        &census,
        &entry("hnn_lattice_read", 1024, 40_000),
        3,
        5000,
        1,
    )
    .unwrap();
    assert_eq!(crowded.block, Dim3::x(256));
    // The function's own ceiling, lowered by its registers, bounds it too.
    let lowered = read_layout(&census, &entry("hnn_lattice_read", 384, 0), 3, 5000, 1).unwrap();
    assert_eq!(lowered.block, Dim3::x(256));
    assert!(matches!(
        read_layout(&census, &read, 4, 4, 65_536),
        Err(DeviceError::Launch { .. })
    ));
    assert!(matches!(
        read_layout(&census, &read, 0, 4, 1),
        Err(DeviceError::Launch { .. })
    ));
}

/// The ingest's layout is one block, as wide as the census and the rings' scans admit, narrowed
/// only on request; its tiles cover the cells.
#[test]
fn ingest_layout_is_derived_from_the_census() {
    let census = census();
    let ingest = entry("hnn_moment_ingest", 1024, 8);
    // Campaign 1: four rings, 1,190 cells (a mean aeon on uniform bytes).
    let layout = ingest_layout(&census, &ingest, 4, 1190, None).unwrap();
    assert_eq!((layout.grid, layout.block), (Dim3::x(1), Dim3::x(1024)));
    assert_eq!(layout.shared, ingest_shared(4, 1024).unwrap());
    assert_eq!(
        layout.realization,
        Realization::OneBlockScan {
            threads: 1024,
            tiles: 2
        }
    );
    // Twelve rings' scans need 48 octets a thread: (49,152 − 8 − 144) / 48 = 1,020, so 512.
    assert_eq!(
        ingest_layout(&census, &ingest, 12, 1, None).unwrap().block,
        Dim3::x(512)
    );
    // Narrowed on request, to a power of two.
    assert_eq!(
        ingest_layout(&census, &ingest, 3, 400, Some(48))
            .unwrap()
            .realization,
        Realization::OneBlockScan {
            threads: 32,
            tiles: 13
        }
    );
    assert!(matches!(
        ingest_layout(&census, &ingest, 0, 1, None),
        Err(DeviceError::Launch { .. })
    ));
}

// -------------------------------------------------------------------------------------------
// parity on the card

/// The card opens with its census read off the driver, and each entry's lowered limits.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_opens_with_its_census() {
    let card = card();
    let census = card.census();
    eprintln!("kernels: {KERNELS}");
    eprintln!("census: {census:#?}");
    for name in [
        lattice::READ_ENTRY,
        moment::INGEST_ENTRY,
        word::TICK_ENTRY,
        word::ADJOINT_ENTRY,
        word::RESIDUAL_ENTRY,
        word::REFINE_ENTRY,
        word::CERTIFICATE_ENTRY,
    ] {
        eprintln!("entry: {:?}", card.entry(name).unwrap());
    }
    assert!(census.multiprocessors > 0 && census.warp > 0);
    assert!(census.max_threads_per_block >= census.warp);
    assert!(KERNELS.starts_with("compute_"));
}

/// A buffer of one card is refused by another (#15).
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn a_foreign_buffer_is_refused() {
    let (first, second) = (card(), card());
    let a =
        LatticeCoordinates::of_vectors(&[vec![integer(1), integer(2)]], Lattice::new(0)).unwrap();
    let locus = ResidentLattice::mount(&first, &a).unwrap();
    let operand = ResidentLattice::mount(&second, &a).unwrap();
    assert!(matches!(
        first.read(&locus, operand.operand(), None),
        Err(DeviceError::ForeignBuffer)
    ));
    let own = ResidentLattice::mount(&first, &a).unwrap();
    let read = first
        .read(&locus, own.operand(), None)
        .unwrap()
        .fetch()
        .unwrap();
    assert_eq!(read.coordinate(0, 0), 5);
}

/// The lattice read equals the host's exact product on small fixtures: dyadic entries at two
/// lattices, a gather, and the carrier's edges (the l1 certificate at `2^127 − 1` admitted, at and
/// past `2^127` refused whatever the sum's value, the signed minimum squared admitted), with the
/// refused entries exactly the host oracle's.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn lattice_read_matches_the_host_on_small_fixtures() {
    let card = card();
    // Dyadic fixture: A on 2^(−3)ℤ, vectors on 2^(−2)ℤ.
    let mut draw = Draw(7);
    let a = draw.lattice_matrix(3, 4, 3, 12);
    let vectors: Vec<Vec<Rat>> = (0..2)
        .map(|_| (0..4).map(|_| draw.lattice_value(2, 10)).collect())
        .collect();
    let locus = ResidentLattice::mount(
        &card,
        &LatticeCoordinates::of_matrix(&a, Lattice::new(3)).unwrap(),
    )
    .unwrap();
    let x = ResidentLattice::mount(
        &card,
        &LatticeCoordinates::of_vectors(&vectors, Lattice::new(2)).unwrap(),
    )
    .unwrap();
    let read = card.read(&locus, x.operand(), None).unwrap();
    eprintln!("small read: {:?}", read.layout());
    let read = read.fetch().unwrap();
    assert_eq!(read.exponent(), 5);
    for (b, vector) in vectors.iter().enumerate() {
        assert_eq!(read.vector(b), a.apply(vector).unwrap(), "vector {b}");
    }
    // A gather: vector 0 reversed, vector 1 its coordinates 2, 2, 0, 3.
    let maps = vec![vec![3, 2, 1, 0], vec![2, 2, 0, 3]];
    let gather = Gather::mount(&card, &maps).unwrap();
    let gathered = card
        .read(&locus, x.operand(), Some(&gather))
        .unwrap()
        .fetch()
        .unwrap();
    for (b, (vector, map)) in vectors.iter().zip(&maps).enumerate() {
        let moved: Vec<Rat> = map.iter().map(|&k| vector[k].clone()).collect();
        assert_eq!(gathered.vector(b), a.apply(&moved).unwrap(), "gathered {b}");
    }
    let outside = Gather::mount(&card, &[vec![0, 1, 2, 4], vec![0, 1, 2, 3]]).unwrap();
    assert!(matches!(
        card.read(&locus, x.operand(), Some(&outside)).unwrap().fetch(),
        Err(DeviceError::Malformed { entries }) if entries == vec![(0, 0), (0, 1), (0, 2)]
    ));

    // The carrier's edges, in words (L = 0).
    let big = i64::MAX; // 2^63 − 1
    let word = |v: i64| Rat::from_integer(BigInt::from(v));
    let edges = LatticeCoordinates::of_vectors(
        &[
            vec![
                word(big),
                word(big),
                word((1 << 33) - 1),
                word((1 << 32) - 3),
            ],
            vec![word(i64::MIN), word(0), word(0), word(0)],
            vec![word(i64::MIN), word(i64::MIN), word(0), word(0)],
        ],
        Lattice::new(0),
    )
    .unwrap();
    let operands = LatticeCoordinates::of_vectors(
        &[
            vec![word(big), word(-big), word(1 << 32), word(1)],
            vec![word(big), word(-big), word(1 << 32), word(2)],
            vec![word(i64::MIN), word(i64::MIN), word(0), word(0)],
        ],
        Lattice::new(0),
    )
    .unwrap();
    let expected = oracle(&edges, &operands);
    let carrier = BigInt::from(1) << 127usize;
    // Row 0 against vector 0 sits exactly at 2^127 − 1 and is admitted.
    assert_eq!(expected[0].1, &carrier - 1);
    let refused: Vec<(usize, usize)> = expected
        .iter()
        .enumerate()
        .filter(|(_, (_, bound))| *bound >= carrier)
        .map(|(at, _)| (at / 3, at % 3))
        .collect();
    assert_eq!(refused, vec![(1, 0), (2, 2)]);
    let edge_locus = ResidentLattice::mount(&card, &edges).unwrap();
    let edge_operand = ResidentLattice::mount(&card, &operands).unwrap();
    match card
        .read(&edge_locus, edge_operand.operand(), None)
        .unwrap()
        .fetch()
    {
        Err(DeviceError::Carrier { entries }) => assert_eq!(entries, refused),
        other => panic!("expected the carrier refusal, found {other:?}"),
    }
    // Vector 0 alone is admitted at every row, exactly.
    let first = ResidentLattice::mount(
        &card,
        &LatticeCoordinates::of_vectors(
            &[vec![word(big), word(-big), word(1 << 32), word(1)]],
            Lattice::new(0),
        )
        .unwrap(),
    )
    .unwrap();
    let admitted = card
        .read(&edge_locus, first.operand(), None)
        .unwrap()
        .fetch()
        .unwrap();
    for (row, (sum, _)) in expected.iter().take(3).enumerate() {
        assert_eq!(&BigInt::from(admitted.coordinate(0, row)), sum, "row {row}");
    }
    // The signed minimum squared, 2^126, is a word of the carrier.
    let square = ResidentLattice::mount(
        &card,
        &LatticeCoordinates::of_vectors(
            &[vec![word(i64::MIN), word(i64::MIN), word(0), word(0)]],
            Lattice::new(0),
        )
        .unwrap(),
    )
    .unwrap();
    let single = ResidentLattice::mount(
        &card,
        &LatticeCoordinates::of_vectors(
            &[vec![word(i64::MIN), word(0), word(0), word(0)]],
            Lattice::new(0),
        )
        .unwrap(),
    )
    .unwrap();
    let squared = card
        .read(&single, square.operand(), None)
        .unwrap()
        .fetch()
        .unwrap();
    assert_eq!(squared.coordinate(0, 0), 1i128 << 126);
}

/// Ingest parity on the small chain: batch by batch, the device's `Ingested`, lift point and phase
/// classes equal the host moment's, across carry-outs, tiles and the window's three cells; at the
/// end every phase-binned and offset count and the window are equal.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn moment_ingest_matches_the_host_moment() {
    let field = chain();
    let a = field.alphabet();
    let card = card();
    for lanes in [Some(32), None] {
        let opening = Current::at(&field, vec![1.into(), 2.into(), 1.into()]).unwrap();
        let mut current = opening.clone();
        let mut host = SourceMoment::open(&field, &current);
        let mut device = ResidentMoment::open(&card, &field, &opening).unwrap();
        let mut draw = Draw(21);
        let cells: Vec<usize> = (0..400).map(|_| draw.below(a)).collect();
        let (mut fed, mut batch, mut carries) = (0usize, 1usize, 0usize);
        while fed < cells.len() {
            let end = (fed + batch).min(cells.len());
            let chunk = &cells[fed..end];
            let expected = host.ingest(&field, &mut current, chunk).unwrap();
            let (found, layout) = device.ingest_in(chunk, lanes).unwrap();
            assert_eq!(found, expected, "batch at {fed}, {layout:?}");
            assert_eq!(
                device.lift(),
                current.lift(),
                "lift after the batch at {fed}"
            );
            let phases: Vec<u32> = (0..field.rings().len())
                .map(|g| current.phase(&field, g).unwrap() as u32)
                .collect();
            assert_eq!(device.phases().unwrap(), phases);
            carries += usize::from(expected.carry_out);
            fed += expected.cells;
            batch = batch * 7 % 61 + 1;
        }
        assert!(carries > 3, "the fixture crosses carry-outs ({carries})");
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
    assert!(matches!(
        ResidentMoment::open(&card, &field, &Current::at_rest(&field))
            .unwrap()
            .ingest(&[1, 4]),
        Err(DeviceError::Hnn(holonics::hnn::HnnError::CellOutside {
            code: 4,
            alphabet: 4
        }))
    ));
}

/// Campaign 1's declared shapes (`FieldDeclaration::campaign_one` at `n* = 6,148`): the ingest of
/// `n*` drawn bytes equals the host moment's; `E_0 M_0[c]` (`10 × 256` on its lattice, against the
/// resident counts) equals the host's product per phase and folds to `SourceMoment::encode`; and
/// `R P_R^(τ_R) v` (`512 × 22` on `2^(−10)ℤ`, the initial and a drawn map, against lattice anchors
/// with the rotation as a gather) equals `ReceivingPhases::read`'s logits.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn campaign_one_reads_and_ingest_match_the_host() {
    let started = Instant::now();
    let population = 6_148;
    let field = Field::declare(FieldDeclaration::campaign_one(population)).unwrap();
    let initial =
        Constitution::initial(&field, Steps::campaign_one(), CAMPAIGN_ONE_BUDGET).unwrap();
    eprintln!("declared in {} us", started.elapsed().as_micros());
    let card = card();
    let mut draw = Draw(1_077);

    // The ingest of n* bytes, batch by batch across the carry-outs.
    let cells: Vec<usize> = (0..population as usize).map(|_| draw.below(256)).collect();
    let opening = Current::at_rest(&field);
    let mut current = opening.clone();
    let mut host = SourceMoment::open(&field, &current);
    let mut device = ResidentMoment::open(&card, &field, &opening).unwrap();
    let (mut fed, mut aeons, mut device_us) = (0usize, 0usize, 0u128);
    while fed < cells.len() {
        let chunk = &cells[fed..];
        let expected = host.ingest(&field, &mut current, chunk).unwrap();
        let clock = Instant::now();
        let (found, layout) = device.ingest_in(chunk, None).unwrap();
        device_us += clock.elapsed().as_micros();
        if fed == 0 {
            eprintln!("ingest: {layout:?}");
        }
        assert_eq!(found, expected, "batch at {fed}");
        assert_eq!(device.lift(), current.lift());
        aeons += usize::from(expected.carry_out);
        fed += expected.cells;
    }
    eprintln!(
        "ingest: {fed} cells, {aeons} carry-outs, {device_us} us on the card (with transfers)"
    );
    let counts = device.counts().unwrap();
    for phase in 0..5 {
        assert_eq!(
            counts.phase_counts(0, phase).unwrap(),
            host.phase_counts(0, phase).unwrap()
        );
        assert_eq!(
            counts.offset_counts(0, 1, phase).unwrap(),
            host.offset_counts(0, 1, phase).unwrap()
        );
    }
    assert_eq!(device.window().unwrap(), host.window());

    // E_0 on its lattice, read against the resident phase rows.
    let lattice = initial.lattice(Locus::SourcePort(0)).unwrap();
    let e0 = draw.lattice_matrix(10, 256, lattice.exponent(), 40);
    let theta = initial
        .clone()
        .with_ports(0, None, Some(e0.clone()), None)
        .unwrap();
    let locus = ResidentLattice::mount(
        &card,
        &LatticeCoordinates::of_matrix(theta.source_port(0).unwrap(), lattice).unwrap(),
    )
    .unwrap();
    let clock = Instant::now();
    let read = card
        .read(&locus, device.phase_operand(0).unwrap(), None)
        .unwrap();
    let layout = *read.layout();
    let read = read.fetch().unwrap();
    eprintln!(
        "E_0 M_0[c] (L = {}): {layout:?}, {} us with the transfer",
        lattice.exponent(),
        clock.elapsed().as_micros()
    );
    let mut folded = vec![Rat::zero(); 10];
    for phase in 0..5 {
        let binned = read.vector(phase);
        assert_eq!(
            binned,
            e0.apply(&as_rats(host.phase_counts(0, phase).unwrap()))
                .unwrap(),
            "phase {phase}"
        );
        let carried = field.ring(0).rotate(&binned, &-BigInt::from(phase));
        for (value, add) in folded.iter_mut().zip(carried) {
            *value += add;
        }
    }
    // The pair port's outputs are zero at the initial constitution, so its part adds nothing.
    assert_eq!(folded, host.encode(&field, &theta, 0).unwrap());

    // R on 2^(−10)ℤ: the initial map and a drawn one, against two lattice anchors on 2^(−20)ℤ,
    // rotated by the receiving ring's lift.
    let r_lattice = initial.lattice(Locus::ReceivingMap(2)).unwrap();
    assert_eq!(r_lattice.exponent(), 10);
    let anchors: Vec<Vec<Rat>> = (0..2)
        .map(|_| (0..22).map(|_| draw.lattice_value(20, 40)).collect())
        .collect();
    let lift = current.lift()[2].clone();
    let gather = rotation_gather(&field, 2, &lift);
    let gathers = Gather::mount(&card, &[gather.clone(), gather]).unwrap();
    let x = ResidentLattice::mount(
        &card,
        &LatticeCoordinates::of_vectors(&anchors, Lattice::new(20)).unwrap(),
    )
    .unwrap();
    let drawn = draw.lattice_matrix(512, 22, 10, 50);
    for (name, theta) in [
        ("initial", initial.clone()),
        (
            "drawn",
            initial
                .clone()
                .with_ports(2, None, None, Some(drawn))
                .unwrap(),
        ),
    ] {
        let map = theta.receiving_map(2).unwrap();
        let locus = ResidentLattice::mount(
            &card,
            &LatticeCoordinates::of_matrix(map, r_lattice).unwrap(),
        )
        .unwrap();
        let clock = Instant::now();
        let read = card.read(&locus, x.operand(), Some(&gathers)).unwrap();
        let layout = *read.layout();
        let read = read.fetch().unwrap();
        eprintln!(
            "R P v ({name}): {layout:?}, {} us with the transfer",
            clock.elapsed().as_micros()
        );
        // Declared at the mount's lift point, as the reference declares its admitted family; the
        // read rotates by the lift the ingest reached.
        let clock = Instant::now();
        let phases =
            ReceivingPhases::declare(&field, &theta, &opening, &field.receivers()[0]).unwrap();
        eprintln!(
            "receiving phases declared in {} us",
            clock.elapsed().as_micros()
        );
        for (b, anchor) in anchors.iter().enumerate() {
            let logits = phases
                .read(&field, &theta, &current, anchor)
                .unwrap()
                .logits;
            assert_eq!(read.vector(b), logits, "{name}, anchor {b}");
        }
    }
    eprintln!("campaign 1 parity in {} us", started.elapsed().as_micros());
}
