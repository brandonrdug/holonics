//! Tests of the release at class grain: the release reads the scorer's face, the point face's
//! certified mass is its scored mass, a fixed key gives the identical release, the commit holds a
//! tie and releases a certified maximum, a straddled key refines by demand, and a stream that runs
//! out holds by name.

use num_bigint::{BigInt, BigUint};

use super::*;
use crate::hnn::ratio::Faces;
use crate::hnn::receiving::{ReceivingRead, receiving_population, score};
use crate::ratio::rat;
use crate::receiver::face::grain_exponent;

const GRAIN: u64 = 4;

/// A dyadic tree face over the classes, with each class's grain exponent.
fn tree_face(probabilities: Vec<Rat>) -> LandmarkFace {
    let exponents = probabilities
        .iter()
        .map(|p| {
            grain_exponent(
                &BigUint::try_from(p.numer().clone()).unwrap(),
                &BigUint::try_from(p.denom().clone()).unwrap(),
                GRAIN,
            )
            .unwrap()
        })
        .collect();
    LandmarkFace {
        grain: GRAIN,
        probabilities,
        exponents,
    }
}

/// The epoch's faces with the known classes: phase 0's tree is fixed, phase 1's turns by the class
/// released at phase 0, and each combined face is the wave's logits plus its tree's grain logits.
fn epoch(waves: &[Vec<Rat>], known: &[usize]) -> Against {
    let base = [rat(1, 2), rat(1, 4), rat(1, 8), rat(1, 8)];
    let trees: Vec<LandmarkFace> = (0..waves.len())
        .map(|j| {
            let turn = if j == 0 {
                0
            } else {
                known.first().copied().unwrap_or(0)
            };
            tree_face((0..4).map(|c| base[(c + turn) % 4].clone()).collect())
        })
        .collect();
    let reads: Vec<ReceivingRead> = waves
        .iter()
        .zip(&trees)
        .map(|(wave, tree)| ReceivingRead::combined(wave.clone(), tree, GRAIN).unwrap())
        .collect();
    Against {
        faces: Faces::of_reads(&reads, GRAIN).unwrap(),
        trees,
    }
}

fn waves() -> Vec<Vec<Rat>> {
    vec![
        vec![
            rat(1, 3),
            rat(0, 1),
            rat(0, 1),
            rat(1, 5),
            rat(2, 7),
            rat(0, 1),
            rat(-1, 2),
            rat(0, 1),
        ],
        vec![
            rat(-1, 3),
            rat(1, 7),
            rat(3, 5),
            rat(0, 1),
            rat(0, 1),
            rat(0, 1),
            rat(1, 9),
            rat(0, 1),
        ],
    ]
}

fn keys(bytes: &[u8]) -> KeyStream {
    KeyStream::new(bytes.to_vec(), 4).unwrap()
}

#[test]
fn the_demand_ladder_doubles_from_the_reading_bits_to_the_population_precision() {
    assert_eq!(demand_ladder(), vec![64, 128, 192]);
}

/// `P_release = P_scored`: each drawn class's scored face, at the declared reading bits, is the
/// face the scorer's population reads for that class as a target, with the same prefix received.
#[test]
fn the_release_reads_the_scorers_face_with_the_drawn_prefix_received() {
    let waves = waves();
    let population = receiving_population();
    let mut stream = keys(&[0x9a, 0x13, 0x55, 0x01, 0x40, 0x00, 0x00, 0x07]);
    let release = release_cells(
        &population,
        2,
        |known| Ok(epoch(&waves, known)),
        CellLaw::Draw(&mut stream),
    )
    .unwrap();
    let placement = release.classes().expect("both phases drawn");
    let against = epoch(&waves, &placement);
    let scored = score(&population, 0, &against.faces, &against.trees, &placement).unwrap();
    let mut local = population.clone();
    for (j, step) in scored.steps.iter().enumerate() {
        let cell = &release.cells[j];
        assert_eq!(cell.bits, READING_BITS);
        assert_eq!(
            local.face_of(&step.faces()).unwrap(),
            cell.face[placement[j]]
        );
        local.receive(&step.faces()).unwrap();
    }
    // The certified mass is at most the scored mass's upper bound.
    let upper = release
        .cells
        .iter()
        .zip(&placement)
        .fold(Rat::one(), |mass, (cell, &class)| {
            mass * &cell.face[class].upper
        });
    assert!(release.certified_mass().unwrap() <= upper);
}

/// The first decision at uniform faces releases a fair draw: the point face's certified cell is
/// its scored mass exactly, a key on a cell's left end lands in that cell, and the commit holds.
#[test]
fn a_uniform_point_face_draws_its_exact_cell_and_the_commit_holds_the_tie() {
    let uniform = vec![vec![rat(0, 1); 8]];
    let flat = |_: &[usize]| {
        let tree = tree_face(vec![rat(1, 4); 4]);
        let read = ReceivingRead::combined(uniform[0].clone(), &tree, GRAIN).unwrap();
        Ok(Against {
            faces: Faces::of_reads(&[read], GRAIN).unwrap(),
            trees: vec![tree],
        })
    };
    let population = receiving_population();
    // The key 3/4 (bytes c0 00 00 00) is the left end of class 3's cell.
    let mut stream = keys(&[0xc0, 0, 0, 0]);
    let drawn = release_cells(&population, 1, flat, CellLaw::Draw(&mut stream)).unwrap();
    assert_eq!(drawn.classes(), Some(vec![3]));
    assert_eq!(drawn.certified_mass(), Some(rat(1, 4)));
    assert!(
        drawn.cells[0]
            .face
            .iter()
            .all(|f| f.lower == rat(1, 4) && f.upper == rat(1, 4))
    );
    let held = release_cells(&population, 1, flat, CellLaw::Commit).unwrap();
    assert_eq!(held.cells[0].release, ReleaseReturn::Hold);
    assert_eq!(held.cells[0].classes, vec![0, 1, 2, 3]);
    assert_eq!(held.classes(), None);
}

/// The commit releases the class every compatible face holds maximal.
#[test]
fn the_commit_releases_a_certified_maximum() {
    let waves = waves();
    let population = receiving_population();
    let release = release_cells(
        &population,
        2,
        |known| Ok(epoch(&waves, known)),
        CellLaw::Commit,
    )
    .unwrap();
    let first = &release.cells[0];
    let class = first.class().expect("phase 0 has a certified maximum");
    for (other, face) in first.face.iter().enumerate() {
        if other != class {
            assert!(first.face[class].lower > face.upper);
        }
    }
}

/// A fixed key stream gives the identical release; the keys read are counted.
#[test]
fn a_fixed_key_stream_gives_the_identical_release() {
    let waves = waves();
    let population = receiving_population();
    let bytes = [0x21, 0x7f, 0x00, 0x99, 0xee, 0x01, 0x02, 0x03];
    let mut first = keys(&bytes);
    let mut second = keys(&bytes);
    let a = release_cells(
        &population,
        2,
        |k| Ok(epoch(&waves, k)),
        CellLaw::Draw(&mut first),
    )
    .unwrap();
    let b = release_cells(
        &population,
        2,
        |k| Ok(epoch(&waves, k)),
        CellLaw::Draw(&mut second),
    )
    .unwrap();
    assert_eq!(a, b);
    assert_eq!(first.keys_read(), 2);
    assert_eq!(a.cells[1].key.as_ref().map(|(index, _)| *index), Some(1));
}

/// A key the declared reading bits leave straddling a cell's boundary is read again at the bits
/// it demands and certified there, never forced and never loosened.
#[test]
fn a_straddled_key_refines_by_demand() {
    // Class 0's combined mass is θ/(θ + 3), θ = 2^(1/4): irrational, so its enclosure has width.
    let wave = vec![
        rat(1, 4),
        rat(0, 1),
        rat(0, 1),
        rat(0, 1),
        rat(0, 1),
        rat(0, 1),
        rat(0, 1),
        rat(0, 1),
    ];
    let tree = tree_face(vec![rat(1, 4); 4]);
    let read = ReceivingRead::combined(wave, &tree, GRAIN).unwrap();
    let faces = Faces::of_reads(&[read], GRAIN).unwrap();
    let population = receiving_population();
    let coarse = scored_face(&population, &tree, &faces.faces[0], 0, READING_BITS).unwrap();
    assert!(coarse.lower < coarse.upper);
    // A key strictly inside class 0's enclosure at the reading bits: class 0's cell ends at its
    // lower bound, class 1's begins at its upper bound, so the key straddles.
    let midpoint = (&coarse.lower + &coarse.upper) / rat(2, 1);
    let scale = BigInt::from(1u8) << 256usize;
    let k = (midpoint * Rat::from_integer(scale)).floor().to_integer();
    let mut bytes = k.to_bytes_be().1;
    while bytes.len() < 32 {
        bytes.insert(0, 0);
    }
    let mut stream = KeyStream::new(bytes, 32).unwrap();
    let release = release_cells(
        &population,
        1,
        |_| {
            Ok(Against {
                faces: faces.clone(),
                trees: vec![tree.clone()],
            })
        },
        CellLaw::Draw(&mut stream),
    )
    .unwrap();
    let cell = &release.cells[0];
    assert!(cell.bits > READING_BITS, "decided at {} bits", cell.bits);
    assert!(matches!(cell.release, ReleaseReturn::Drawn(_)));
    // The finer enclosure nests inside the coarser one.
    assert!(cell.face[0].lower >= coarse.lower && cell.face[0].upper <= coarse.upper);
}

/// A declared key stream that runs out holds by name.
#[test]
fn an_exhausted_key_stream_holds_by_name() {
    let waves = waves();
    let population = receiving_population();
    let mut stream = keys(&[0x10, 0, 0, 0]);
    let release = release_cells(
        &population,
        2,
        |k| Ok(epoch(&waves, k)),
        CellLaw::Draw(&mut stream),
    )
    .unwrap();
    assert_eq!(release.cells.len(), 2);
    assert!(matches!(
        release.cells[1].release,
        ReleaseReturn::NoContinuationBridges { .. }
    ));
    assert_eq!(release.classes(), None);
}
