//! The landmark tree (Decision 28, count-only) on its declared dyadic lattice: the reference
//! oracle on the Willems–Shtarkov–Tjalkens fixture and the block recursion; the executed face's
//! exact normalization (a chart of five classes, so the odometer digits prune), its lattice law
//! against a recomputation in ℚ, and its certificate against the oracle cell by cell; the stop
//! weight's rounding; the β chart's rebase and its certified residual; the opened path's telescope;
//! the certified binary logarithm and the grain exponents; the derived widths; the stored bits;
//! score and deposit against receive; the refusals; and the prequential measurement.

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

use crate::hnn::HnnError;
use crate::hnn::landmark::{
    Beta, IdealLandmarks, LandmarkDeclaration, Landmarks, Letter, address, binary_log,
    carrier_width, choose_depth, code_length, face_bits, prequential,
};
use crate::hnn::ratio::log2_enclosure;
use crate::hnn::receiving::grain_exponent;
use crate::hnn::reference::Cut;
use crate::ratio::{Rat, rat};

fn declaration(alphabet: usize, depth: usize) -> LandmarkDeclaration {
    LandmarkDeclaration {
        alphabet,
        depth,
        forced: 0,
        population: 64,
        grain: 16,
    }
}

/// The sequential KT probability of a binary run, `Π (n_x + ½)/(n + 1)`.
fn kt_block(run: &[usize]) -> Rat {
    let mut counts = [0i64; 2];
    let mut probability = Rat::one();
    for &x in run {
        probability *= rat(2 * counts[x] + 1, 2 * (counts[0] + counts[1]) + 2);
        counts[x] += 1;
    }
    probability
}

/// **The block recursion**, independent of the path law: `W_s = E_s` at depth `D`, otherwise
/// `W_s = ½E_s + ½ Π_b W_bs`, over the symbols of `stream[past..]` whose context (newest first)
/// extends `context`.
fn block_weight(stream: &[usize], past: usize, context: &[usize], depth: usize) -> Rat {
    let routed: Vec<usize> = (past..stream.len())
        .filter(|&t| {
            context
                .iter()
                .enumerate()
                .all(|(back, &x)| stream[t - 1 - back] == x)
        })
        .map(|t| stream[t])
        .collect();
    let estimate = kt_block(&routed);
    if context.len() == depth {
        return estimate;
    }
    let split: Rat = (0..2)
        .map(|b| {
            let mut child = context.to_vec();
            child.push(b);
            block_weight(stream, past, &child, depth)
        })
        .product();
    rat(1, 2) * estimate + rat(1, 2) * split
}

/// `max(q̂/q, q/q̂) ≤ 1 + ρ` with `ρ = (2/3) R` the certificate in `ln`: then
/// `|ln(q̂/q)| ≤ ln(1 + ρ) ≤ ρ`, so `|log₂(q̂/q)| ≤ R` (a sufficient check).
fn within(executed: &Rat, ideal: &Rat, residual: &Rat) -> bool {
    let nats = residual * rat(2, 3);
    let (high, low) = if executed > ideal {
        (executed, ideal)
    } else {
        (ideal, executed)
    };
    high / low <= Rat::one() + nats
}

/// **The Willems–Shtarkov–Tjalkens fixture** (the 1995 paper's weighted context tree) on the
/// oracle with `β` exact: binary, `D = 3`, the source `0110100` after the past `0 1 0`, weighted
/// probability `95/32768` exactly; the pair `0100110` after `110` gives `7/2048`, checked against
/// the independent block recursion. The executed tree's product lies within the product of its
/// certificates.
#[test]
fn landmark_oracle_reproduces_the_willems_shtarkov_tjalkens_fixture() {
    let paper = [0, 1, 0, 0, 1, 1, 0, 1, 0, 0];
    let brief = [1, 1, 0, 0, 1, 0, 0, 1, 1, 0];
    let fixture = LandmarkDeclaration {
        population: 7,
        ..declaration(2, 3)
    };
    for (stream, weight) in [(paper, rat(95, 32768)), (brief, rat(7, 2048))] {
        assert_eq!(block_weight(&stream, 3, &[], 3), weight);
        let mut oracle = IdealLandmarks::new(fixture.clone(), None).unwrap();
        let mut tree = Landmarks::new(fixture.clone()).unwrap();
        let (mut ideal, mut executed, mut residual) = (Rat::one(), Rat::one(), Rat::zero());
        for t in 3..stream.len() {
            let here = address(&stream, t, 3);
            ideal *= oracle.receive(&here, stream[t]).unwrap();
            let reading = tree.receive(&here, stream[t]).unwrap();
            executed *= reading.executed;
            residual += reading.residual;
        }
        assert_eq!(ideal, weight);
        assert_eq!(oracle.rebases(), 0);
        assert!(within(&executed, &ideal, &residual));
    }
}

/// **The sequential path law is the block recursion** (the oracle, `β` exact) on a longer binary
/// stream at every depth up to 4, and the executed tree stays within its certificate there.
#[test]
fn landmark_oracle_path_law_is_the_block_recursion() {
    let stream: Vec<usize> = (0..24u64)
        .map(|t| usize::from((t * t + 3 * t) % 7 < 3))
        .collect();
    for depth in 0..=4 {
        let mut oracle = IdealLandmarks::new(declaration(2, depth), None).unwrap();
        let mut tree = Landmarks::new(declaration(2, depth)).unwrap();
        let mut ideal = Rat::one();
        for t in depth..stream.len() {
            let here = address(&stream, t, depth);
            let face = oracle.receive(&here, stream[t]).unwrap();
            let reading = tree.receive(&here, stream[t]).unwrap();
            assert!(within(&reading.executed, &face, &reading.residual));
            ideal *= face;
        }
        assert_eq!(ideal, block_weight(&stream, depth, &[], depth));
    }
}

/// **The executed faces are normalized exactly** (Lean `HNN/LandmarkTree.{lattice_path_laws,
/// cell_faces_partition, forced_digits_normalized}`) at every step of a short stream over five
/// classes (so the odometer's third digit is forced where the upper half is empty): the face sums
/// to 1, each class's face is positive, equals the one-class read and is a dyadic of at most
/// `B · M_p` bits; each grain exponent is `grain_exponent`'s and brackets its face; the oracle's
/// faces sum to 1; and each cell's certificate lies within the rule, below one grain, and holds
/// against the oracle.
#[test]
fn landmark_faces_are_normalized_and_certified() {
    let alphabet = 5;
    let stream: Vec<usize> = (0..40u64).map(|t| ((t * 7 + t / 3) % 5) as usize).collect();
    for forced in [0, 1] {
        let declared = LandmarkDeclaration {
            forced,
            ..declaration(alphabet, 2)
        };
        let mut tree = Landmarks::new(declared.clone()).unwrap();
        let mut oracle = IdealLandmarks::new(declared, None).unwrap();
        assert!(tree.face_rule() < rat(1, 32));
        let bits = tree.digits() * tree.face_bits();
        for (position, &cell) in stream.iter().enumerate() {
            let here = address(&stream, position, 2);
            let face = tree.face(&here, 16).unwrap();
            let sum: Rat = face.probabilities.iter().cloned().sum();
            assert_eq!(sum, Rat::one());
            let ideal: Rat = (0..alphabet)
                .map(|class| oracle.probability(&here, class).unwrap())
                .sum();
            assert_eq!(ideal, Rat::one());
            for class in 0..alphabet {
                let p = &face.probabilities[class];
                assert!(p > &Rat::zero());
                assert_eq!(p, &tree.probability(&here, class).unwrap());
                assert!(p.denom() <= &(BigInt::one() << bits as usize));
                let exact = grain_exponent(p.numer().magnitude(), p.denom().magnitude(), 16);
                assert_eq!(face.exponents[class], exact.unwrap());
            }
            let reading = tree.receive(&here, cell).unwrap();
            let ideal = oracle.receive(&here, cell).unwrap();
            assert!(reading.residual <= tree.face_rule());
            assert!(within(&reading.executed, &ideal, &reading.residual));
        }
    }
}

/// **The lattice law, recomputed in ℚ** at every step on every opened path: a founded leaf reads
/// `⟦k_D(0)⟧`, the first unfounded depth the prior `1/2`, a forced depth its child, and a mixing
/// depth `⟦λ̂ k(0) + (1 − λ̂) q̂'(0)⟧` with `λ̂ = ⟦β/(1 + β)⟧₀¹`, every face a numerator of
/// `2^(−M_p)` inside `[1, 2^(M_p) − 1]` (Lean `HNN/LandmarkTree.lattice_path_laws`); after the
/// deposit each mixing node's `β` is `β k(b)/q̂'(b)`, or its rebase within `2^(1−W)` below it.
#[test]
fn landmark_lattice_faces_follow_the_law() {
    let stream: Vec<usize> = (0..60u64).map(|t| ((t * t + t / 4) % 4) as usize).collect();
    for forced in [0, 1] {
        let mut tree = Landmarks::with_carrier(
            LandmarkDeclaration {
                forced,
                ..declaration(4, 3)
            },
            12,
        )
        .unwrap();
        let scale = Rat::from_integer(BigInt::one() << tree.face_bits() as usize);
        let lattice = |x: &Rat| {
            let rounded = (x * &scale + rat(1, 2)).floor();
            rounded.max(Rat::one()).min(&scale - Rat::one()) / &scale
        };
        let rebase = rat(1, 1 << 11);
        for (position, &cell) in stream.iter().enumerate() {
            let here = address(&stream, position, 3);
            for class in 0..4 {
                for path in tree.opened(&here, class).unwrap() {
                    let zero = |x: &Rat| {
                        if path.symbol == 0 {
                            x.clone()
                        } else {
                            Rat::one() - x
                        }
                    };
                    let top = path.faces.len() - 1;
                    for q in &path.faces {
                        let numerator = q * &scale;
                        assert!(numerator.is_integer());
                        assert!(numerator >= Rat::one() && numerator <= &scale - Rat::one());
                    }
                    if path.founded == 4 {
                        assert_eq!(zero(&path.faces[3]), lattice(&zero(&path.masses[3])));
                    } else {
                        assert_eq!(path.faces[top], rat(1, 2));
                    }
                    for d in 0..top {
                        let expected = if d < forced {
                            path.faces[d + 1].clone()
                        } else {
                            let beta = &path.betas[d];
                            let stop =
                                (beta / (Rat::one() + beta) * &scale + rat(1, 2)).floor() / &scale;
                            zero(&lattice(
                                &(&stop * zero(&path.masses[d])
                                    + (Rat::one() - &stop) * zero(&path.faces[d + 1])),
                            ))
                        };
                        assert_eq!(path.faces[d], expected);
                    }
                }
            }
            let before = tree.opened(&here, cell).unwrap();
            tree.receive(&here, cell).unwrap();
            let after = tree.opened(&here, cell).unwrap();
            for (old, new) in before.iter().zip(&after) {
                for d in forced..old.founded.min(3) {
                    let stepped = &old.betas[d] * &old.masses[d] / &old.faces[d + 1];
                    let ratio = &new.betas[d] / &stepped;
                    assert!(ratio <= Rat::one() && ratio > Rat::one() - &rebase);
                }
            }
        }
    }
}

/// **The stop weight** `λ̂ = ⟦β/(1 + β)⟧₀¹` on `2^(−M)` against the exact rounding in ℚ, over
/// ratios whose exponents run past `±(M + W)`, where the rounding is decided without operands.
#[test]
fn landmark_stop_weight_rounds_exactly() {
    let (face, width) = (12u64, 8u64);
    let scale = Rat::from_integer(BigInt::one() << face as usize);
    for (numerator, denominator) in [(1u128, 1u128), (255, 1), (1, 255), (171, 85), (3, 5)] {
        for exponent in -40i64..=40 {
            let (beta, rebased) = Beta::carry(numerator, denominator, exponent, width);
            assert!(rebased.is_none());
            let value = beta.value();
            let lambda = &value / (Rat::one() + &value) * &scale;
            let rounded = (lambda + rat(1, 2)).floor().to_integer();
            assert_eq!(
                BigInt::from(beta.stop_weight(face, width)),
                rounded,
                "β = {numerator}/{denominator}·2^{exponent}"
            );
        }
    }
}

/// **The β chart rebases** (Lean `HNN/LandmarkTree.rebase_log_residual`): a ratio whose odd parts
/// outgrow `W` keeps its mantissa `m' ∈ [2^(W−1), 2^W)` with relative residual in `[0, 1/m')`, a
/// ratio within `W` is carried exactly and reduced; at a declared carrier of 4 bits a tree rebases,
/// its faces stay exactly normalized and its certificates grow with the rebases while holding
/// against the oracle.
#[test]
fn landmark_chart_rebases_with_its_certified_residual() {
    let width = 4u64;
    let (carried, mantissa) = Beta::carry(1000, 7, 0, width);
    let mantissa = mantissa.expect("1000 = 2³·125 outgrows 4 bits");
    assert!((8..16).contains(&mantissa));
    let value = rat(1000, 7);
    let residual = (&value - carried.value()) / &value;
    assert!(residual >= Rat::zero() && residual < Rat::new(BigInt::one(), BigInt::from(mantissa)));
    let (exact, rebased) = Beta::carry(96 * 3, 5 * 3, -1, width);
    assert!(rebased.is_none());
    assert_eq!(exact.value(), rat(48, 5));
    assert_eq!(exact.exponent(), 4);

    let stream: Vec<usize> = (0..60u64).map(|t| ((t * t) % 3) as usize).collect();
    let mut tree = Landmarks::with_carrier(declaration(3, 2), width).unwrap();
    let mut oracle = IdealLandmarks::new(declaration(3, 2), None).unwrap();
    for (position, &cell) in stream.iter().enumerate() {
        let here = address(&stream, position, 2);
        let reading = tree.receive(&here, cell).unwrap();
        let ideal = oracle.receive(&here, cell).unwrap();
        assert!(within(&reading.executed, &ideal, &reading.residual));
    }
    let chart = tree.chart();
    assert_eq!(chart.carrier, width);
    assert!(chart.rebases > 0);
    assert!(chart.node_rebases > 0 && chart.node_rebases <= chart.rebases);
    assert!(chart.drift > Rat::zero());
    let face = tree.face(&address(&stream, stream.len(), 2), 16).unwrap();
    let sum: Rat = face.probabilities.into_iter().sum();
    assert_eq!(sum, Rat::one());
}

/// **The telescope** on an opened path (Lean `HNN/LandmarkTree.path_telescope_exact`), executed
/// and ideal: `q_0 = q_f · Π_(d<f) q_d/q_(d+1)`, and the edge ratios carry `q_0` to `q_f`.
#[test]
fn landmark_opened_path_telescopes() {
    let stream: Vec<usize> = (0..24u64).map(|t| ((t * 5 + 1) % 4) as usize).collect();
    let mut tree = Landmarks::new(declaration(4, 3)).unwrap();
    let mut oracle = IdealLandmarks::new(declaration(4, 3), None).unwrap();
    for (position, &cell) in stream.iter().enumerate() {
        let here = address(&stream, position, 3);
        for class in 0..4 {
            let paths = tree
                .opened(&here, class)
                .unwrap()
                .into_iter()
                .chain(oracle.opened(&here, class).unwrap());
            for path in paths {
                let last = path.faces.len() - 1;
                let product: Rat = (0..last)
                    .map(|d| &path.faces[d] / &path.faces[d + 1])
                    .product();
                assert_eq!(path.faces[0], &path.faces[last] * product);
                let edges: Rat = path.edge_ratios().into_iter().product();
                assert_eq!(&path.faces[0] * edges, path.faces[last]);
            }
        }
        tree.receive(&here, cell).unwrap();
        oracle.receive(&here, cell).unwrap();
    }
    let founded = tree
        .opened(&address(&stream, stream.len(), 3), stream[0])
        .unwrap();
    assert!(founded.iter().any(|path| path.founded == 4));
}

/// **The certified binary logarithm**: its enclosure meets `log2_enclosure`'s on integers of a few
/// bits to a few hundred, is exact on powers of two, and reaches the enclosure grid's `O` bits.
#[test]
fn landmark_binary_log_is_certified() {
    let values = [
        BigUint::from(3u32),
        BigUint::from(1_000_003u32),
        (BigUint::one() << 200usize) - 1u32,
        (BigUint::one() << 300usize) + 12_345u32,
        BigUint::from(6_148u32).pow(9),
    ];
    for m in values {
        let log = binary_log(&m, 96, |_| false);
        assert!(!log.exact);
        assert_eq!(log.bits, 96);
        let scale = BigInt::one() << log.bits as usize;
        let lower = Rat::new(
            (BigInt::from(log.whole) << log.bits as usize) + BigInt::from(log.fraction),
            scale.clone(),
        );
        let upper = &lower + Rat::new(BigInt::one(), scale);
        let direct = log2_enclosure(&Rat::from_integer(BigInt::from(m.clone()))).unwrap();
        assert!(lower <= direct.upper && direct.lower <= upper, "log₂ {m}");
    }
    let power = binary_log(&(BigUint::one() << 77usize), 96, |_| false);
    assert!(power.exact && power.whole == 77);
}

/// **The code length** ([`code_length`]) of narrow, wide and dyadic faces meets the direct series'
/// enclosure (`log2_enclosure`), is at most `2^(−96)` wide, and is exact on `2^(−k)`.
#[test]
fn landmark_code_length_meets_the_series() {
    let faces = [
        rat(1537, 12298),
        Rat::new(
            (BigInt::one() << 300usize) + BigInt::from(12_345),
            (BigInt::one() << 305usize) - BigInt::from(977),
        ),
        Rat::new(BigInt::from(123_456_789u64), BigInt::one() << 40usize),
        rat(95, 32768),
    ];
    let grid = Rat::new(BigInt::one(), BigInt::one() << 96usize);
    for face in faces {
        let read = code_length(&face).unwrap();
        let direct = log2_enclosure(&face.recip()).unwrap();
        assert!(read.lower <= direct.upper && direct.lower <= read.upper);
        assert!(&read.upper - &read.lower <= grid);
    }
    let exact = code_length(&rat(1, 1 << 20)).unwrap();
    assert_eq!((exact.lower.clone(), exact.upper), (rat(20, 1), rat(20, 1)));
}

/// **The derived widths** at the standing real cut's scope (`n* = 6,148`, `L_R = 16`, `B = 8`):
/// at `D = 4`, `M_p = 39` (`2^38 < 3·8·16·12298·98377 ≤ 2^39`), `W = 28`
/// (`2^27 < 12·8·16·6148·16 ≤ 2^28`) and `C = 67`; the rule's residual per cell lies below half a
/// grain; the reference oracle's width is `96 + 34`.
#[test]
fn landmark_widths_follow_the_passage_and_the_grain() {
    assert_eq!(face_bits(6_148, 8, 16, 4), 39);
    assert_eq!(carrier_width(6_148, 8, 16, 4), 28);
    assert_eq!(face_bits(6_148, 8, 16, 1), 35);
    assert_eq!(carrier_width(6_148, 8, 16, 1), 24);
    let declared = LandmarkDeclaration {
        population: 6_148,
        ..declaration(256, 4)
    };
    let tree = Landmarks::new(declared.clone()).unwrap();
    let widths = tree.widths();
    assert_eq!(
        (
            widths.digits,
            widths.face,
            widths.carrier,
            widths.certificate
        ),
        (8, 39, 28, 67)
    );
    assert!(tree.face_rule() < rat(1, 32));
    assert_eq!(IdealLandmarks::reference_width(&declared), 130);
}

/// **The stored bits** (`ClassMasses::bits`' style): the empty tree stores one bit a splitting
/// dyadic cell;
/// one arrival at depth 1 over two classes founds a root (masses `3/2`, `1/2` and `β = 1`) and
/// a leaf (masses only) behind the letter `Boundary`.
#[test]
fn landmark_bits_count_the_stored_parts() {
    let mut tree = Landmarks::new(declaration(2, 1)).unwrap();
    assert_eq!(tree.bits(), 1);
    tree.receive(&[Letter::Boundary], 0).unwrap();
    // masses 2C = 3 and 1: (2 + 2) + (1 + 2) each node; β = 1/1·2^0: 2 + 2 + 2 + 1; letter 0: 2.
    let masses = (2 + 2) + (1 + 2);
    assert_eq!(tree.bits(), 2 * masses + 7 + 2 + 1);
}

/// **Score then deposit is receive**, and a clone compares equal (the arena's table as a map).
#[test]
fn landmark_score_and_deposit_is_receive() {
    let stream: Vec<usize> = (0..50u64)
        .map(|t| ((t * 11 + t / 7) % 6) as usize)
        .collect();
    let mut once = Landmarks::new(declaration(6, 2)).unwrap();
    let mut twice = once.clone();
    for (position, &cell) in stream.iter().enumerate() {
        let here = address(&stream, position, 2);
        let reading = once.receive(&here, cell).unwrap();
        assert_eq!(twice.score(&here, cell).unwrap(), reading);
        twice.deposit(&here, cell).unwrap();
        assert_eq!(once, twice);
    }
    assert_eq!(once.clone(), once);
    assert_eq!(once.passed(), stream.len() as u64);
}

/// **The refusals**: an address of the wrong depth, a class or letter outside the chart, a forced
/// depth past the address, a passage past the declared population, each before anything moves; and
/// widths whose operands would outgrow `u128`.
#[test]
fn landmark_refusals() {
    let mut tree = Landmarks::new(LandmarkDeclaration {
        population: 2,
        ..declaration(3, 1)
    })
    .unwrap();
    assert!(matches!(tree.receive(&[], 0), Err(HnnError::Shape { .. })));
    assert!(matches!(
        tree.receive(&[Letter::Boundary], 3),
        Err(HnnError::CellOutside { .. })
    ));
    assert!(matches!(
        tree.receive(&[Letter::Cell(5)], 0),
        Err(HnnError::CellOutside { .. })
    ));
    assert_eq!(tree.nodes(), 0);
    tree.receive(&[Letter::Boundary], 0).unwrap();
    tree.receive(&[Letter::Cell(0)], 1).unwrap();
    let before = tree.clone();
    assert_eq!(
        tree.receive(&[Letter::Cell(1)], 2),
        Err(HnnError::PopulationReached { population: 2 })
    );
    assert_eq!(tree, before);
    assert!(
        Landmarks::new(LandmarkDeclaration {
            forced: 2,
            ..declaration(3, 1)
        })
        .is_err()
    );
    assert!(
        Landmarks::new(LandmarkDeclaration {
            population: 1 << 30,
            grain: 1 << 20,
            ..declaration(1 << 20, 64)
        })
        .is_err()
    );
}

/// **The prequential measurement**: the development and held-out sums are the replay's per-cell
/// code lengths of the executed faces; the depth sweep reads the development cells only (changing
/// the held-out cells changes no reading) and charges `⌈log₂⌉` of the family tried.
#[test]
fn landmark_prequential_partitions_the_cut() {
    let cells: Vec<usize> = (0..48u64).map(|t| ((t * 3 + t / 5) % 4) as usize).collect();
    let tail = 36..48;
    let cut = Cut {
        cells: cells.clone(),
        held_out: vec![tail],
    };
    let declared = declaration(4, 2);
    let run = prequential(&cut, &declared).unwrap();
    assert_eq!(run.development.cells, 36);
    assert_eq!(run.held_out.cells, 12);
    let mut tree = Landmarks::new(declared.clone()).unwrap();
    let mut sums = [Rat::zero(), Rat::zero(), Rat::zero(), Rat::zero()];
    for (position, &cell) in cells.iter().enumerate() {
        let reading = tree.receive(&address(&cells, position, 2), cell).unwrap();
        let length = code_length(&reading.executed).unwrap();
        let part = 2 * usize::from(position >= 36);
        sums[part] += length.lower;
        sums[part + 1] += length.upper;
    }
    assert!(run.development.tree.lower <= sums[0] && sums[1] <= run.development.tree.upper);
    assert!(run.held_out.tree.lower <= sums[2] && sums[3] <= run.held_out.tree.upper);
    assert_eq!(run.run.nodes, tree.nodes());
    assert_eq!(run.run.bits, tree.bits());
    assert!(run.run.largest_residual <= run.run.face_rule);

    let sweep = choose_depth(&cut, &declared).unwrap();
    let mut other = cut.clone();
    for cell in &mut other.cells[36..] {
        *cell = 3 - *cell;
    }
    assert_eq!(choose_depth(&other, &declared).unwrap(), sweep);
    assert!(!sweep.tried.is_empty());
    assert_eq!(
        sweep.description_bits,
        crate::compression::cost::ceil_log2(&BigUint::from(sweep.tried.len()))
    );
}
