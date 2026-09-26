//! The landmark tree (Decision 28, count-only) on its declared dyadic lattice: the reference
//! oracle on the Willems–Shtarkov–Tjalkens fixture and the block recursion; the executed face's
//! exact normalization (a chart of five classes, so the odometer digits prune), its lattice law
//! against a recomputation in ℚ, and its certificate against the oracle cell by cell; the stop
//! weight's rounding; the β chart's rebase and its certified residual; the opened path's telescope;
//! the certified binary logarithm and the grain exponents; the derived widths; the stored bits;
//! score and deposit against receive; a window's faces in cell order on a working overlay against
//! the deposited tree; the refusals; and the prequential measurement. Campaign 2: the enlarged tree
//! addressed by typed bundles (its faces normalized and certified against the oracle with its join,
//! the cell-only branch kept within one bit a dyadic cell, a window in cell order, the letters
//! refused outside their family), the carrier's rebase with its enclosure, and a declaration past
//! the old `u128` refusal whose certified residual stays within the grain.

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

use crate::hnn::HnnError;
use crate::hnn::landmark::{
    Beta, Bundle, Feature, IdealLandmarks, LandmarkDeclaration, LandmarkFace, Landmarks, Letter,
    LetterFamily, address, binary_log, carrier_width, cell_letters, choose_depth, code_length,
    face_bits, letter_address, prequential,
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
        family: LetterFamily::cells(),
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

/// **The stored bits**: the empty tree stores one bit a splitting dyadic cell; one arrival at depth
/// 1 over two classes founds a root (masses `3/2`, `1/2` and `β = 1`) and a leaf (masses only)
/// behind the letter `Boundary`.
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

/// **A window's faces in cell order** (`Landmarks::window_faces`): phase `j` reads the face of a
/// clone into which the earlier phases' targets were deposited, exactly, founded nodes and rebased
/// charts included (a narrow carrier forces rebases); the tree is unchanged; with nothing known
/// every phase reads the current standing; the window past the declared population is still read
/// (a deposit's re-read at its successor), and a bad class is refused.
#[test]
fn landmark_window_faces_read_each_phase_after_the_earlier_deposits() {
    let stream: Vec<usize> = (0..90u64)
        .map(|t| ((t * 7 + t / 3 + t * t / 11) % 5) as usize)
        .collect();
    let declared = LandmarkDeclaration {
        population: 90,
        ..declaration(5, 2)
    };
    let mut tree = Landmarks::with_carrier(declared.clone(), 6).unwrap();
    let aperture = 3;
    for start in (0..stream.len()).step_by(aperture) {
        let window = start..(start + aperture).min(stream.len());
        let addresses: Vec<Vec<Letter>> = window
            .clone()
            .map(|position| address(&stream, position, 2))
            .collect();
        let known = &stream[window.clone()];
        let before = tree.clone();
        let faces = tree.window_faces(&addresses, known, 16).unwrap();
        assert_eq!(tree, before, "the tree is unchanged");
        let mut deposited = tree.clone();
        for (j, (here, &cell)) in addresses.iter().zip(known).enumerate() {
            assert_eq!(faces[j], deposited.face(here, 16).unwrap(), "phase {j}");
            deposited.deposit(here, cell).unwrap();
        }
        let unknown = tree.window_faces(&addresses, &[], 16).unwrap();
        for (face, here) in unknown.iter().zip(&addresses) {
            assert_eq!(face, &tree.face(here, 16).unwrap());
        }
        tree = deposited;
    }
    assert!(tree.chart().rebases > 0, "the narrow carrier rebased");
    assert_eq!(tree.passed(), 90);
    // Past the population: the window's earlier cells are read again, as a re-read does.
    let last = [address(&stream, 88, 2), address(&stream, 89, 2)];
    let again = tree.window_faces(&last, &stream[88..90], 16).unwrap();
    assert_eq!(again.len(), 2);
    assert!(matches!(
        tree.window_faces(&last, &[5, 0], 16),
        Err(HnnError::CellOutside { .. })
    ));
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
    let run = prequential(&cut, &cell_letters(&cut.cells), &declared).unwrap();
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

    let sweep = choose_depth(&cut, &cell_letters(&cut.cells), &declared).unwrap();
    let mut other = cut.clone();
    for cell in &mut other.cells[36..] {
        *cell = 3 - *cell;
    }
    assert_eq!(
        choose_depth(&other, &cell_letters(&other.cells), &declared).unwrap(),
        sweep
    );
    assert!(!sweep.tried.is_empty());
    assert_eq!(
        sweep.description_bits,
        crate::compression::cost::ceil_log2(&BigUint::from(sweep.tried.len()))
    );
}

// -------------------------------------------------------------------------------------------
// campaign 2: typed bundles, the enlarged tree that keeps the cell-only branch, and the carrier

/// A family of two phase slots (grains 3 and 2).
fn phase_family() -> LetterFamily {
    LetterFamily::new(vec![
        Feature::Phase { ring: 0, grain: 3 },
        Feature::Phase { ring: 1, grain: 2 },
    ])
    .unwrap()
}

/// Each tick's bundle: its cell with the features `(i mod 3, ⌊i/3⌋ mod 2)`.
fn bundles(stream: &[usize], family: &LetterFamily) -> Vec<Letter> {
    stream
        .iter()
        .enumerate()
        .map(|(i, &cell)| {
            Letter::Bundle(Bundle {
                cell,
                features: family
                    .encode(&[(i % 3) as u64, ((i / 3) % 2) as u64])
                    .unwrap(),
            })
        })
        .collect()
}

fn bundle_declaration(alphabet: usize, depth: usize) -> LandmarkDeclaration {
    LandmarkDeclaration {
        family: phase_family(),
        ..declaration(alphabet, depth)
    }
}

/// **The enlarged tree's faces are normalized and certified** (Lean `HNN/LandmarkTree.{
/// lattice_path_laws, cell_faces_partition, executed_face_bound}`, `HNN/LandmarkAddress`): with a
/// declared family each dyadic cell joins the cell tree and the bundle tree, and at every step the
/// all-class face sums to 1 exactly, each class's face is the one-class read and a dyadic of at
/// most `B · M_p` bits, each grain exponent is `grain_exponent`'s, the splits rebuild the face, the
/// ideal oracle (the join in ℚ) sums to 1, and each cell's certificate lies within the rule and
/// holds against the oracle.
#[test]
fn landmark_bundle_tree_is_normalized_and_certified() {
    let alphabet = 5;
    let stream: Vec<usize> = (0..60u64).map(|t| ((t * 7 + t / 3) % 5) as usize).collect();
    for forced in [0, 1] {
        let declared = LandmarkDeclaration {
            forced,
            ..bundle_declaration(alphabet, 2)
        };
        let letters = bundles(&stream, &declared.family);
        let mut tree = Landmarks::new(declared.clone()).unwrap();
        let mut oracle = IdealLandmarks::new(declared.clone(), None).unwrap();
        assert_eq!(declared.branch_depths(), vec![2, 6]);
        assert_eq!(declared.path_depth(), 10);
        assert!(tree.face_rule() < rat(1, 32));
        let bits = tree.digits() * tree.face_bits();
        for (position, &cell) in stream.iter().enumerate() {
            let here = letter_address(&letters, position, 2);
            let face = tree.face(&here, 16).unwrap();
            let sum: Rat = face.probabilities.iter().cloned().sum();
            assert_eq!(sum, Rat::one());
            let rebuilt =
                LandmarkFace::of_splits(&declared, &tree.splits(&here).unwrap(), 16).unwrap();
            assert_eq!(rebuilt, face);
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
        // Both branches opened: the cell tree's and the bundle tree's paths.
        let here = letter_address(&letters, stream.len(), 2);
        let paths = tree.opened(&here, 3).unwrap();
        assert!(paths.iter().any(|path| path.branch == 0));
        assert!(paths.iter().any(|path| path.branch == 1));
    }
}

/// **The enlarged tree keeps the cell-only branch** (Lean
/// `HNN/LandmarkAddress.cell_only_dominance_with_feature_charge`, on the ideal oracles with `β`
/// exact): over any stream the join at each dyadic cell is the sequential mixture of the two
/// branches (`sequential_mixture`), so the enlarged code is at most the cell tree's plus one bit per
/// dyadic cell opened, `∏ q_enlarged · 2^H ≥ ∏ q_cells`. And where the features carry what the
/// cells do not (the next cell's parity is its tick's phase, which the previous cell leaves plural),
/// the enlarged executed tree codes strictly shorter, by disjoint exact enclosures.
#[test]
fn landmark_enlarged_tree_keeps_the_cell_only_branch() {
    let mut draw = super::support::Draw::new(5);
    let stream: Vec<usize> = (0..240)
        .map(|i| 2 * (draw.next() % 2) as usize + usize::from(i % 3 == 0))
        .collect();
    let cells_only = LandmarkDeclaration {
        population: 240,
        ..declaration(4, 1)
    };
    let enlarged = LandmarkDeclaration {
        population: 240,
        ..bundle_declaration(4, 1)
    };
    let letters = bundles(&stream, &enlarged.family);
    let mut cell_oracle = IdealLandmarks::new(cells_only.clone(), None).unwrap();
    let mut oracle = IdealLandmarks::new(enlarged.clone(), None).unwrap();
    let (mut product, mut cell_product) = (Rat::one(), Rat::one());
    let mut opened = std::collections::BTreeSet::new();
    for (position, &cell) in stream.iter().enumerate() {
        product *= oracle
            .receive(&letter_address(&letters, position, 1), cell)
            .unwrap();
        cell_product *= cell_oracle
            .receive(&address(&stream, position, 1), cell)
            .unwrap();
        for path in oracle
            .opened(&letter_address(&letters, position, 1), cell)
            .unwrap()
        {
            opened.insert(path.dyadic);
        }
        let joins = Rat::from_integer(BigInt::one() << opened.len());
        assert!(&product * joins >= cell_product, "cell {position}");
    }
    // The features carry the parity: the enlarged executed tree codes shorter than the cell tree.
    let executed = |declared: &LandmarkDeclaration, letters: &[Letter]| {
        let mut tree = Landmarks::new(declared.clone()).unwrap();
        let mut sum = crate::ratio::algebraic::ExactInterval::point(Rat::zero());
        for (position, &cell) in stream.iter().enumerate() {
            let reading = tree
                .receive(&letter_address(letters, position, 1), cell)
                .unwrap();
            sum = crate::hnn::ratio::interval_sum(&sum, &code_length(&reading.executed).unwrap())
                .unwrap();
        }
        sum
    };
    let with_letters = executed(&enlarged, &letters);
    let cells = executed(&cells_only, &cell_letters(&stream));
    assert!(with_letters.upper < cells.lower);
}

/// **A window's faces in cell order on the enlarged tree** (`Landmarks::window_faces`): phase `j`
/// reads exactly the face of a clone into which the earlier phases' targets were deposited, the
/// joins included; the tree is unchanged.
#[test]
fn landmark_bundle_window_faces_read_each_phase_after_the_earlier_deposits() {
    let stream: Vec<usize> = (0..60u64)
        .map(|t| ((t * 7 + t / 3 + t * t / 11) % 5) as usize)
        .collect();
    let declared = LandmarkDeclaration {
        population: 60,
        ..bundle_declaration(5, 2)
    };
    let letters = bundles(&stream, &declared.family);
    let mut tree = Landmarks::with_carrier(declared, 6).unwrap();
    for start in (0..stream.len()).step_by(3) {
        let window = start..(start + 3).min(stream.len());
        let addresses: Vec<Vec<Letter>> = window
            .clone()
            .map(|position| letter_address(&letters, position, 2))
            .collect();
        let known = &stream[window];
        let before = tree.clone();
        let faces = tree.window_faces(&addresses, known, 16).unwrap();
        assert_eq!(tree, before);
        let mut deposited = tree.clone();
        for (j, (here, &cell)) in addresses.iter().zip(known).enumerate() {
            assert_eq!(faces[j], deposited.face(here, 16).unwrap(), "phase {j}");
            deposited.deposit(here, cell).unwrap();
        }
        tree = deposited;
    }
    assert!(tree.chart().rebases > 0);
}

/// **The letters are refused outside their family**: a cell letter where bundles are declared, a
/// bundle where cells are, and a bundle's features past the family's codes.
#[test]
fn landmark_letters_are_refused_outside_their_family() {
    let mut cells = Landmarks::new(declaration(3, 1)).unwrap();
    let bundle = Letter::Bundle(Bundle {
        cell: 0,
        features: 0,
    });
    assert!(matches!(
        cells.receive(&[bundle], 0),
        Err(HnnError::Shape { .. })
    ));
    let mut tree = Landmarks::new(bundle_declaration(3, 1)).unwrap();
    assert!(matches!(
        tree.receive(&[Letter::Cell(0)], 0),
        Err(HnnError::Shape { .. })
    ));
    let past = Letter::Bundle(Bundle {
        cell: 0,
        features: 6,
    });
    assert!(matches!(
        tree.receive(&[past], 0),
        Err(HnnError::Shape { .. })
    ));
    tree.receive(&[bundle], 0).unwrap();
    tree.receive(&[Letter::Boundary], 1).unwrap();
}

/// **The carrier rebases with its enclosure** (Lean `HNN/LandmarkCarrier.{rebase_decode,
/// rebase_ratio_enclosed}`, `HNN/LandmarkTree.rebase_log_residual`): at the widths of a 131,072-cell
/// declaration (`W = 32`, `R = 94`) a β step whose carrier `(N, D)` has a 99-bit odd denominator
/// passes the mantissa's division, so `D` rebases to its top `R` bits and releases its remainder;
/// the carried `β'` lies in `[v(1 − 1/m'), v(1 + 1/D̂))` of the exact step `v`, and a carrier within
/// the division is carried as before.
#[test]
fn landmark_carrier_rebases_with_its_enclosure() {
    let (width, rebase) = (32u64, 94u64);
    // β = (2^31 + 1)/(2^32 − 1), a KT face 262,145/262,146 in half-units, a child face near 2^48.
    let (beta_n, beta_d) = ((1u128 << 31) + 1, (1u128 << 32) - 1);
    let (u, v, below) = (262_145u128, 262_146u128, (1u128 << 48) - 59);
    let (numerator, denominator) = (beta_n * u, beta_d * v * below);
    assert!(width + 128 - u64::from(denominator.leading_zeros()) > 128);
    let carried = Beta::step(numerator, denominator, 48, width, rebase);
    let kept = carried.released.expect("the carrier rebased");
    let mantissa = carried.mantissa.expect("a mantissa");
    assert_eq!(128 - kept.leading_zeros(), 94);
    let exact = Rat::new(
        BigInt::from(numerator) << 48usize,
        BigInt::from(denominator),
    );
    let value = carried.beta.value();
    let one = Rat::one();
    assert!(value < &exact * (&one + Rat::new(BigInt::one(), BigInt::from(kept))));
    assert!(value >= &exact * (&one - Rat::new(BigInt::one(), BigInt::from(mantissa))));
    // Within the division the step is `carry`'s, exact or at its mantissa, releasing nothing.
    let small = Beta::step(1000, 7, 0, 4, 0);
    assert!(small.released.is_none());
    assert_eq!((small.beta, small.mantissa), Beta::carry(1000, 7, 0, 4));
}

/// **The tree declares past the old refusal and stays within its grain** (Sol's review §4; Lean
/// `HNN/LandmarkCarrier.width_or_rebase_total`): campaign 1's `|A| = 256`, `D = 4`, `L_R = 16` was
/// refused from 87,382 cells, where the β step's product `2W + κ + M_p + 1` passed 128 bits. At
/// 131,072 cells the widths stay the rule's (`M_p = 48`, `W = 32`, never reduced), the carrier
/// rebases at `R = 94` bits, and over the whole passage every cell's certified residual lies within
/// the rule, which lies below half the declared grain; the declaration reaches `2^19` cells.
#[test]
fn landmark_tree_declares_past_the_old_refusal_and_stays_within_the_grain() {
    let population = 131_072u64;
    let declared = LandmarkDeclaration {
        population,
        ..declaration(256, 4)
    };
    let mut tree = Landmarks::new(declared.clone()).unwrap();
    let widths = tree.widths();
    assert_eq!(widths.face, face_bits(population, 8, 16, 4));
    assert_eq!(widths.carrier, carrier_width(population, 8, 16, 4));
    assert_eq!((widths.face, widths.carrier, widths.rebase), (48, 32, 94));
    let kappa = 64 - (2 * population + 2).leading_zeros() as u64;
    assert!(
        2 * widths.carrier + kappa + widths.face + 1 > 128,
        "the old refusal"
    );
    let rule = tree.face_rule();
    assert!(rule < rat(1, 32));
    // The declaration reaches 2^19 cells before a lattice product itself passes 128 bits.
    assert!(
        Landmarks::new(LandmarkDeclaration {
            population: 1 << 19,
            ..declaration(256, 4)
        })
        .is_ok()
    );
    // A text-like passage: words drawn from a small vocabulary, separated by spaces.
    let mut draw = super::support::Draw::new(1_024);
    let words: Vec<Vec<usize>> = (0..96)
        .map(|_| {
            let length = 2 + (draw.next() % 7) as usize;
            (0..length)
                .map(|_| 97 + (draw.next() % 26) as usize)
                .collect()
        })
        .collect();
    let mut stream = Vec::with_capacity(population as usize);
    while stream.len() < population as usize {
        let word = &words[(draw.next() % 96) as usize];
        stream.extend(word.iter().copied().chain([32]));
    }
    stream.truncate(population as usize);
    let mut largest = Rat::zero();
    for (position, &cell) in stream.iter().enumerate() {
        let reading = tree.receive(&address(&stream, position, 4), cell).unwrap();
        if reading.residual > largest {
            largest = reading.residual;
        }
    }
    assert!(largest <= rule);
    assert_eq!(tree.passed(), population);
    let chart = tree.chart();
    assert!(chart.drift <= rule);
    println!(
        "131,072 cells: {} nodes, {} rebases, {} carrier releases, largest residual {largest} bits, rule {rule} bits",
        tree.nodes(),
        chart.rebases,
        chart.released
    );
    assert!(matches!(
        tree.receive(&address(&stream, 0, 4), 0),
        Err(HnnError::PopulationReached { .. })
    ));
}
