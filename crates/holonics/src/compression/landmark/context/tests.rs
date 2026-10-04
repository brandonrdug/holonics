//! The landmark tree (count-only) on its declared dyadic lattice: the reference
//! oracle on the Willems–Shtarkov–Tjalkens fixture and the block recursion; the executed face's
//! exact normalization (a chart of five classes, so the odometer digits prune), its lattice law
//! against a recomputation in ℚ, and its certificate against the oracle cell by cell; the stop
//! weight's rounding; the β chart's rebase and its certified residual; the opened path's telescope;
//! the certified binary logarithm and the grain exponents; the derived widths; the stored bits;
//! score and deposit against receive; a window's faces in cell order on a working overlay against
//! the deposited tree; the refusals; the code length of faces and passages; and the online context
//! baselines (the prequential measurement on a cut and the development choices are the exposure's,
//! tested in `hnn::tests::reference`). Campaign 2: the enlarged tree
//! addressed by typed bundles (its faces normalized and certified against the oracle with its join,
//! the cell-only branch kept within one bit a dyadic cell, a window in cell order, the letters
//! refused outside their family), the carrier's rebase with its enclosure, and a declaration past
//! the old `u128` refusal whose certified residual stays within the grain. The declared stop prior on the
//! dyadic ladder (the block recursion at any stop weights, the founding ratio
//! `2^j − 1`, the lattice law, the faces and windows under a prior), campaign 2's constant-slot
//! controls as the per-depth prior `(1, r + 1)`.
//! Local weighing: the join tree's prior; the joins as the Bayesian mixture per dyadic cell; and the
//! stop-weight mixture per digit tree telescoping per dyadic cell (the node-local law is retired,
//! its realization and tests at commit `89460425`). The storage where paths part (the one
//! storage): the oracle stored where paths part against the full tree of one node a depth
//! (`landmark_full`, the tests' independent reference), exact in ℚ at depths past the stream's
//! recurrence (under the stop priors, forced depths and on both branches of the enlarged tree), the executed tree within its carried certificate with at most `2n − 1`
//! nodes a tree, its windows in cell order, the split's ratios against their exact forms, and its
//! stored parts. A landmark's storage has a capacity: the unbounded register and any
//! ceiling no node reaches are the uncapped tree exactly; the capped oracle equals the
//! naive tree of one register a depth (`landmark_full`) exactly in ℚ, register for register along
//! every opened path, with chains split after their registers carried; the capped executed tree
//! within its certificate; and its windows in cell order.

mod full;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

use crate::compression::landmark::context::baseline::{Baselines, Ppm, kt_probability};
use crate::compression::landmark::context::{
    Beta, Bundle, Capacity, ContextError, DigitsReading, FaceJoins, IdealLandmarks, JoinTree,
    LandmarkDeclaration, LandmarkFace, Landmarks, Letter, LetterFamily, PassageCode, StopMixture,
    StopPrior, Widths, address, binary_log, carrier_width, cell_letters, code_length, face_bits,
    ladder_top, lattice_mix, letter_address, odometer_digits, prior_family, ratio_code_length,
};
use crate::ratio::algebraic::{ExactInterval, interval_sum, log2_enclosure};
use crate::ratio::{Rat, rat};
use crate::receiver::face::grain_exponent;
use full::FullTree;

/// The seeded exact draw, for deterministic streams and operands (the terrain owner's).
pub(super) use crate::holarchy::terrain::Draw;

/// **A window's faces in cell order**, read phase by phase through [`Landmarks::window`].
fn window_faces(
    tree: &Landmarks,
    addresses: &[Vec<Letter>],
    known: &[usize],
    grain: u64,
) -> Result<Vec<LandmarkFace>, ContextError> {
    let window = tree.window(addresses, known)?;
    (0..window.phases())
        .map(|phase| window.face(phase, grain))
        .collect()
}

fn declaration(alphabet: usize, depth: usize) -> LandmarkDeclaration {
    LandmarkDeclaration {
        alphabet,
        depth,
        forced: 0,
        population: 64,
        grain: 16,
        family: LetterFamily::cells(),
        prior: StopPrior::half(),
        capacity: Capacity::Unbounded,
        mass: 1,
        base: crate::compression::landmark::context::BaseMeasure::Even,
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
/// `W_s = w_d E_s + (1 − w_d) Π_b W_bs` at the node's depth `d` (Lean `Compression/Landmark/Context/Tree.stopWeight`;
/// `½` is the landmark tree's), over the symbols of `stream[past..]` whose context (newest first) extends
/// `context`.
fn block_weight(
    stream: &[usize],
    past: usize,
    context: &[usize],
    depth: usize,
    prior: &StopPrior,
) -> Rat {
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
            block_weight(stream, past, &child, depth, prior)
        })
        .product();
    let stop = prior.weight(context.len());
    &stop * estimate + (Rat::one() - &stop) * split
}

/// The stop priors the laws are checked under: the `½` stop prior, two global rungs and two
/// per-depth laws.
fn priors() -> Vec<StopPrior> {
    vec![
        StopPrior::half(),
        StopPrior::global(2).unwrap(),
        StopPrior::global(5).unwrap(),
        StopPrior::per_depth(vec![1, 3]).unwrap(),
        StopPrior::per_depth(vec![4, 1, 2]).unwrap(),
    ]
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
        assert_eq!(block_weight(&stream, 3, &[], 3, &StopPrior::half()), weight);
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

/// **The sequential path law is the block recursion at any stop prior** (Lean
/// `Compression/Landmark/Context/Tree.{stop_weight_step, stop_founding_step}`; the oracle, `β` exact, founded at
/// `2^(j_d) − 1`) on a longer binary stream at every depth up to 4, and the executed tree stays
/// within its certificate there.
#[test]
fn landmark_oracle_path_law_is_the_block_recursion() {
    let stream: Vec<usize> = (0..24u64)
        .map(|t| usize::from((t * t + 3 * t) % 7 < 3))
        .collect();
    for prior in priors() {
        for depth in 0..=4 {
            let declared = LandmarkDeclaration {
                prior: prior.clone(),
                ..declaration(2, depth)
            };
            let mut oracle = IdealLandmarks::new(declared.clone(), None).unwrap();
            let mut tree = Landmarks::new(declared).unwrap();
            let mut ideal = Rat::one();
            for t in depth..stream.len() {
                let here = address(&stream, t, depth);
                let face = oracle.receive(&here, stream[t]).unwrap();
                let reading = tree.receive(&here, stream[t]).unwrap();
                assert!(within(&reading.executed, &face, &reading.residual));
                ideal *= face;
            }
            assert_eq!(
                ideal,
                block_weight(&stream, depth, &[], depth, &prior),
                "{prior}, D = {depth}"
            );
        }
    }
}

/// **The executed faces are normalized exactly** (Lean `Compression/Landmark/Context/Tree.{lattice_path_laws,
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
    let laws = [StopPrior::half(), StopPrior::per_depth(vec![1, 3]).unwrap()];
    for (forced, prior) in [0, 1]
        .into_iter()
        .flat_map(|f| laws.clone().map(|p| (f, p)))
    {
        let declared = LandmarkDeclaration {
            forced,
            prior,
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

/// **The lattice law, recomputed in ℚ** at every step on every opened path, level by level (each
/// level a stored chain, the storage where paths part): a leaf reads `⟦k_D(0)⟧`, past the last stored level the
/// prior `1/2`, a chain above the forced depths its child, and a mixing chain
/// `⟦λ̂ k(0) + (1 − λ̂) q̂'(0)⟧` with `λ̂ = ⟦β/(1 + β)⟧₀¹`, every face a numerator of `2^(−M_p)`
/// inside `[1, 2^(M_p) − 1]` (Lean `Compression/Landmark/Context/Tree.lattice_path_laws`); after the deposit each
/// mixing chain's `β` (a parting chain's upper part's split `β`) is `β k(b)/q̂'(b)`, or its rebase
/// within `2^(1−W)` below it, and the leaf it founds keeps `D`'s `β₀ = 2^(j_D) − 1`.
#[test]
fn landmark_lattice_faces_follow_the_law() {
    let stream: Vec<usize> = (0..60u64).map(|t| ((t * t + t / 4) % 4) as usize).collect();
    let laws = [
        StopPrior::half(),
        StopPrior::global(3).unwrap(),
        StopPrior::per_depth(vec![1, 4]).unwrap(),
    ];
    for (forced, prior) in [0, 1]
        .into_iter()
        .flat_map(|f| laws.clone().map(|p| (f, p)))
    {
        let mut tree = Landmarks::with_carrier(
            LandmarkDeclaration {
                forced,
                prior: prior.clone(),
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
                    if path.founded == path.faces.len() {
                        assert_eq!(path.bottoms[top], 3);
                        assert_eq!(zero(&path.faces[top]), lattice(&zero(&path.masses[top])));
                    } else {
                        assert_eq!(path.faces[top], rat(1, 2));
                    }
                    for d in 0..top {
                        let expected = if path.bottoms[d] < forced {
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
                let mixing = old.founded.min(old.faces.len() - 1);
                for d in (0..mixing).filter(|&d| old.bottoms[d] >= forced) {
                    let stepped = &old.betas[d] * &old.masses[d] / &old.faces[d + 1];
                    let ratio = &new.betas[d] / &stepped;
                    assert!(ratio <= Rat::one() && ratio > Rat::one() - &rebase);
                }
                // The leaf this arrival founded keeps D's β₀ = 2^(j_D) − 1.
                assert_eq!(new.founded, new.faces.len(), "the arrival ends at a leaf");
                if old.founded < old.faces.len() {
                    assert_eq!(new.founded, old.founded + 1);
                    let founding = BigInt::from(prior.founding(3));
                    assert_eq!(
                        new.betas[old.founded],
                        Rat::from_integer(founding),
                        "{prior}"
                    );
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

/// **The β chart rebases** (Lean `Compression/Landmark/Context/Tree.rebase_log_residual`): a ratio whose odd parts
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

/// **The telescope** on an opened path (Lean `Compression/Landmark/Context/Tree.path_telescope_exact`), executed
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
    assert!(founded.iter().any(|path| path.founded == path.faces.len()));
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
/// at `D = 4`, `M_p = 39` (`2^38 < 3·8·16·12298·98377 ≤ 2^39`), `W = 29`
/// (`2^28 < 12·8·16·12297·16 ≤ 2^29`, the splits counted: `2n* + 1 = 12297`) and `C = 68`; the rule's
/// residual per cell lies below half a grain; the reference oracle's width is `96 + 34`. At `D = 1`
/// the splits' `4n* P` passes `(n* + 1) P²`: `W = 26` (`2^25 < 12·8·16·30740 ≤ 2^26`,
/// `30740 = n* + 4n* = 2²·5·29·53`), where `(2n* + 1) P²` alone gave `25`.
#[test]
fn landmark_widths_follow_the_passage_and_the_grain() {
    assert_eq!(face_bits(6_148, 8, 16, 4, 1), 39);
    assert_eq!(carrier_width(6_148, 8, 16, 4), 29);
    assert_eq!(face_bits(6_148, 8, 16, 1, 1), 35);
    assert_eq!(carrier_width(6_148, 8, 16, 1), 26);
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
        (8, 39, 29, 68)
    );
    assert!(tree.face_rule() < rat(1, 32));
    assert_eq!(IdealLandmarks::reference_width(&declared), 130);
}

/// **The rule lies below half a grain** (module header, "The widths"; the splits counted in `W`,
/// the storage where paths part): at `n* ∈ {64, 6148, 2^14, 2^17, 2^20}`, `L_R = 16`, `B = 8` and path depths
/// `P ∈ {1, …, 6, 8, 12, 24, 48, 73}`, the lattice's rounding term and the mantissa term
/// `(3/2) B (n* P² + max((n* + 1) P², 4n* P)) 2^(1−W)` (`4n* P`, the splits' count through Lean
/// `StoredDrift.split_charge`, passes `(n* + 1) P²` only at `P ≤ 3`) each lie within a quarter grain, and the rule
/// (`Landmarks::face_rule`) below half a grain, exactly, with the carrier's rebase or without it
/// (both occur on the scan). With `W` from `n*` alone (commit `89460425`) the rule passed half a
/// grain at `n* = 6148`, `D = 5`, where that rule's `W = 28`.
#[test]
fn landmark_rule_lies_below_half_a_grain() {
    let (digits, grain) = (8u64, 16i64);
    let mut rebased = [false; 2];
    for population in [64u64, 6_148, 1 << 14, 1 << 17, 1 << 20] {
        for depth in [1usize, 2, 3, 4, 5, 6, 8, 12, 24, 48, 73] {
            let declared = LandmarkDeclaration {
                population,
                ..declaration(256, depth)
            };
            let tree = Landmarks::new(declared).unwrap();
            let widths = tree.widths();
            let (n, p) = (BigInt::from(population), BigInt::from(depth as u64));
            let floor = (BigInt::one() << widths.face as usize) / (&n * 2 + 2);
            let rounding = Rat::new(&n * &p * &p + &p * 2 + 1, floor * 2);
            let paths = &n * &p * &p;
            let splits = (&paths + &p * &p).max(&n * &p * 4);
            let mantissa = Rat::from_integer(&paths + splits) * rat_power(1 - widths.carrier as i64);
            let quarter = rat(1, 4 * grain);
            let bits = |term: Rat| term * rat(3, 2) * Rat::from_integer(BigInt::from(digits));
            assert!(bits(rounding) <= quarter, "n* = {population}, D = {depth}");
            assert!(bits(mantissa) <= quarter, "n* = {population}, D = {depth}");
            assert!(
                tree.face_rule() < rat(1, 2 * grain),
                "n* = {population}, D = {depth}"
            );
            rebased[usize::from(widths.rebase > 0)] = true;
        }
    }
    assert_eq!(rebased, [true, true]);
    let before = LandmarkDeclaration {
        population: 6_148,
        ..declaration(256, 5)
    };
    let narrow = Landmarks::with_carrier(before, 28).unwrap();
    assert!(narrow.face_rule() > rat(1, 2 * grain));
}

/// **The stored bits**: the empty tree stores one bit a splitting dyadic cell; one arrival at depth
/// 1 over two classes stores one leaf at the root (stored where paths part: masses `3/2`, `1/2`, no `β`, its
/// bottom depth and its label, the one letter `Boundary`); a second arrival behind another letter
/// splits it into the root at depth 0 (founded with the leaf's masses at `β = 2¹ − 1`, then stepped
/// to `3/2` by `k(0)/½`) with two leaves behind their letters, and holds no label letter (its leaf
/// is reached by its letter alone).
#[test]
fn landmark_bits_count_the_stored_parts() {
    let mut tree = Landmarks::new(declaration(2, 1)).unwrap();
    assert_eq!(tree.bits(), 1);
    tree.receive(&[Letter::Boundary], 0).unwrap();
    // masses 2C = 3 and 1: (2 + 2) + (1 + 2); the bottom depth 1 and the label end 1: 2 each; the
    // label's letter 0: 2.
    let masses = (2 + 2) + (1 + 2);
    assert_eq!(tree.bits(), masses + 2 + 2 + 2 + 1);
    assert_eq!((tree.nodes(), tree.held()), (1, 1));
    tree.receive(&[Letter::Cell(1)], 0).unwrap();
    // The root: masses 2C = 5 and 1, (3 + 2) + (1 + 2); β = 3/1·2^(−1): 3 + 2 + 2 + 1; the bottom
    // depth 0 and the label end 0: 2 each. The two leaves: masses 3 and 1, the bottom depth 1 and
    // the label end 1 each; their child letters 0 and 2: 2 and 3; the pool's one letter 0: 2.
    let root = (3 + 2) + (1 + 2) + (3 + 2 + 2 + 1) + 2 + 2;
    let leaves = 2 * (masses + 2 + 2);
    assert_eq!(tree.bits(), root + leaves + (2 + 3) + 2 + 1);
    assert_eq!((tree.nodes(), tree.held()), (3, 1));
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

/// **A window's faces in cell order** (`Landmarks::window`): phase `j` reads the face of a
/// clone into which the earlier phases' targets were deposited, exactly, founded nodes and rebased
/// charts included (a narrow carrier forces rebases); the tree is unchanged; with nothing known
/// every phase reads the current standing; the window past the declared population is still read
/// (a deposit's re-read at its successor), and a bad class is refused.
#[test]
fn landmark_window_faces_read_each_phase_after_the_earlier_deposits() {
    let stream: Vec<usize> = (0..90u64)
        .map(|t| ((t * 7 + t / 3 + t * t / 11) % 5) as usize)
        .collect();
    for prior in [StopPrior::half(), StopPrior::per_depth(vec![2, 5]).unwrap()] {
        window_in_cell_order(&stream, prior, 2, Capacity::Unbounded);
    }
}

/// One stop prior's run of `landmark_window_faces_read_each_phase_after_the_earlier_deposits` at a
/// depth and a capacity.
fn window_in_cell_order(stream: &[usize], prior: StopPrior, depth: usize, capacity: Capacity) {
    let declared = LandmarkDeclaration {
        population: 90,
        prior,
        capacity,
        ..declaration(5, depth)
    };
    let mut tree = Landmarks::with_carrier(declared.clone(), 6).unwrap();
    let aperture = 3;
    for start in (0..stream.len()).step_by(aperture) {
        let window = start..(start + aperture).min(stream.len());
        let addresses: Vec<Vec<Letter>> = window
            .clone()
            .map(|position| address(stream, position, depth))
            .collect();
        let known = &stream[window.clone()];
        let before = tree.clone();
        let faces = window_faces(&tree, &addresses, known, 16).unwrap();
        assert_eq!(tree, before, "the tree is unchanged");
        let mut deposited = tree.clone();
        for (j, (here, &cell)) in addresses.iter().zip(known).enumerate() {
            assert_eq!(faces[j], deposited.face(here, 16).unwrap(), "phase {j}");
            deposited.deposit(here, cell).unwrap();
        }
        let unknown = window_faces(&tree, &addresses, &[], 16).unwrap();
        for (face, here) in unknown.iter().zip(&addresses) {
            assert_eq!(face, &tree.face(here, 16).unwrap());
        }
        tree = deposited;
    }
    assert!(tree.chart().rebases > 0, "the narrow carrier rebased");
    assert_eq!(tree.passed(), 90);
    // Past the population: the window's earlier cells are read again, as a re-read does.
    let last = [address(stream, 88, depth), address(stream, 89, depth)];
    let again = window_faces(&tree, &last, &stream[88..90], 16).unwrap();
    assert_eq!(again.len(), 2);
    assert!(matches!(
        window_faces(&tree, &last, &[5, 0], 16),
        Err(ContextError::CellOutside { .. })
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
    assert!(matches!(
        tree.receive(&[], 0),
        Err(ContextError::Extent { .. })
    ));
    assert!(matches!(
        tree.receive(&[Letter::Boundary], 3),
        Err(ContextError::CellOutside { .. })
    ));
    assert!(matches!(
        tree.receive(&[Letter::Cell(5)], 0),
        Err(ContextError::CellOutside { .. })
    ));
    assert_eq!(tree.nodes(), 0);
    tree.receive(&[Letter::Boundary], 0).unwrap();
    tree.receive(&[Letter::Cell(0)], 1).unwrap();
    let before = tree.clone();
    assert_eq!(
        tree.receive(&[Letter::Cell(1)], 2),
        Err(ContextError::PopulationReached { population: 2 })
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

// -------------------------------------------------------------------------------------------
// campaign 2: typed bundles, the enlarged tree that keeps the cell-only branch, and the carrier

/// A family of two phase slots (grains 3 and 2).
fn phase_family() -> LetterFamily {
    LetterFamily::new(vec![3, 2]).unwrap()
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

/// **The enlarged tree's faces are normalized and certified** (Lean `Compression/Landmark/Context/Tree.{
/// lattice_path_laws, cell_faces_partition, executed_face_bound}`, `Compression/Landmark/Context/Address`): with a
/// declared family each dyadic cell joins the cell tree and the bundle tree, and at every step the
/// all-class face sums to 1 exactly, each class's face is the one-class read and a dyadic of at
/// most `B · M_p` bits, each grain exponent is `grain_exponent`'s, the splits rebuild the face, the
/// ideal oracle (the join in ℚ) sums to 1, and each cell's certificate lies within the rule and
/// holds against the oracle.
#[test]
fn landmark_bundle_tree_is_normalized_and_certified() {
    let alphabet = 5;
    let stream: Vec<usize> = (0..60u64).map(|t| ((t * 7 + t / 3) % 5) as usize).collect();
    let laws = [StopPrior::half(), StopPrior::global(3).unwrap()];
    for (forced, prior) in [0, 1]
        .into_iter()
        .flat_map(|f| laws.clone().map(|p| (f, p)))
    {
        let declared = LandmarkDeclaration {
            forced,
            prior,
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
/// `Compression/Landmark/Context/Address.cell_only_dominance_with_feature_charge`, on the ideal oracles with `β`
/// exact): over any stream the join at each dyadic cell is the sequential mixture of the two
/// branches (`sequential_mixture`), so the enlarged code is at most the cell tree's plus one bit per
/// dyadic cell opened, `∏ q_enlarged · 2^H ≥ ∏ q_cells`. And where the features carry what the
/// cells do not (the next cell's parity is its tick's phase, which the previous cell leaves plural),
/// the enlarged executed tree codes strictly shorter, by disjoint exact enclosures.
#[test]
fn landmark_enlarged_tree_keeps_the_cell_only_branch() {
    let mut draw = Draw::new(5);
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
            sum = interval_sum(&sum, &code_length(&reading.executed).unwrap()).unwrap();
        }
        sum
    };
    let with_letters = executed(&enlarged, &letters);
    let cells = executed(&cells_only, &cell_letters(&stream));
    assert!(with_letters.upper < cells.lower);
    // The executed passage bound (`passage_join_bound`, the dominance's third clause): within one
    // bit a dyadic cell opened of the cell tree's code, plus both trees' certified drift (the rule
    // a cell times the cells).
    let drift = (Landmarks::new(enlarged.clone()).unwrap().face_rule()
        + Landmarks::new(cells_only.clone()).unwrap().face_rule())
        * Rat::from_integer(BigInt::from(stream.len()));
    assert!(
        with_letters.upper <= &cells.lower + Rat::from_integer(BigInt::from(opened.len())) + drift
    );
}

/// **A window's faces in cell order on the enlarged tree** (`Landmarks::window`): phase `j`
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
        let faces = window_faces(&tree, &addresses, known, 16).unwrap();
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
        Err(ContextError::Extent { .. })
    ));
    let mut tree = Landmarks::new(bundle_declaration(3, 1)).unwrap();
    assert!(matches!(
        tree.receive(&[Letter::Cell(0)], 0),
        Err(ContextError::Extent { .. })
    ));
    let past = Letter::Bundle(Bundle {
        cell: 0,
        features: 6,
    });
    assert!(matches!(
        tree.receive(&[past], 0),
        Err(ContextError::Extent { .. })
    ));
    tree.receive(&[bundle], 0).unwrap();
    tree.receive(&[Letter::Boundary], 1).unwrap();
}

/// **The carrier rebases with its enclosure** (Lean `Compression/Landmark/Context/Carrier.{rebase_decode,
/// rebase_ratio_enclosed}`, `Compression/Landmark/Context/Tree.rebase_log_residual`): at the carrier `W = 32` with
/// the rebase `R = 94` a β step whose carrier `(N, D)` has a 99-bit odd denominator
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
/// `Compression/Landmark/Context/Carrier.width_or_rebase_total`): campaign 1's `|A| = 256`, `D = 4`, `L_R = 16` was
/// refused from 87,382 cells, where the β step's product `2W + κ + M_p + 1` passed 128 bits. At
/// 131,072 cells the widths stay the rule's (`M_p = 48`, `W = 33`, never reduced), the carrier
/// rebases at `R = 93` bits, and over the whole passage every cell's certified residual lies within
/// the rule, which lies below half the declared grain; the declaration reaches `2^19` cells (and,
/// with the split operands, `2^24`: `landmark_split_operands_are_the_single_division`).
#[test]
fn landmark_tree_declares_past_the_old_refusal_and_stays_within_the_grain() {
    let population = 131_072u64;
    let declared = LandmarkDeclaration {
        population,
        ..declaration(256, 4)
    };
    let mut tree = Landmarks::new(declared.clone()).unwrap();
    let widths = tree.widths();
    assert_eq!(widths.face, face_bits(population, 8, 16, 4, 1));
    assert_eq!(widths.carrier, carrier_width(population, 8, 16, 4));
    assert_eq!((widths.face, widths.carrier, widths.rebase), (48, 33, 93));
    let kappa = 64 - (2 * population + 2).leading_zeros() as u64;
    assert!(
        2 * widths.carrier + kappa + widths.face + 1 > 128,
        "the old refusal"
    );
    let rule = tree.face_rule();
    assert!(rule < rat(1, 32));
    // The declaration reaches 2^19 cells.
    assert!(
        Landmarks::new(LandmarkDeclaration {
            population: 1 << 19,
            ..declaration(256, 4)
        })
        .is_ok()
    );
    // A text-like passage: words drawn from a small vocabulary, separated by spaces.
    let mut draw = Draw::new(1_024);
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
        Err(ContextError::PopulationReached { .. })
    ));
}

/// **The split operands are the single division** (module header, "The lattice mixture and the
/// stop weight read split operands"; the wide cut): at widths where the single division
/// `(2^M λ̂ u + (2^M − λ̂) x v)/(2^M v)` passes `u128`, `lattice_mix` returns the nearest lattice
/// numerator of `λ̂u/v + (1 − λ̂)x` (ties up, inside `[1, 2^M − 1]`), read exactly in `ℕ`; the stop
/// weight decided before its division is the exact rounding of `2^M β/(1 + β)`; and the wide cut's
/// `2^20` cells declare at `D = 1, …, 8`, where the single division's `2M_p + κ + 3` passed 128
/// bits (133 at `D = 4`), up to `19,372,659` cells at `D = 4` (the card's kernel mixes and decides
/// the stop weight with the same split operands, `tree_mix` and `tree_stop_weight`).
#[test]
fn landmark_split_operands_are_the_single_division() {
    let mut draw = Draw::new(35);
    for (population, depth) in [
        (6_148u64, 4usize),
        (1 << 20, 1),
        (1 << 20, 4),
        (19_372_659, 4),
    ] {
        let declared = LandmarkDeclaration {
            population,
            ..declaration(256, depth)
        };
        let widths = Widths::derived(&declared);
        let full = 1u64 << widths.face;
        for _ in 0..4_000 {
            let stop = draw.next() % (full + 1);
            let v = 2 + 2 * (draw.next() % (population + 1));
            let u = 1 + 2 * (draw.next() % (v / 2));
            let below = 1 + draw.next() % (full - 1);
            let big = |x: u64| BigUint::from(x);
            let numerator = ((big(stop) * big(u)) << widths.face as usize)
                + big(full - stop) * big(below) * big(v);
            let denominator = big(v) << widths.face as usize;
            let rounded: BigUint = (numerator * 2u32 + &denominator) / (denominator * 2u32);
            let expected = u64::try_from(rounded).unwrap().clamp(1, full - 1);
            assert_eq!(lattice_mix(&widths, stop, u, v, below), expected);
        }
        for _ in 0..4_000 {
            let bits = 1 + draw.next() % widths.carrier;
            let odd = |x: u64| (x % (1u64 << bits)) | 1;
            let reach = (widths.face + widths.carrier + 2) as i64;
            let exponent = (draw.next() % (2 * reach as u64 + 1)) as i64 - reach;
            let (beta, mantissa) = Beta::carry(
                u128::from(odd(draw.next())),
                u128::from(odd(draw.next())),
                exponent,
                widths.carrier,
            );
            assert!(mantissa.is_none());
            let value = beta.value();
            let lambda = &value / (Rat::one() + &value);
            let scaled =
                lambda * Rat::from_integer(BigInt::one() << widths.face as usize) + rat(1, 2);
            let expected = u64::try_from(scaled.floor().to_integer()).unwrap();
            assert_eq!(beta.stop_weight(widths.face, widths.carrier), expected);
        }
    }
    let wide = |depth: usize| LandmarkDeclaration {
        population: 1 << 20,
        ..declaration(256, depth)
    };
    let widths = Widths::derived(&wide(4));
    assert_eq!(
        (widths.face, widths.carrier, widths.certificate),
        (54, 36, 90)
    );
    assert_eq!(
        2 * widths.face + 22 + 3,
        133,
        "the single division's operand"
    );
    assert!(widths.operand_bits(1 << 20) <= 128);
    for depth in 1..=8 {
        assert!(Landmarks::new(wide(depth)).is_ok(), "D = {depth}");
    }
    let at = |population: u64| {
        Landmarks::new(LandmarkDeclaration {
            population,
            ..declaration(256, 4)
        })
    };
    assert!(at(19_372_659).is_ok());
    assert!(at(19_372_660).is_err());
}

/// **A passage's code is its faces' product, enclosed once** (`PassageCode`, the wide cut): over
/// dyadic sides, dyadic faces and faces with odd denominators (a KT face), the product's bounds hold
/// the exact product between them, and its code length meets the exact product's enclosure within
/// `f 2^(−125) + 2^(−95)` bits; two passages joined are their faces together; bounds compare as
/// integers.
#[test]
fn landmark_passage_code_is_the_faces_product() {
    let mut draw = Draw::new(20);
    let mut code = PassageCode::new();
    let (mut left, mut right) = (PassageCode::new(), PassageCode::new());
    // The exact product, unreduced: the faces' numerators and denominators multiplied apart.
    let (mut numerators, mut denominators) = (BigUint::one(), BigUint::one());
    for index in 0..3_000u64 {
        let face = match index % 3 {
            0 => {
                let bits = 1 + draw.next() % 62;
                let side = 1 + draw.next() % ((1u64 << bits) - 1);
                code.side(side, bits);
                numerators *= side;
                denominators <<= bits as usize;
                Rat::new(BigInt::from(side), BigInt::one() << bits as usize)
            }
            1 => {
                let digits = 1 + draw.next() % 7;
                let mut numerator = BigUint::one();
                for _ in 0..digits {
                    numerator *= 1 + draw.next() % ((1u64 << 54) - 1);
                }
                let face = Rat::new(
                    BigInt::from(numerator),
                    BigInt::one() << (54 * digits) as usize,
                );
                code.face(&face).unwrap();
                numerators *= face.numer().magnitude();
                denominators *= face.denom().magnitude();
                face
            }
            _ => {
                let total = 1 + draw.next() % 5_000;
                let count = draw.next() % (total + 1);
                let face = rat(2 * count as i64 + 1, 2 * total as i64 + 256);
                code.face(&face).unwrap();
                numerators *= face.numer().magnitude();
                denominators *= face.denom().magnitude();
                face
            }
        };
        if index % 2 == 0 {
            left.face(&face).unwrap();
        } else {
            right.face(&face).unwrap();
        }
    }
    let (numerator, denominator, exponent) = code.bounds();
    let integer = |bound: &crate::compression::landmark::context::ProductBound| {
        BigUint::from(bound.mantissa) << bound.exponent as usize
    };
    // `∏ q = N/(D 2^E)`: `N` between its bounds, `D 2^E` between its bounds times `2^E`.
    assert!(integer(&numerator[0]) <= numerators && numerators <= integer(&numerator[1]));
    let scale = BigUint::one() << exponent as usize;
    assert!(integer(&denominator[0]) * &scale <= denominators);
    assert!(denominators <= integer(&denominator[1]) * &scale);
    let bits = code.bits().unwrap();
    let whole = ratio_code_length(&numerators, &denominators).unwrap();
    assert!(bits.lower <= whole.upper && whole.lower <= bits.upper);
    assert!(&bits.upper - &bits.lower <= rat_power(-90));
    left.join(&right);
    let joined = left.bits().unwrap();
    assert!(joined.lower <= whole.upper && whole.lower <= joined.upper);
    assert_eq!(left.factors(), 3_000);
    assert!(numerator[0] <= numerator[1] && denominator[0] <= denominator[1]);
}

/// `2^e` as an exact rational.
fn rat_power(exponent: i64) -> Rat {
    let shift = exponent.unsigned_abs() as usize;
    if exponent >= 0 {
        Rat::from_integer(BigInt::one() << shift)
    } else {
        Rat::new(BigInt::one(), BigInt::one() << shift)
    }
}

// -------------------------------------------------------------------------------------------
// The declared stop prior

/// **The stop prior is the dyadic ladder** (Lean `Compression/Landmark/Context/Tree.ladder_founding`): rung `j`
/// stops with `1 − 2^(−j)` and founds at `2^j − 1`; `[1]` is the `½` stop prior; a repeated last
/// rung is dropped, so one law compares equal however it is declared; rungs outside `1..=63` and
/// an empty law are refused. The ladder's top at the standing cut's scope is
/// `⌈log₂(6148 · 8)⌉ = 16`, and the declared family is the global ladder, then the per-depth pairs.
#[test]
fn landmark_stop_prior_is_the_dyadic_ladder() {
    let half = StopPrior::half();
    assert_eq!(half.rungs(), &[1]);
    assert_eq!(half.weight(0), rat(1, 2));
    assert_eq!(half.founding(7), 1);
    let law = StopPrior::per_depth(vec![1, 4, 4]).unwrap();
    assert_eq!(law.rungs(), &[1, 4]);
    assert_eq!(law, StopPrior::per_depth(vec![1, 4]).unwrap());
    assert_eq!(
        StopPrior::per_depth(vec![3, 3]).unwrap(),
        StopPrior::global(3).unwrap()
    );
    assert!(!law.is_global() && StopPrior::global(3).unwrap().is_global());
    assert_eq!((law.rung(0), law.rung(1), law.rung(9)), (1, 4, 4));
    assert_eq!(law.weight(2), rat(15, 16));
    assert_eq!((law.founding(0), law.founding(5)), (1, 15));
    assert_eq!(law.widest(), 4);
    assert_eq!(law.to_string(), "j_0 = 1, j_(≥1) = 4");
    assert_eq!(StopPrior::global(3).unwrap().to_string(), "j = 3");
    for rung in [1u32, 2, 5, 63] {
        let global = StopPrior::global(rung).unwrap();
        let w = global.weight(0);
        let beta = Rat::from_integer(BigInt::from(global.founding(0)));
        assert_eq!(&w / (Rat::one() - &w), beta, "rung {rung}");
    }
    assert!(StopPrior::global(0).is_err());
    assert!(StopPrior::global(64).is_err());
    assert!(StopPrior::per_depth(Vec::new()).is_err());

    let standing = LandmarkDeclaration {
        population: 6_148,
        ..declaration(256, 4)
    };
    assert_eq!(ladder_top(&standing), 16);
    let family = prior_family(4);
    assert_eq!(family.len(), 16);
    assert_eq!(family[0], half);
    assert!(family[..4].iter().all(StopPrior::is_global));
    assert_eq!(family[4], StopPrior::per_depth(vec![1, 2]).unwrap());
    let distinct: std::collections::BTreeSet<Vec<u32>> =
        family.iter().map(|law| law.rungs().to_vec()).collect();
    assert_eq!(distinct.len(), family.len());
}

/// **Each node is founded at its depth's ratio, each chain at its summed rung** (Lean
/// `Compression/Landmark/Context/Tree.stop_founding_step`, `Compression/Landmark/Context/Compaction.{leaf_chain_is_one_node,
/// chain_split}`): the founding chart is `β₀ = 2^(j_d) − 1` exactly with the stop weight
/// `λ̂ = 1 − 2^(−j_d)` on the lattice; one arrival stores one leaf chain at the root with `D`'s
/// chart; an arrival parting from it at depth 2 reads the upper part at the summed rung,
/// `2^(j_0 + j_1 + j_2) − 1`; one parting from that internal chain at depth 0 reads
/// `β_u = (2^(S_up) − 1) 2^(S_low) β/(β (2^(S_low) − 1) + 2^S − 1)` and leaves the lower part at
/// `β_ℓ = β (2^(S_low) − 1)/(2^S − 1)`, exactly; and a rung past the carrier `W` is refused (its
/// founding ratio would not be carried exactly).
#[test]
fn landmark_stop_prior_founds_each_node_at_its_ratio() {
    let prior = StopPrior::per_depth(vec![2, 3, 5]).unwrap();
    let declared = LandmarkDeclaration {
        prior: prior.clone(),
        ..declaration(2, 3)
    };
    let mut tree = Landmarks::new(declared.clone()).unwrap();
    let face = tree.face_bits();
    for depth in 0..=3 {
        let words = tree.arena().founding(depth).unwrap();
        let j = prior.rung(depth);
        assert_eq!(
            (words.numerator, words.denominator, words.exponent),
            ((1u64 << j) - 1, 1, 0)
        );
        assert_eq!(words.stop, (1u64 << face) - (1u64 << (face - u64::from(j))));
    }
    assert!(tree.arena().founding(4).is_none());
    let ladder = |rung: u32| Rat::from_integer((BigInt::one() << rung as usize) - 1);
    let (b, c) = (Letter::Boundary, Letter::Cell(0));
    let first = [b, b, b];
    tree.receive(&first, 1).unwrap();
    let path = &tree.opened(&first, 1).unwrap()[0];
    assert_eq!((path.founded, &path.bottoms[..]), (1, &[3][..]));
    assert_eq!(path.betas[0], ladder(prior.rung(3)));
    // Parting at depth 2 from the leaf chain: the upper part at the summed rung 2 + 3 + 5.
    let second = [b, b, c];
    let path = &tree.opened(&second, 1).unwrap()[0];
    assert_eq!((path.founded, &path.bottoms[..]), (1, &[2][..]));
    assert_eq!(path.betas[0], ladder(10));
    tree.receive(&second, 1).unwrap();
    let beta = tree.opened(&second, 1).unwrap()[0].betas[0].clone();
    // Parting at depth 0 from the internal chain 0..2: S_up = 2, S_low = 3 + 5.
    let third = [c, b, b];
    let path = &tree.opened(&third, 1).unwrap()[0];
    assert_eq!((path.founded, &path.bottoms[..]), (1, &[0][..]));
    let (up, low, whole) = (ladder(2), ladder(8), ladder(10));
    let upper = &up * rat(256, 1) * &beta / (&beta * &low + &whole);
    assert_eq!(path.betas[0], upper);
    tree.receive(&third, 1).unwrap();
    let path = &tree.opened(&second, 1).unwrap()[0];
    assert_eq!(&path.bottoms[..], &[0, 2, 3]);
    assert_eq!(path.betas[1], &beta * &low / &whole);
    let wide = LandmarkDeclaration {
        prior: StopPrior::global(13).unwrap(),
        ..declaration(4, 2)
    };
    assert!(Landmarks::with_carrier(wide.clone(), 12).is_err());
    assert!(Landmarks::with_carrier(wide, 13).is_ok());
}

/// **Campaign 2's constant-slot controls are the per-depth prior `(1, r + 1)`** (the declared stop prior; Lean
/// `Compression/Landmark/Context/Tree.stop_mixture_over_trees`): in the bundle branch over `r` slots of one letter, a
/// cell node's split passes through a chain of `r` constant nodes at `½` (each routes the same
/// counts), so every cell depth past the root stops with `1 − 2^(−(r+1))`, the root with `½`, and
/// the bottom chain reads its leaf's face. On the ideal oracles with `β` exact, every opened digit's
/// bundle-branch face equals the cell tree's face under that law, in ℚ, at every step.
#[test]
fn landmark_constant_slots_are_the_per_depth_prior() {
    let alphabet = 4;
    let stream: Vec<usize> = (0..80u64)
        .map(|t| ((t * t + 3 * t + t / 5) % 4) as usize)
        .collect();
    let letters: Vec<Letter> = stream
        .iter()
        .map(|&cell| Letter::Bundle(Bundle { cell, features: 0 }))
        .collect();
    for (slots, depth) in [(1usize, 2usize), (2, 2), (1, 3)] {
        let control = LandmarkDeclaration {
            population: 80,
            family: LetterFamily::constant_control(slots),
            ..declaration(alphabet, depth)
        };
        let law = LandmarkDeclaration {
            population: 80,
            prior: StopPrior::per_depth(vec![1, slots as u32 + 1]).unwrap(),
            ..declaration(alphabet, depth)
        };
        let mut joined = IdealLandmarks::new(control, None).unwrap();
        let mut tree = IdealLandmarks::new(law, None).unwrap();
        for (position, &cell) in stream.iter().enumerate() {
            let bundled = letter_address(&letters, position, depth);
            let here = address(&stream, position, depth);
            for class in 0..alphabet {
                let bundle: Vec<_> = joined
                    .opened(&bundled, class)
                    .unwrap()
                    .into_iter()
                    .filter(|path| path.branch == 1)
                    .collect();
                let cells = tree.opened(&here, class).unwrap();
                assert_eq!(bundle.len(), cells.len());
                for (b, c) in bundle.iter().zip(&cells) {
                    assert_eq!(b.dyadic, c.dyadic);
                    assert_eq!(
                        b.faces[0], c.faces[0],
                        "r = {slots}, D = {depth}, cell {position}, class {class}"
                    );
                }
            }
            joined.receive(&bundled, cell).unwrap();
            tree.receive(&here, cell).unwrap();
        }
    }
}

// -------------------------------------------------------------------------------------------
// Weighing is local

/// An external digit-0 face on the tree's lattice `2^(−M)`: a declared odd numerator pattern,
/// never a tuned value, inside the open unit interval.
fn external_split(face_bits: u64, t: usize, h: usize) -> u64 {
    let eighths = 1 + ((t * 5 + h * 3) % 7) as u64;
    eighths << (face_bits - 3)
}

/// **A join tree's prior sums to one** (Lean `Compression/Landmark/Context/LocalWeighing.static_mixture`): the balanced
/// tree over `2^m` faces is uniform, over five faces its weights are `2^(−depth)`; the incumbent's
/// tree gives face 0 the prior `1 − 2^(−j)` and shares `2^(−j)` among the rest.
#[test]
fn landmark_join_tree_prior_sums_to_one() {
    let uniform = JoinTree::balanced(4).unwrap().prior();
    assert_eq!(uniform, vec![rat(1, 4); 4]);
    let five = JoinTree::balanced(5).unwrap().prior();
    assert_eq!(
        five,
        vec![rat(1, 4), rat(1, 4), rat(1, 4), rat(1, 8), rat(1, 8)]
    );
    let incumbent = JoinTree::incumbent(3, 3).unwrap().prior();
    assert_eq!(incumbent, vec![rat(7, 8), rat(1, 16), rat(1, 16)]);
    for tree in [
        JoinTree::balanced(1).unwrap(),
        JoinTree::balanced(7).unwrap(),
        JoinTree::incumbent(2, 1).unwrap(),
        JoinTree::incumbent(6, 4).unwrap(),
    ] {
        let sum: Rat = tree.prior().into_iter().sum();
        assert_eq!(sum, Rat::one());
        assert_eq!(tree.joins() + 1, tree.faces());
    }
    assert!(JoinTree::balanced(0).is_err());
    assert!(JoinTree::incumbent(1, 1).is_err());
    assert!(JoinTree::incumbent(3, 0).is_err());
}

/// **The joins are the Bayesian mixture of their faces, digit by digit** (Lean
/// `Compression/Landmark/Context/LocalWeighing.{static_mixture, forward_executed}`): three declared lattice faces in two
/// dyadic cells, joined by the incumbent's tree; each digit's mixed face lies within its
/// certificate of the exact posterior mixture `Σ_k π_k A_k q_k/Σ_k π_k A_k` (each dyadic cell its
/// own evidence `A_k`), and the mixed faces' product within the certificates' sum of the
/// telescoped `Σ_k π_k Π q_k`.
#[test]
fn landmark_joins_are_the_bayes_mixture_per_dyadic_cell() {
    let declared = declaration(4, 1);
    let widths = Landmarks::new(declared).unwrap().widths();
    let tree = JoinTree::incumbent(3, 2).unwrap();
    let prior = tree.prior();
    let mut joins = FaceJoins::new(tree, widths).unwrap();
    let bits = widths.face;
    let scale = Rat::from_integer(BigInt::one() << bits as usize);
    let full = 1u64 << bits;
    let mut evidence = [vec![Rat::one(); 3], vec![Rat::one(); 3]];
    let (mut executed, mut residual) = ([Rat::one(), Rat::one()], [Rat::zero(), Rat::zero()]);
    for t in 0..40usize {
        let cell = t % 2;
        let dyadic = 2 + cell;
        let symbol = (t * t / 3) % 2;
        let faces: Vec<u64> = (0..3).map(|k| external_split(bits, t + k * 4, k)).collect();
        let sides: Vec<Rat> = faces
            .iter()
            .map(|&x| {
                let side = if symbol == 0 { x } else { full - x };
                Rat::from_integer(BigInt::from(side)) / &scale
            })
            .collect();
        let weights: Vec<Rat> = (0..3).map(|k| &prior[k] * &evidence[cell][k]).collect();
        let total: Rat = weights.iter().cloned().sum();
        let ideal: Rat = (0..3).map(|k| &weights[k] * &sides[k]).sum::<Rat>() / &total;
        let receipt = joins
            .receive(dyadic, &faces, symbol, &[0; 3], &[0; 3])
            .unwrap();
        let side = if symbol == 0 {
            receipt.split
        } else {
            full - receipt.split
        };
        let mixed = Rat::from_integer(BigInt::from(side)) / &scale;
        let bound = Rat::new(
            BigInt::from(receipt.certificate) * 3,
            BigInt::from(2u32) << widths.certificate as usize,
        );
        assert!(within(&mixed, &ideal, &bound), "digit {t}");
        executed[cell] *= mixed;
        residual[cell] += bound;
        for k in 0..3 {
            evidence[cell][k] *= &sides[k];
        }
    }
    for cell in 0..2 {
        let telescoped: Rat = (0..3).map(|k| &prior[k] * &evidence[cell][k]).sum();
        assert!(within(&executed[cell], &telescoped, &residual[cell]));
    }
    assert!(joins.receive(1, &[1, 2], 0, &[0; 2], &[0; 2]).is_err());
    assert!(
        joins
            .receive(1, &[1, 2, full], 0, &[0; 3], &[0; 3])
            .is_err()
    );
}

/// **The stop-weight mixture per digit tree** (Lean `Compression/Landmark/Context/LocalWeighing.stop_mixture_per_tree`):
/// one law alone is its tree exactly; a law joined with itself is its tree exactly (a join of two
/// equal faces is that face); and two laws' mixture multiplies, in each dyadic cell, to within its
/// certificates of `Σ_k π_k Π q̂_k` over the trees' own executed faces there.
#[test]
fn landmark_stop_mixture_is_the_bayes_mixture_per_digit_tree() {
    let alphabet = 5;
    let stream: Vec<usize> = (0..48u64).map(|t| ((t * t + t / 3) % 5) as usize).collect();
    let declared = declaration(alphabet, 2);
    let half = StopPrior::half();
    let other = StopPrior::per_depth(vec![1, 3]).unwrap();
    let mut alone = StopMixture::new(
        declared.clone(),
        vec![half.clone()],
        JoinTree::balanced(1).unwrap(),
    )
    .unwrap();
    let mut twice = StopMixture::new(
        declared.clone(),
        vec![half.clone(), half.clone()],
        JoinTree::incumbent(2, 3).unwrap(),
    )
    .unwrap();
    let tree = JoinTree::incumbent(2, 2).unwrap();
    let prior = tree.prior();
    let mut mixture =
        StopMixture::new(declared.clone(), vec![half.clone(), other.clone()], tree).unwrap();
    assert_eq!(mixture.priors(), vec![half.clone(), other.clone()]);
    let mut trees = [
        Landmarks::new(declared.clone()).unwrap(),
        Landmarks::new(LandmarkDeclaration {
            prior: other,
            ..declared.clone()
        })
        .unwrap(),
    ];
    let bits = trees[0].face_bits();
    let scale = Rat::from_integer(BigInt::one() << bits as usize);
    let cells = 1usize << trees[0].digits();
    let mut evidence = vec![[Rat::one(), Rat::one()]; cells];
    let (mut executed, mut residual) = (Rat::one(), Rat::zero());
    for (position, &cell) in stream.iter().enumerate() {
        let here = address(&stream, position, 2);
        let single = trees[0].score(&here, cell).unwrap();
        assert_eq!(
            alone.receive(&here, cell).unwrap().executed,
            single.executed
        );
        assert_eq!(
            twice.receive(&here, cell).unwrap().executed,
            single.executed
        );
        let reading = mixture.receive(&here, cell).unwrap();
        executed *= &reading.executed;
        residual += &reading.residual;
        let digits: Vec<DigitsReading> = trees
            .iter_mut()
            .map(|tree| tree.receive_digits(&here, cell).unwrap())
            .collect();
        for i in 0..digits[0].digits.len() {
            let h = digits[0].digits[i].dyadic;
            for (k, reading) in digits.iter().enumerate() {
                let digit = reading.digits[i];
                let side = if digit.symbol == 0 {
                    digit.split
                } else {
                    (1u64 << bits) - digit.split
                };
                evidence[h][k] *= Rat::from_integer(BigInt::from(side)) / &scale;
            }
        }
    }
    // Each dyadic cell is its own digit tree: the passage telescopes to Π_h Σ_k π_k A_(h,k).
    let telescoped: Rat = evidence
        .iter()
        .map(|pair| &prior[0] * &pair[0] + &prior[1] * &pair[1])
        .product();
    assert!(within(&executed, &telescoped, &residual));
    assert!(residual > Rat::zero());
}

// -------------------------------------------------------------------------------------------
// The tree is stored at the faces where paths part

/// The arrivals each tree `t = branch · 2^B + h` routes over a stream of classes: every opened
/// digit's dyadic cell, in each branch.
fn arrivals(declared: &LandmarkDeclaration, stream: &[usize]) -> Vec<usize> {
    let cells = 1usize << odometer_digits(declared.alphabet);
    let branches = declared.branch_depths().len();
    let mut routed = vec![0usize; branches * cells];
    for &class in stream {
        for (h, _) in declared.emitted(class) {
            for branch in 0..branches {
                routed[branch * cells + h] += 1;
            }
        }
    }
    routed
}

/// **Each tree stores at most `2n − 1` nodes** (Lean `Compression/Landmark/Context/Compaction.compacted_node_bound`)
/// over `n` arrivals, and none without one.
fn within_node_bound(tree: &Landmarks, routed: &[usize]) -> bool {
    let sizes = tree.tree_sizes();
    sizes.iter().sum::<usize>() == tree.nodes()
        && sizes
            .iter()
            .zip(routed)
            .all(|(&size, &n)| size <= (2 * n).saturating_sub(1))
}

/// **The oracle is the full tree's, exactly in ℚ** (Lean `Compression/Landmark/Context/Compaction.{chain_ratio,
/// chain_ratio_dyadic, leaf_chain_is_one_node, chain_split, compacted_is_the_full_tree}`): over streams
/// of two and five classes, at depths from 1 to past the stream's recurrence (at the deepest every
/// context is new, so each leaf's label runs to the boundary letters), under the `½` stop prior, two
/// global rungs and two per-depth priors, with forced depths 0 and 1, every class's face before
/// each deposit and every prequential face of the oracle stored where paths part equal the
/// full tree of one node a depth (`landmark_full`); it stores no more nodes.
#[test]
fn landmark_compacted_oracle_is_the_full_tree() {
    let binary: Vec<usize> = (0..40u64)
        .map(|t| usize::from((t * t + 3 * t) % 7 < 3))
        .collect();
    let five: Vec<usize> = (0..30u64).map(|t| ((t * 7 + t / 3) % 5) as usize).collect();
    for (stream, alphabet, depths) in [
        (&binary, 2, [1, 3, 6, 12, 41]),
        (&five, 5, [1, 2, 4, 9, 31]),
    ] {
        for prior in priors() {
            for depth in depths {
                for forced in [0, 1] {
                    let declared = LandmarkDeclaration {
                        forced,
                        prior: prior.clone(),
                        ..declaration(alphabet, depth)
                    };
                    let mut full = FullTree::new(declared.clone());
                    let mut compact = IdealLandmarks::new(declared, None).unwrap();
                    for (position, &cell) in stream.iter().enumerate() {
                        let here = address(stream, position, depth);
                        for class in 0..alphabet {
                            assert_eq!(
                                compact.probability(&here, class).unwrap(),
                                full.probability(&here, class),
                                "{prior}, D = {depth}, forced {forced}, cell {position}, class {class}"
                            );
                        }
                        assert_eq!(
                            compact.receive(&here, cell).unwrap(),
                            full.receive(&here, cell),
                            "{prior}, D = {depth}, forced {forced}, cell {position}"
                        );
                    }
                    assert!(compact.nodes() <= full.nodes());
                }
            }
        }
    }
}

/// **The executed tree stored where paths part holds its carried certificate**: at
/// depths from 1 to past the stream's recurrence, under three priors, forced depths 0 and 1, at the
/// rule's carrier and at a narrow one (so the founding ratios `2^S − 1` of long chains and the
/// splits' ratios rebase), every all-class face sums to 1 and meets each one-class read, every
/// cell's executed face lies within its certificate of the ideal face (the full tree of one
/// node a depth, exact, `landmark_full`), the certificate within the rule, and each tree stores at
/// most `2n − 1` nodes, no more than the full tree's.
#[test]
fn landmark_compacted_tree_is_within_its_certificate() {
    let alphabet = 5;
    let stream: Vec<usize> = (0..60u64)
        .map(|t| ((t * 7 + t / 3 + t * t / 11) % 5) as usize)
        .collect();
    let laws = [
        StopPrior::half(),
        StopPrior::global(3).unwrap(),
        StopPrior::per_depth(vec![1, 4]).unwrap(),
    ];
    for depth in [1, 3, 8, 61] {
        for prior in &laws {
            for (forced, carrier) in [(0, None), (1, None), (0, Some(6))] {
                let declared = LandmarkDeclaration {
                    forced,
                    prior: prior.clone(),
                    ..declaration(alphabet, depth)
                };
                let declare = || match carrier {
                    Some(width) => Landmarks::with_carrier(declared.clone(), width).unwrap(),
                    None => Landmarks::new(declared.clone()).unwrap(),
                };
                let mut tree = declare();
                let mut oracle = FullTree::new(declared.clone());
                for (position, &cell) in stream.iter().enumerate() {
                    let here = address(&stream, position, depth);
                    let face = tree.face(&here, 16).unwrap();
                    let sum: Rat = face.probabilities.iter().cloned().sum();
                    assert_eq!(sum, Rat::one());
                    for class in 0..alphabet {
                        assert_eq!(
                            face.probabilities[class],
                            tree.probability(&here, class).unwrap()
                        );
                    }
                    let reading = tree.receive(&here, cell).unwrap();
                    let ideal = oracle.receive(&here, cell);
                    assert!(
                        within(&reading.executed, &ideal, &reading.residual),
                        "{prior}, D = {depth}, forced {forced}, cell {position}"
                    );
                    assert!(reading.residual <= tree.face_rule());
                }
                assert!(within_node_bound(&tree, &arrivals(&declared, &stream)));
                assert!(tree.nodes() <= oracle.nodes());
                if carrier.is_some() && depth > 3 {
                    assert!(tree.chart().rebases > 0, "the narrow carrier rebased");
                }
            }
        }
    }
}

/// **The enlarged tree stored where paths part** (on both branches): with a declared
/// family each dyadic cell joins the cell tree and the bundle tree, each stored where its paths
/// part; the oracle's faces are the full tree's exactly, the executed faces sum to 1 and hold
/// their certificates, and a window's faces in cell order are the deposited clone's.
#[test]
fn landmark_enlarged_tree_where_paths_part_is_the_full_tree() {
    let alphabet = 5;
    let stream: Vec<usize> = (0..48u64)
        .map(|t| ((t * 7 + t / 3 + t * t / 11) % 5) as usize)
        .collect();
    for (depth, prior) in [
        (2, StopPrior::half()),
        (5, StopPrior::per_depth(vec![1, 3]).unwrap()),
        (17, StopPrior::global(2).unwrap()),
    ] {
        let declared = LandmarkDeclaration {
            prior,
            ..bundle_declaration(alphabet, depth)
        };
        let letters = bundles(&stream, &declared.family);
        let mut tree = Landmarks::new(declared.clone()).unwrap();
        let mut full = FullTree::new(declared.clone());
        let mut compact = IdealLandmarks::new(declared.clone(), None).unwrap();
        for (position, &cell) in stream.iter().enumerate() {
            let here = letter_address(&letters, position, depth);
            let face = tree.face(&here, 16).unwrap();
            let sum: Rat = face.probabilities.iter().cloned().sum();
            assert_eq!(sum, Rat::one());
            let ideal = full.receive(&here, cell);
            assert_eq!(compact.receive(&here, cell).unwrap(), ideal, "D = {depth}");
            let reading = tree.receive(&here, cell).unwrap();
            assert!(within(&reading.executed, &ideal, &reading.residual));
            assert!(reading.residual <= tree.face_rule());
        }
        assert!(within_node_bound(&tree, &arrivals(&declared, &stream)));
        let here = letter_address(&letters, stream.len(), depth);
        let paths = tree.opened(&here, 3).unwrap();
        assert!(paths.iter().any(|path| path.branch == 1));
    }
    let declared = LandmarkDeclaration {
        population: 48,
        ..bundle_declaration(alphabet, 4)
    };
    let letters = bundles(&stream, &declared.family);
    let mut tree = Landmarks::with_carrier(declared, 6).unwrap();
    for start in (0..stream.len()).step_by(3) {
        let window = start..(start + 3).min(stream.len());
        let addresses: Vec<Vec<Letter>> = window
            .clone()
            .map(|position| letter_address(&letters, position, 4))
            .collect();
        let known = &stream[window];
        let before = tree.clone();
        let faces = window_faces(&tree, &addresses, known, 16).unwrap();
        assert_eq!(tree, before);
        let mut deposited = tree.clone();
        for (j, (here, &cell)) in addresses.iter().zip(known).enumerate() {
            assert_eq!(faces[j], deposited.face(here, 16).unwrap(), "phase {j}");
            deposited.deposit(here, cell).unwrap();
        }
        tree = deposited;
    }
}

/// **A window's faces in cell order past the stream's recurrence** (`Landmarks::window`): the
/// overlay founds, splits and relinks as the deposit does, so phase `j` reads exactly the face of a
/// clone into which the earlier phases' targets were deposited.
#[test]
fn landmark_deep_window_faces_read_each_phase_after_the_earlier_deposits() {
    let stream: Vec<usize> = (0..90u64)
        .map(|t| ((t * 7 + t / 3 + t * t / 11) % 5) as usize)
        .collect();
    for (prior, depth) in [
        (StopPrior::half(), 2),
        (StopPrior::half(), 9),
        (StopPrior::per_depth(vec![2, 5]).unwrap(), 5),
    ] {
        window_in_cell_order(&stream, prior, depth, Capacity::Unbounded);
    }
}

/// **The parts stored where paths part**: score then deposit is receive and a clone compares equal
/// past the stream's recurrence; one arrival at `D = 3` over two classes stores one leaf at the root
/// (its masses `3/2` and `1/2`, its bottom depth and its label's three boundary letters in the pool)
/// where the full tree founds four nodes.
#[test]
fn landmark_stored_parts_where_paths_part() {
    let stream: Vec<usize> = (0..50u64)
        .map(|t| ((t * 11 + t / 7) % 6) as usize)
        .collect();
    let mut once = Landmarks::new(declaration(6, 7)).unwrap();
    let mut twice = once.clone();
    for (position, &cell) in stream.iter().enumerate() {
        let here = address(&stream, position, 7);
        let reading = once.receive(&here, cell).unwrap();
        assert_eq!(twice.score(&here, cell).unwrap(), reading);
        twice.deposit(&here, cell).unwrap();
        assert_eq!(once, twice);
    }
    assert!(once.held() > 0);

    let mut tree = Landmarks::new(declaration(2, 3)).unwrap();
    let mut full = FullTree::new(declaration(2, 3));
    let boundary = [Letter::Boundary; 3];
    tree.receive(&boundary, 0).unwrap();
    full.receive(&boundary, 0);
    assert_eq!((tree.nodes(), full.nodes()), (1, 4));
    assert_eq!(tree.held(), 3);
    // masses 2C = 3 and 1: (2 + 2) + (1 + 2); the bottom depth 3 and the label end 3: 2 + 1 each;
    // three letters 0: 2 each; the root's presence: 1.
    assert_eq!(tree.bits(), (2 + 2) + (1 + 2) + 3 + 3 + 3 * 2 + 1);
}

/// **The split's ratios are their exact forms carried once** (`Beta::split`; Lean
/// `Compression/Landmark/Context/Compaction.chain_split`): over carried ratios `β` whose exponents run to `±3000`
/// and rungs to 40 on each side, the upper part lies at `β_u = (2^(S_up) − 1) 2^(S_low) β/(β (2^(S_low)
/// − 1) + 2^S − 1)` and the lower at `β_ℓ = β (2^(S_low) − 1)/(2^S − 1)`, each exactly when its odd
/// parts fit `W` bits and otherwise its `W`-bit floor, below the exact ratio by a relative
/// `[0, 1/m')` with `m'` the kept mantissa in `[2^(W−1), 2^W)`.
#[test]
fn landmark_split_ratios_are_the_exact_forms() {
    let mut draw = Draw::new(37);
    let ladder = |rung: u64| Rat::from_integer((BigInt::one() << rung as usize) - 1);
    let (mut exact, mut rebased) = (0, 0);
    for width in [6u64, 28, 42] {
        for trial in 0..300 {
            let wide = |draw: &mut Draw| u128::from(draw.next() >> (64 - width)) | 1;
            let exponent = match trial % 3 {
                0 => (draw.next() % 21) as i64 - 10,
                1 => (draw.next() % 6001) as i64 - 3000,
                _ => (draw.next() % 401) as i64 - 200,
            };
            let (beta, _) = Beta::carry(wide(&mut draw), wide(&mut draw), exponent, width);
            let (upper, lower) = (1 + draw.next() % 40, 1 + draw.next() % 40);
            let value = beta.value();
            let targets = [
                ladder(upper) * rat_power(lower as i64) * &value
                    / (&value * ladder(lower) + ladder(upper + lower)),
                &value * ladder(lower) / ladder(upper + lower),
            ];
            for ((carried, mantissa), target) in
                beta.split(upper, lower, width).iter().zip(&targets)
            {
                let (n, d, _) = carried.parts();
                assert!(n % 2 == 1 && d % 2 == 1 && n < 1 << width && d < 1 << width);
                match mantissa {
                    None => {
                        assert_eq!(&carried.value(), target);
                        exact += 1;
                    }
                    Some(m) => {
                        assert!(*m >= 1 << (width - 1) && *m < 1 << width);
                        let relative = (target - carried.value()) / target;
                        assert!(relative >= Rat::zero());
                        assert!(relative < Rat::new(BigInt::one(), BigInt::from(*m)));
                        rebased += 1;
                    }
                }
            }
        }
    }
    assert!(exact > 0 && rebased > 0);
}

// -------------------------------------------------------------------------------------------
// A landmark's storage has a capacity

/// The capacities the capped laws are checked at: `L = 2, 4, 8, 32`.
fn ceilings() -> Vec<Capacity> {
    [1, 2, 3, 5].into_iter().map(Capacity::Ceiling).collect()
}

/// A binary stream of period five with one flipped cell: after the flip, each address holds it at
/// one more depth, so it parts from the periodic contexts' chains, which have carried by then.
fn flipped(length: u64) -> Vec<usize> {
    (0..length)
        .map(|t| usize::from([0, 1, 1, 0, 1][(t % 5) as usize] == 1) ^ usize::from(t == 60))
        .collect()
}

/// **The register's carry** (`Capacity::carry`, Lean `Compression/Landmark/Context/Capacity.capCarry`): at the
/// ceiling each half-unit mass `2n + 1` becomes `2⌈n/2⌉ + 1`, and below it nothing moves; the
/// unbounded register and a ceiling past every `u32` total never carry.
#[test]
fn landmark_capacity_carries_its_register() {
    for exponent in 0..8u32 {
        let top = 1u32 << exponent;
        for zero in 0..=top + 1 {
            for one in 0..=top + 1 {
                let mut halves = [2 * zero + 1, 2 * one + 1];
                let carried = Capacity::Ceiling(exponent).carry(&mut halves);
                assert_eq!(carried, zero + one >= top);
                let expected = if carried {
                    [2 * zero.div_ceil(2) + 1, 2 * one.div_ceil(2) + 1]
                } else {
                    [2 * zero + 1, 2 * one + 1]
                };
                assert_eq!(halves, expected);
                // A reached symbol keeps a count.
                assert!(zero == 0 || halves[0] >= 3);
                let mut unbounded = [2 * zero + 1, 2 * one + 1];
                assert!(!Capacity::Unbounded.carry(&mut unbounded));
            }
        }
    }
    let mut widest = [u32::MAX, u32::MAX];
    assert!(!Capacity::Ceiling(32).carry(&mut widest));
    assert_eq!(Capacity::default(), Capacity::Unbounded);
    assert_eq!(
        format!("{} {}", Capacity::Unbounded, Capacity::Ceiling(7)),
        "c = ∞ c = 7"
    );
}

/// **`c = ∞` and every ceiling no node reaches are the uncapped tree exactly** (Lean
/// `Compression/Landmark/Context/Capacity.{cap_unbounded_is_kt, cap_below_ceiling_is_kt}`): over a stream of 60
/// cells, the unbounded tree, the tree at `c = 6` (`L = 64` passes every node's arrivals) and at
/// `c = 40` read the same executed faces and certificates, store the same arena, and their oracles
/// the same ideal faces, equal to the full tree of one node a depth.
#[test]
fn landmark_unbounded_capacity_is_the_uncapped_tree() {
    let alphabet = 5;
    let stream: Vec<usize> = (0..60u64)
        .map(|t| ((t * 7 + t / 3 + t * t / 11) % 5) as usize)
        .collect();
    for depth in [1, 4, 31] {
        for prior in [StopPrior::half(), StopPrior::per_depth(vec![1, 4]).unwrap()] {
            let declared = |capacity| LandmarkDeclaration {
                prior: prior.clone(),
                capacity,
                ..declaration(alphabet, depth)
            };
            let capacities = [
                Capacity::Unbounded,
                Capacity::Ceiling(6),
                Capacity::Ceiling(40),
            ];
            let mut trees: Vec<Landmarks> = capacities
                .iter()
                .map(|&capacity| Landmarks::new(declared(capacity)).unwrap())
                .collect();
            let mut oracles: Vec<IdealLandmarks> = capacities
                .iter()
                .map(|&capacity| IdealLandmarks::new(declared(capacity), None).unwrap())
                .collect();
            let mut full = FullTree::new(declared(Capacity::Unbounded));
            for (position, &cell) in stream.iter().enumerate() {
                let here = address(&stream, position, depth);
                let readings: Vec<_> = trees
                    .iter_mut()
                    .map(|tree| tree.receive(&here, cell).unwrap())
                    .collect();
                let ideal: Vec<Rat> = oracles
                    .iter_mut()
                    .map(|oracle| oracle.receive(&here, cell).unwrap())
                    .collect();
                let reference = full.receive(&here, cell);
                for (reading, face) in readings.iter().zip(&ideal) {
                    assert_eq!(
                        reading, &readings[0],
                        "{prior}, D = {depth}, cell {position}"
                    );
                    assert_eq!(face, &reference, "{prior}, D = {depth}, cell {position}");
                }
            }
            let arena = trees[0].arena();
            for tree in &trees[1..] {
                let other = tree.arena();
                assert_eq!(other.halves(), arena.halves());
                assert_eq!(other.words(), arena.words());
                assert_eq!(other.labels(), arena.labels());
                assert_eq!(other.charts(), arena.charts());
                assert_eq!(tree.nodes(), trees[0].nodes());
            }
            assert_eq!(full.carries(), 0);
        }
    }
}

/// **The capped oracle is the naive tree of one register a depth, exactly in ℚ** (Lean
/// `Compression/Landmark/Context/Compaction.compacted_node_law`, `Compression/Landmark/Context/Capacity.capped_tree_laws`): at
/// `L = 2, 4, 8, 32`, over the flipped binary stream and a five-class stream, at depths from 1 to
/// past the stream's recurrence, under three priors and forced depths 0 and 1, every class's ideal
/// face before each deposit equals the naive tree's (`landmark_full`, each depth its own register
/// carrying on its own), the faces sum to 1, and along every opened path each stored level's
/// register (its KT face of the digit) is the naive tree's at the level's bottom depth. The registers
/// carry, and chains whose registers have carried are split: a stored chain is one register, and its
/// split's upper part takes it.
#[test]
fn landmark_capped_oracle_is_the_naive_tree() {
    let binary = flipped(110);
    let five: Vec<usize> = (0..40u64).map(|t| ((t * 7 + t / 3) % 5) as usize).collect();
    let mut split_after_carries = 0;
    for (stream, alphabet, depths) in [(&binary, 2, [1, 3, 12, 111]), (&five, 5, [1, 2, 5, 41])] {
        for capacity in ceilings() {
            let mut carries = 0;
            for prior in [
                StopPrior::half(),
                StopPrior::global(3).unwrap(),
                StopPrior::per_depth(vec![1, 3]).unwrap(),
            ] {
                for depth in depths {
                    for forced in [0, 1] {
                        let declared = LandmarkDeclaration {
                            forced,
                            prior: prior.clone(),
                            capacity,
                            ..declaration(alphabet, depth)
                        };
                        let mut full = FullTree::new(declared.clone());
                        let mut compact = IdealLandmarks::new(declared, None).unwrap();
                        for (position, &cell) in stream.iter().enumerate() {
                            let here = address(stream, position, depth);
                            let label = format!(
                                "{capacity}, {prior}, D = {depth}, forced {forced}, cell {position}"
                            );
                            let mut sum = Rat::zero();
                            for class in 0..alphabet {
                                let face = compact.probability(&here, class).unwrap();
                                assert_eq!(face, full.probability(&here, class), "{label}");
                                sum += face;
                                let registers = full.registers(&here, class);
                                let paths = compact.opened(&here, class).unwrap();
                                for (path, path_registers) in
                                    paths.iter().zip(registers.iter().flatten())
                                {
                                    // A forced level's register is never read (`λ = 0`).
                                    for (level, &bottom) in path
                                        .bottoms
                                        .iter()
                                        .enumerate()
                                        .filter(|&(_, &bottom)| bottom >= forced)
                                    {
                                        assert_eq!(
                                            path.masses[level], path_registers[bottom].0,
                                            "{label}, class {class}, level {level}"
                                        );
                                    }
                                }
                            }
                            assert_eq!(sum, Rat::one(), "{label}");
                            let before = compact.nodes();
                            let opened = compact.opened(&here, cell).unwrap();
                            let registers = full.registers(&here, cell);
                            assert_eq!(
                                compact.receive(&here, cell).unwrap(),
                                full.receive(&here, cell),
                                "{label}"
                            );
                            // One digit tree over two classes: two nodes founded is a split and
                            // its arrival's leaf; the upper part's register is the chain's, which
                            // the naive tree carried at the parting depth.
                            if alphabet == 2 && compact.nodes() == before + 2 {
                                let path = &opened[0];
                                let parting = *path.bottoms.last().expect("a parting level");
                                if registers[0][0][parting].2 > 0 {
                                    split_after_carries += 1;
                                }
                            }
                        }
                        assert!(compact.nodes() <= full.nodes());
                        carries += full.carries();
                    }
                }
            }
            assert!(carries > 0, "{capacity}: the registers carried");
        }
    }
    assert!(
        split_after_carries > 0,
        "chains split after their registers carried"
    );
}

/// **The capped executed tree holds its carried certificate** (the register's capacity: the counts stay exact
/// integers, every total at most its arrivals, so KT's floor and the widths' rule are unchanged): at
/// `L = 2` and `L = 16`, depths from 1 to past the stream's recurrence, two priors, forced depths 0
/// and 1 and a narrow carrier, every all-class face sums to 1 and meets each one-class read, every
/// cell's executed face lies within its certificate of the naive capped tree's ideal face, the
/// certificate within the rule, and each tree stores at most `2n − 1` nodes; its windows in cell
/// order read the deposited clone's faces.
#[test]
fn landmark_capped_tree_is_within_its_certificate() {
    let alphabet = 5;
    let stream: Vec<usize> = (0..60u64)
        .map(|t| ((t * 7 + t / 3 + t * t / 11) % 5) as usize)
        .collect();
    for capacity in [Capacity::Ceiling(1), Capacity::Ceiling(4)] {
        let mut carries = 0;
        for depth in [1, 3, 8, 61] {
            for prior in [StopPrior::half(), StopPrior::per_depth(vec![1, 4]).unwrap()] {
                for (forced, carrier) in [(0, None), (1, None), (0, Some(6))] {
                    let declared = LandmarkDeclaration {
                        forced,
                        prior: prior.clone(),
                        capacity,
                        ..declaration(alphabet, depth)
                    };
                    let mut tree = match carrier {
                        Some(width) => Landmarks::with_carrier(declared.clone(), width).unwrap(),
                        None => Landmarks::new(declared.clone()).unwrap(),
                    };
                    let mut oracle = FullTree::new(declared.clone());
                    for (position, &cell) in stream.iter().enumerate() {
                        let here = address(&stream, position, depth);
                        let face = tree.face(&here, 16).unwrap();
                        let sum: Rat = face.probabilities.iter().cloned().sum();
                        assert_eq!(sum, Rat::one());
                        for class in 0..alphabet {
                            assert_eq!(
                                face.probabilities[class],
                                tree.probability(&here, class).unwrap()
                            );
                        }
                        let reading = tree.receive(&here, cell).unwrap();
                        let ideal = oracle.receive(&here, cell);
                        assert!(
                            within(&reading.executed, &ideal, &reading.residual),
                            "{capacity}, {prior}, D = {depth}, forced {forced}, cell {position}"
                        );
                        assert!(reading.residual <= tree.face_rule());
                    }
                    assert!(within_node_bound(&tree, &arrivals(&declared, &stream)));
                    carries += oracle.carries();
                }
            }
        }
        assert!(carries > 0, "{capacity}: the registers carried");
    }
    let windows: Vec<usize> = (0..90u64)
        .map(|t| ((t * 7 + t / 3 + t * t / 11) % 5) as usize)
        .collect();
    for (depth, capacity) in [(2, Capacity::Ceiling(1)), (9, Capacity::Ceiling(2))] {
        window_in_cell_order(&windows, StopPrior::half(), depth, capacity);
    }
}

// -------------------------------------------------------------------------------------------
// the online context baselines

/// A stream over four classes: a period-four pattern with one cell in eight drawn at random.
fn baseline_source(length: usize, seed: u64) -> Vec<usize> {
    let mut draw = Draw::new(seed);
    (0..length)
        .map(|k| {
            if draw.next() % 8 == 0 {
                (draw.next() % 4) as usize
            } else {
                [0, 1, 2, 1][k % 4]
            }
        })
        .collect()
}

/// **The baselines' exact faces are the faces their codes read** (`Baselines::face_cell`, the
/// reader that multiplies a passage's faces, the wide cut): stepped beside `code_cell` over the same
/// cells, each face's code length is the enclosure `code_cell` returns, and a cell outside the
/// chart is refused.
#[test]
fn the_baselines_faces_are_the_faces_their_codes_read() {
    let cells = baseline_source(96, 5);
    let (mut faces, mut codes) = (Baselines::new(4).unwrap(), Baselines::new(4).unwrap());
    for &cell in &cells {
        let face = faces.face_cell(cell).unwrap();
        let code = codes.code_cell(cell).unwrap();
        assert_eq!(code_length(&face.uniform).unwrap(), code.uniform);
        assert_eq!(code_length(&face.order_zero).unwrap(), code.order_zero);
        assert_eq!(code_length(&face.order_one).unwrap(), code.order_one);
        assert_eq!(code_length(&face.ppm).unwrap(), code.ppm);
    }
    assert!(matches!(
        faces.face_cell(4),
        Err(ContextError::CellOutside { .. })
    ));
}

/// The baselines read their code lengths by the certified integer binary logarithm
/// ([`code_length`]): every enclosure contains the exact value the series enclosure
/// (`ratio::algebraic::log2_enclosure`) contains, so the two meet, and both read the same grain cell wherever
/// their widths lie inside one; uniform over 2^k classes reads exactly `k`.
#[test]
fn the_baselines_read_their_exact_code_lengths_by_the_binary_logarithm() {
    let cells = baseline_source(64, 3);
    let mut baselines = Baselines::new(4).unwrap();
    let mut ppm = Ppm::new(2, 4);
    let mut counts = [0u64; 4];
    for (seen, &cell) in cells.iter().enumerate() {
        let kt = kt_probability(counts[cell], seen as u64, 4);
        let series = log2_enclosure(&kt.recip()).unwrap();
        let binary = code_length(&kt).unwrap();
        assert!(binary.lower <= series.upper && series.lower <= binary.upper);
        let mass = ppm.mass(cell);
        let (series, binary) = (
            log2_enclosure(&mass.recip()).unwrap(),
            code_length(&mass).unwrap(),
        );
        assert!(binary.lower <= series.upper && series.lower <= binary.upper);
        let codes = baselines.code_cell(cell).unwrap();
        assert_eq!(codes.order_zero, code_length(&kt).unwrap());
        assert_eq!(
            codes.uniform,
            ExactInterval::point(Rat::from_integer(2.into()))
        );
        ppm.update(cell);
        counts[cell] += 1;
    }
}

/// **The prior mass** (module header, "The prior mass"): at `2^(−j)`, `j ∈ {1, 2, 3, 8}`, a fresh
/// node's binary face after `n_b` of `n` arrivals is `(2^j n_b + 1)/(2^j n + 2)` in the oracle; the
/// executed faces stay exactly normalized, within the rule and within their certificates of the
/// oracle; and a deterministic run is coded more cheaply the smaller the prior mass. A ceiling
/// below KT's half-unit masses is refused.
#[test]
fn the_prior_mass_reads_its_masses_and_keeps_the_rule() {
    let alphabet = 5;
    let stream: Vec<usize> = (0..40u64).map(|t| ((t * 7 + t / 3) % 5) as usize).collect();
    let mut previous: Option<Rat> = None;
    for mass in [1u32, 2, 3, 8] {
        let declared = LandmarkDeclaration { mass, ..declaration(alphabet, 2) };
        let mut tree = Landmarks::new(declared.clone()).unwrap();
        let mut oracle = IdealLandmarks::new(declared.clone(), None).unwrap();
        assert!(tree.face_rule() < rat(1, 32), "j = {mass}");
        for (position, &cell) in stream.iter().enumerate() {
            let here = address(&stream, position, 2);
            let face = tree.face(&here, 16).unwrap();
            assert_eq!(face.probabilities.iter().cloned().sum::<Rat>(), Rat::one());
            let ideal: Rat = (0..alphabet)
                .map(|class| oracle.probability(&here, class).unwrap())
                .sum();
            assert_eq!(ideal, Rat::one());
            let reading = tree.receive(&here, cell).unwrap();
            let face = oracle.receive(&here, cell).unwrap();
            assert!(reading.residual <= tree.face_rule());
            assert!(within(&reading.executed, &face, &reading.residual));
        }
        // A binary depth-0 tree after a run of three zeros reads (3·2^j + 1)/(3·2^j + 2).
        let binary = LandmarkDeclaration { mass, ..declaration(2, 0) };
        let mut run = IdealLandmarks::new(binary, None).unwrap();
        let mut weight = Rat::one();
        for _ in 0..3 {
            weight *= run.receive(&[], 0).unwrap();
        }
        let unit = BigInt::one() << mass as usize;
        let next = run.probability(&[], 0).unwrap();
        assert_eq!(next, Rat::new(&unit * 3 + 1, &unit * 3 + 2));
        if let Some(previous) = &previous {
            assert!(weight > *previous);
        }
        previous = Some(weight);
    }
    let ceiling = LandmarkDeclaration {
        mass: 3,
        capacity: Capacity::Ceiling(4),
        ..declaration(alphabet, 2)
    };
    assert!(Landmarks::new(ceiling).is_err());
}

/// **The root's base** (module header; [`BaseMeasure::Root`]): at prior masses `2^(−1)` and
/// `2^(−3)`, every node of a digit tree splits its prior masses by one base read from its root, so
/// the executed faces stay exactly normalized, within the rule and within their certificates of
/// the oracle; a fresh digit tree reads the even split; and a context never seen leans on its
/// root's split.
#[test]
fn the_roots_base_keeps_the_rule_and_leans_on_the_unconditional_split() {
    use crate::compression::landmark::context::BaseMeasure;
    let alphabet = 5;
    let stream: Vec<usize> = (0..60u64)
        .map(|t| if t % 4 == 3 { ((t * 7 + t / 3) % 5) as usize } else { 1 })
        .collect();
    for mass in [1u32, 3] {
        let mut codes = Vec::new();
        for base in [BaseMeasure::Even, BaseMeasure::Root] {
            let declared = LandmarkDeclaration { mass, base, ..declaration(alphabet, 3) };
            let mut tree = Landmarks::new(declared.clone()).unwrap();
            let mut oracle = IdealLandmarks::new(declared, None).unwrap();
            assert!(tree.face_rule() < rat(1, 32), "j = {mass}, {base:?}");
            let mut code = Rat::one();
            for (position, &cell) in stream.iter().enumerate() {
                let here = address(&stream, position, 3);
                let face = tree.face(&here, 16).unwrap();
                assert_eq!(face.probabilities.iter().cloned().sum::<Rat>(), Rat::one());
                let ideal: Rat = (0..alphabet)
                    .map(|class| oracle.probability(&here, class).unwrap())
                    .sum();
                assert_eq!(ideal, Rat::one());
                let reading = tree.receive(&here, cell).unwrap();
                let exact = oracle.receive(&here, cell).unwrap();
                assert!(reading.residual <= tree.face_rule());
                assert!(within(&reading.executed, &exact, &reading.residual));
                code *= exact;
            }
            codes.push(code);
        }
        assert_ne!(codes[0], codes[1]);
    }
    // After its root has seen class 1 ten times in one context, a context never seen leans on the
    // root's split at the root's base and on the even split at the even base.
    let leaning = |base| {
        let mut tree =
            Landmarks::new(LandmarkDeclaration { mass: 3, base, ..declaration(alphabet, 3) }).unwrap();
        let seen = [Letter::Cell(0), Letter::Cell(0), Letter::Cell(0)];
        for _ in 0..10 {
            tree.receive(&seen, 1).unwrap();
        }
        tree.probability(&[Letter::Cell(3), Letter::Cell(3), Letter::Cell(3)], 1).unwrap()
    };
    assert!(leaning(BaseMeasure::Root) > leaning(BaseMeasure::Even));
    // A fresh digit tree reads the even split at either base.
    let fresh = |base| {
        let tree = Landmarks::new(LandmarkDeclaration { base, ..declaration(2, 2) }).unwrap();
        tree.probability(&[Letter::Boundary, Letter::Boundary], 0).unwrap()
    };
    assert_eq!(fresh(BaseMeasure::Root), fresh(BaseMeasure::Even));
}

/// **The root's base is read before the arrival's own deposit** ([`BaseMeasure::Root`]; Lean
/// `Compression/Landmark/Context/BaseMeasure.deposit_first_overcounts`: a root base read after the
/// deposit gives either digit `11/16` on an empty passage at `j = 3`, `11/8` in all). At campaign
/// 1's prior mass `2^(−3)`, every receipt's executed mass is the score read at the standing before
/// its deposit, and those scores sum to one over the classes; a fresh binary tree reads `½` for
/// either digit's first arrival.
#[test]
fn the_roots_base_is_read_before_the_arrivals_deposit() {
    use crate::compression::landmark::context::BaseMeasure;
    let alphabet = 5;
    let stream: Vec<usize> = (0..60u64)
        .map(|t| if t % 4 == 3 { ((t * 7 + t / 3) % 5) as usize } else { 1 })
        .collect();
    let declared = LandmarkDeclaration {
        mass: 3,
        base: BaseMeasure::Root,
        ..declaration(alphabet, 3)
    };
    let mut tree = Landmarks::new(declared).unwrap();
    for (position, &cell) in stream.iter().enumerate() {
        let here = address(&stream, position, 3);
        let before: Vec<Rat> = (0..alphabet)
            .map(|class| tree.probability(&here, class).unwrap())
            .collect();
        assert_eq!(before.iter().cloned().sum::<Rat>(), Rat::one(), "position {position}");
        let reading = tree.receive(&here, cell).unwrap();
        assert_eq!(reading.executed, before[cell], "position {position}");
    }
    for digit in 0..2 {
        let mut fresh = Landmarks::new(LandmarkDeclaration {
            mass: 3,
            base: BaseMeasure::Root,
            ..declaration(2, 2)
        })
        .unwrap();
        let here = [Letter::Boundary, Letter::Boundary];
        assert_eq!(fresh.receive(&here, digit).unwrap().executed, rat(1, 2));
        assert!(fresh.probability(&here, digit).unwrap() > rat(1, 2));
    }
}
