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
//! the old `u128` refusal whose certified residual stays within the grain. Decision 32: the declared
//! stop prior on the dyadic ladder (the block recursion at any stop weights, the founding ratio
//! `2^j − 1`, the lattice law, the faces and windows under a prior), campaign 2's constant-slot
//! controls as the per-depth prior `(1, r + 1)`, and the prior sweep on the development cells.
//! Decision 34: the node-local law against the own-weight block recursion, its faces normalized and
//! certified, its refusals; the join tree's prior; the joins as the Bayesian mixture per dyadic
//! cell; and the stop-weight mixture per digit tree telescoping per dyadic cell. Decision 36: the
//! convergence-founded oracle against the tree with absent children simulated apart (exact in ℚ),
//! the founding at the second arrival with the first arrival's count, Decision 28 as the first
//! arrival, the executed faces normalized and certified, the stopped path's lattice law, the memory
//! bounded at every depth, a window in cell order, and the founded prequential pass and sweep.

use std::collections::HashMap;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

use crate::hnn::HnnError;
use crate::hnn::landmark::{
    Beta, Bundle, DigitsReading, FaceJoins, Feature, Founding, IdealLandmarks, JoinTree,
    LandmarkDeclaration, LandmarkFace, Landmarks, Letter, LetterFamily, LocalLaw, PassageCode,
    StopMixture, StopPrior, Widths, address, binary_log, carrier_width, cell_letters, choose_depth,
    choose_depth_founded, choose_prior, code_length, face_bits, ladder_top, lattice_mix,
    letter_address, prequential, prior_family, ratio_code_length, tree_prequential,
    tree_prequential_founded,
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
        prior: StopPrior::half(),
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
/// `W_s = w_d E_s + (1 − w_d) Π_b W_bs` at the node's depth `d` (Lean `HNN/LandmarkTree.stopWeight`;
/// `½` is Decision 28's), over the symbols of `stream[past..]` whose context (newest first) extends
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

/// The stop priors the laws are checked under: Decision 28's `½`, two global rungs and two
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
/// `HNN/LandmarkTree.{stop_weight_step, stop_founding_step}`; the oracle, `β` exact, founded at
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

/// **The lattice law, recomputed in ℚ** at every step on every opened path: a founded leaf reads
/// `⟦k_D(0)⟧`, the first unfounded depth the prior `1/2`, a forced depth its child, and a mixing
/// depth `⟦λ̂ k(0) + (1 − λ̂) q̂'(0)⟧` with `λ̂ = ⟦β/(1 + β)⟧₀¹`, every face a numerator of
/// `2^(−M_p)` inside `[1, 2^(M_p) − 1]` (Lean `HNN/LandmarkTree.lattice_path_laws`); after the
/// deposit each mixing node's `β` is `β k(b)/q̂'(b)`, or its rebase within `2^(1−W)` below it.
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
                // A node this arrival founded keeps its depth's β₀ = 2^(j_d) − 1.
                for d in old.founded..new.founded {
                    let founding = BigInt::from(prior.founding(d));
                    assert_eq!(
                        new.betas[d],
                        Rat::from_integer(founding),
                        "{prior}, d = {d}"
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
    for prior in [StopPrior::half(), StopPrior::per_depth(vec![2, 5]).unwrap()] {
        window_in_cell_order(&stream, prior);
    }
}

/// One stop prior's run of `landmark_window_faces_read_each_phase_after_the_earlier_deposits`.
fn window_in_cell_order(stream: &[usize], prior: StopPrior) {
    let declared = LandmarkDeclaration {
        population: 90,
        prior,
        ..declaration(5, 2)
    };
    let mut tree = Landmarks::with_carrier(declared.clone(), 6).unwrap();
    let aperture = 3;
    for start in (0..stream.len()).step_by(aperture) {
        let window = start..(start + aperture).min(stream.len());
        let addresses: Vec<Vec<Letter>> = window
            .clone()
            .map(|position| address(stream, position, 2))
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
    let last = [address(stream, 88, 2), address(stream, 89, 2)];
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
    let mut products = [Rat::one(), Rat::one()];
    for (position, &cell) in cells.iter().enumerate() {
        let reading = tree.receive(&address(&cells, position, 2), cell).unwrap();
        let length = code_length(&reading.executed).unwrap();
        let part = 2 * usize::from(position >= 36);
        sums[part] += length.lower;
        sums[part + 1] += length.upper;
        products[part / 2] *= &reading.executed;
    }
    // The run encloses the faces' product (`PassageCode`): it meets the per-cell sum and the
    // product's own code length, within `2^(−80)` bits.
    for (part, coded) in [&run.development.tree, &run.held_out.tree]
        .into_iter()
        .enumerate()
    {
        let whole = code_length(&products[part]).unwrap();
        assert!(coded.lower <= sums[2 * part + 1] && sums[2 * part] <= coded.upper);
        assert!(coded.lower <= whole.upper && whole.lower <= coded.upper);
        assert!(&coded.upper - &coded.lower <= rat_power(-80));
    }
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
    // The declaration reaches 2^19 cells.
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

/// **The split operands are the single division** (module header, "The lattice mixture and the
/// stop weight read split operands"; Decision 35): at widths where the single division
/// `(2^M λ̂ u + (2^M − λ̂) x v)/(2^M v)` passes `u128`, `lattice_mix` returns the nearest lattice
/// numerator of `λ̂u/v + (1 − λ̂)x` (ties up, inside `[1, 2^M − 1]`), read exactly in `ℕ`; the stop
/// weight decided before its division is the exact rounding of `2^M β/(1 + β)`; and the wide cut's
/// `2^20` cells declare at `D = 1, …, 8`, where the single division's `2M_p + κ + 3` passed 128
/// bits (133 at `D = 4`), up to `19,372,659` cells at `D = 4`, while the single divisions (the card
/// kernel's) admit to `605,394`.
#[test]
fn landmark_split_operands_are_the_single_division() {
    let mut draw = super::support::Draw::new(35);
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
        (54, 35, 89)
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
    // The single divisions (the card kernel's realization) admit to 605,394 cells and no further.
    let single = |population: u64| {
        Widths::derived(&LandmarkDeclaration {
            population,
            ..declaration(256, 4)
        })
        .single_division_admitted(population)
    };
    assert!(single(1 << 19) && single(605_394) && !single(605_395) && !single(1 << 20));
}

/// **A passage's code is its faces' product, enclosed once** (`PassageCode`, Decision 35): over
/// dyadic sides, dyadic faces and faces with odd denominators (a KT face), the product's bounds hold
/// the exact product between them, and its code length meets the exact product's enclosure within
/// `f 2^(−125) + 2^(−95)` bits; two passages joined are their faces together; bounds compare as
/// integers.
#[test]
fn landmark_passage_code_is_the_faces_product() {
    let mut draw = super::support::Draw::new(20);
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
    let integer = |bound: &crate::hnn::landmark::ProductBound| {
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
// Decision 32: the declared stop prior

/// **The stop prior is the dyadic ladder** (Lean `HNN/LandmarkTree.ladder_founding`): rung `j`
/// stops with `1 − 2^(−j)` and founds at `2^j − 1`; `[1]` is Decision 28's `½`; a repeated last
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

/// **Each node is founded at its depth's ratio** (Lean `HNN/LandmarkTree.stop_founding_step`): the
/// founding chart is `β₀ = 2^(j_d) − 1` exactly with the stop weight `λ̂ = 1 − 2^(−j_d)` on the
/// lattice, the nodes one arrival founds carry it, and a rung past the carrier `W` is refused (its
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
    let here = [Letter::Boundary; 3];
    tree.receive(&here, 1).unwrap();
    let path = &tree.opened(&here, 1).unwrap()[0];
    assert_eq!(path.founded, 4);
    for (depth, beta) in path.betas.iter().enumerate() {
        assert_eq!(
            beta,
            &Rat::from_integer(BigInt::from(prior.founding(depth)))
        );
    }
    let wide = LandmarkDeclaration {
        prior: StopPrior::global(13).unwrap(),
        ..declaration(4, 2)
    };
    assert!(Landmarks::with_carrier(wide.clone(), 12).is_err());
    assert!(Landmarks::with_carrier(wide, 13).is_ok());
}

/// **Campaign 2's constant-slot controls are the per-depth prior `(1, r + 1)`** (Decision 32; Lean
/// `HNN/LandmarkTree.stop_mixture_over_trees`): in the bundle branch over `r` slots of one letter, a
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

/// **The prior sweep reads the development cells only** (Decision 32's choice): every law of the
/// family runs its own depth sweep ([`choose_depth`]), changing the held-out cells changes nothing,
/// the choice is charged `⌈log₂⌉` of the laws tried, the incumbent is Decision 28's `½`, the chosen
/// law is the incumbent or the least charged law strictly below it, and a family without `½` is
/// refused. [`tree_prequential`] is [`prequential`]'s tree.
#[test]
fn landmark_prior_sweep_reads_the_development_cells_only() {
    let cells: Vec<usize> = (0..96u64)
        .map(|t| ((t * 3 + t / 5 + t * t / 7) % 4) as usize)
        .collect();
    let tail = 72..96;
    let cut = Cut {
        cells: cells.clone(),
        held_out: vec![tail],
    };
    let letters = cell_letters(&cut.cells);
    let declared = LandmarkDeclaration {
        population: 96,
        ..declaration(4, 1)
    };
    let family = prior_family(3);
    let sweep = choose_prior(&cut, &letters, &declared, &family).unwrap();
    let mut other = cut.clone();
    for cell in &mut other.cells[72..] {
        *cell = 3 - *cell;
    }
    assert_eq!(
        choose_prior(&other, &cell_letters(&other.cells), &declared, &family).unwrap(),
        sweep
    );
    assert_eq!(sweep.incumbent, 0);
    assert_eq!(sweep.description_bits, 4);
    assert_eq!(sweep.tried.len(), 9);
    for (prior, depths) in &sweep.tried {
        let at = LandmarkDeclaration {
            prior: prior.clone(),
            ..declared.clone()
        };
        assert_eq!(&choose_depth(&cut, &letters, &at).unwrap(), depths);
    }
    let chosen = sweep.charged(sweep.chosen);
    if sweep.chosen != sweep.incumbent {
        assert!(chosen.upper < sweep.charged(sweep.incumbent).lower);
        assert!((0..9).all(|index| chosen.upper <= sweep.charged(index).upper));
    }
    assert_eq!(
        sweep.decided,
        (0..9).all(|index| index == sweep.chosen || chosen.upper < sweep.charged(index).lower)
    );
    assert_eq!(
        sweep.chosen_description(),
        4 + sweep.tried[sweep.chosen].1.description_bits
    );
    assert!(choose_prior(&cut, &letters, &declared, &family[1..]).is_err());

    let at = LandmarkDeclaration {
        prior: StopPrior::per_depth(vec![1, 3]).unwrap(),
        depth: 2,
        ..declared
    };
    let ([development, held], run) = tree_prequential(&cut, &letters, &at).unwrap();
    let both = prequential(&cut, &letters, &at).unwrap();
    assert_eq!(
        (development, held),
        (both.development.tree, both.held_out.tree)
    );
    assert_eq!(run, both.run);
    assert!(run.largest_residual <= run.face_rule);
}

// -------------------------------------------------------------------------------------------
// Decision 34: weighing is local

/// An external digit-0 face on the tree's lattice `2^(−M)`: a declared odd numerator pattern,
/// never a tuned value, inside the open unit interval.
fn external_split(face_bits: u64, t: usize, h: usize) -> u64 {
    let eighths = 1 + ((t * 5 + h * 3) % 7) as u64;
    eighths << (face_bits - 3)
}

/// **The own-weight block recursion** (Lean `HNN/LocalWeighing.{ownWeight,
/// own_mixture_over_trees}`), independent of the path law: `W_s = E_s` at depth `D`, otherwise
/// `W_s = w_d E_s + (1 − w_d) Π_b W_bs`, with the node-local own weight
/// `E_s = π KT_s + (1 − π) X_s` over the digits routed to `s` (`X_s` the external faces' product).
fn own_block_weight(
    stream: &[usize],
    external: &[Rat],
    past: usize,
    context: &[usize],
    depth: usize,
    prior: &StopPrior,
    law: &LocalLaw,
) -> Rat {
    let routed: Vec<usize> = (past..stream.len())
        .filter(|&t| {
            context
                .iter()
                .enumerate()
                .all(|(back, &x)| stream[t - 1 - back] == x)
        })
        .collect();
    let symbols: Vec<usize> = routed.iter().map(|&t| stream[t]).collect();
    let foreign: Rat = routed
        .iter()
        .map(|&t| {
            if stream[t] == 0 {
                external[t].clone()
            } else {
                Rat::one() - &external[t]
            }
        })
        .product();
    let pi = law.weight();
    let estimate = &pi * kt_block(&symbols) + (Rat::one() - &pi) * foreign;
    if context.len() == depth {
        return estimate;
    }
    let split: Rat = (0..2)
        .map(|b| {
            let mut child = context.to_vec();
            child.push(b);
            own_block_weight(stream, external, past, &child, depth, prior, law)
        })
        .product();
    let stop = prior.weight(context.len());
    &stop * estimate + (Rat::one() - &stop) * split
}

/// **The node-local law is the own-weight recursion** (Lean `HNN/LocalWeighing.{own_weight_step,
/// own_ratio_step, node_local_founding, two_face_prior}`): on a binary stream with a declared
/// external face, the oracle (`β` and `γ` exact, each node's own ratio founded at `γ₀ ½/x(b)`)
/// multiplies to the block recursion with `E_s = π KT_s + (1 − π) X_s` at every depth up to 3,
/// under Decision 28's `½` and a per-depth prior, at two rungs; and the executed tree stays within
/// its certificate of the oracle at every cell.
#[test]
fn landmark_local_law_is_the_own_weight_recursion() {
    let stream: Vec<usize> = (0..22u64)
        .map(|t| usize::from((t * t + 5 * t) % 7 < 3))
        .collect();
    for law in [LocalLaw::new(1).unwrap(), LocalLaw::new(3).unwrap()] {
        for prior in [StopPrior::half(), StopPrior::per_depth(vec![1, 3]).unwrap()] {
            for depth in 0..=3 {
                let declared = LandmarkDeclaration {
                    prior: prior.clone(),
                    ..declaration(2, depth)
                };
                let mut oracle = IdealLandmarks::local(declared.clone(), None, law).unwrap();
                let mut tree = Landmarks::local(declared, law).unwrap();
                let bits = tree.face_bits();
                let scale = Rat::from_integer(BigInt::one() << bits as usize);
                let splits: Vec<u64> = (0..stream.len())
                    .map(|t| external_split(bits, t, 1))
                    .collect();
                let external: Vec<Rat> = splits
                    .iter()
                    .map(|&x| Rat::from_integer(BigInt::from(x)) / &scale)
                    .collect();
                let mut ideal = Rat::one();
                for t in depth..stream.len() {
                    let here = address(&stream, t, depth);
                    let face = oracle
                        .receive_with(&here, stream[t], &external[t..=t])
                        .unwrap();
                    let reading = tree.receive_with(&here, stream[t], &splits[t..=t]).unwrap();
                    assert!(
                        within(&reading.executed, &face, &reading.residual),
                        "{law}, {prior}, D = {depth}, cell {t}"
                    );
                    ideal *= face;
                }
                assert_eq!(
                    ideal,
                    own_block_weight(&stream, &external, depth, &[], depth, &prior, &law),
                    "{law}, {prior}, D = {depth}"
                );
            }
        }
    }
}

/// **The node-local tree's faces are normalized exactly and certified** over five classes (the
/// third digit forced where the upper half is empty): the all-class face under the external
/// faces sums to 1, each class's face is the one-class read with that class's opened digits'
/// external faces, and each cell's certificate holds against the oracle.
#[test]
fn landmark_local_faces_are_normalized_and_certified() {
    let alphabet = 5;
    let stream: Vec<usize> = (0..36u64).map(|t| ((t * 7 + t / 3) % 5) as usize).collect();
    let law = LocalLaw::new(2).unwrap();
    let declared = declaration(alphabet, 2);
    let mut tree = Landmarks::local(declared.clone(), law).unwrap();
    let mut oracle = IdealLandmarks::local(declared.clone(), None, law).unwrap();
    let bits = tree.face_bits();
    let scale = Rat::from_integer(BigInt::one() << bits as usize);
    for (position, &cell) in stream.iter().enumerate() {
        let here = address(&stream, position, 2);
        let by_dyadic: Vec<u64> = tree
            .splitting()
            .iter()
            .map(|&h| external_split(bits, position, h))
            .collect();
        let face = tree.face_with(&here, 16, &by_dyadic).unwrap();
        let sum: Rat = face.probabilities.iter().cloned().sum();
        assert_eq!(sum, Rat::one());
        let opened = |class: usize| -> Vec<u64> {
            declared
                .emitted(class)
                .iter()
                .map(|&(h, _)| external_split(bits, position, h))
                .collect()
        };
        let ideal: Rat = (0..alphabet)
            .map(|class| {
                let external: Vec<Rat> = opened(class)
                    .iter()
                    .map(|&x| Rat::from_integer(BigInt::from(x)) / &scale)
                    .collect();
                oracle.probability_with(&here, class, &external).unwrap()
            })
            .sum();
        assert_eq!(ideal, Rat::one());
        for class in 0..alphabet {
            let p = &face.probabilities[class];
            assert!(p > &Rat::zero());
            assert_eq!(
                p,
                &tree
                    .score_with(&here, class, &opened(class))
                    .unwrap()
                    .executed
            );
        }
        let external: Vec<Rat> = opened(cell)
            .iter()
            .map(|&x| Rat::from_integer(BigInt::from(x)) / &scale)
            .collect();
        let reading = tree.receive_with(&here, cell, &opened(cell)).unwrap();
        let ideal = oracle.receive_with(&here, cell, &external).unwrap();
        assert!(within(&reading.executed, &ideal, &reading.residual));
    }
    assert!(tree.bits() > 0);
}

/// **The node-local law's refusals**: a tree under the law refuses a read without its external
/// faces, a window read, and external faces outside the lattice's open unit interval; a tree
/// without the law refuses external faces; a rung outside the ladder or past the carrier is
/// refused.
#[test]
fn landmark_local_refusals() {
    let declared = declaration(4, 1);
    let law = LocalLaw::new(2).unwrap();
    let mut local = Landmarks::local(declared.clone(), law).unwrap();
    let mut plain = Landmarks::new(declared.clone()).unwrap();
    let here = address(&[1, 2], 1, 1);
    let full = 1u64 << local.face_bits();
    assert!(local.receive(&here, 2).is_err());
    assert!(
        local
            .window_splits(std::slice::from_ref(&here), &[])
            .is_err()
    );
    assert!(local.receive_with(&here, 2, &[0, 5]).is_err());
    assert!(local.receive_with(&here, 2, &[full, 5]).is_err());
    assert!(local.receive_with(&here, 2, &[5]).is_err());
    assert!(plain.receive_with(&here, 2, &[5, 5]).is_err());
    assert!(local.receive_with(&here, 2, &[5, full - 5]).is_ok());
    assert!(plain.receive(&here, 2).is_ok());
    assert_eq!(local.local_law(), Some(law));
    assert_eq!(plain.local_law(), None);
    assert!(LocalLaw::new(0).is_err());
    assert!(LocalLaw::new(64).is_err());
    let wide = LocalLaw::new(u32::try_from(local.widths().carrier).unwrap() + 1).unwrap();
    assert!(Landmarks::local(declared, wide).is_err());
}

/// **A join tree's prior sums to one** (Lean `HNN/LocalWeighing.static_mixture`): the balanced
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
/// `HNN/LocalWeighing.{static_mixture, forward_executed}`): three declared lattice faces in two
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

/// **The stop-weight mixture per digit tree** (Lean `HNN/LocalWeighing.stop_mixture_per_tree`):
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
            .map(|tree| tree.receive_digits(&here, cell, &[]).unwrap())
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
// Decision 36: a landmark is founded where paths converge, at its second arrival

/// A tree of `declared` founded at the second arrival.
fn converging(declared: LandmarkDeclaration) -> Landmarks {
    Landmarks::new(declared)
        .unwrap()
        .founded_at(Founding::SecondArrival)
        .unwrap()
}

/// The oracle of `declared` founded at the second arrival, `β` exact.
fn converging_oracle(declared: LandmarkDeclaration) -> IdealLandmarks {
    IdealLandmarks::new(declared, None)
        .unwrap()
        .founded_at(Founding::SecondArrival)
        .unwrap()
}

/// The KT mass of binary counts, `Π (j + ½)/Π (j + 1)`.
fn kt_mass(counts: [i64; 2]) -> Rat {
    let mut seen = [0i64; 2];
    let mut mass = Rat::one();
    for x in 0..2 {
        for _ in 0..counts[x] {
            mass *= rat(2 * seen[x] + 1, 2 * (seen[0] + seen[1]) + 2);
            seen[x] += 1;
        }
    }
    mass
}

/// One reached node of the convergence standing: its counts, its opening count and its
/// pre-factor.
#[derive(Clone)]
struct Reached {
    count: [i64; 2],
    opening: [i64; 2],
    pre: Rat,
}

/// **The convergence standing, simulated apart from the tree** (Lean
/// `HNN/ConvergenceFounding.Convergence.receive`) over the binary symbols of `stream[past..]`, the
/// nodes keyed by their letter codes newest first: each arrival stops at `τ`, the deepest present
/// node (the root, or a node an earlier arrival reached); the stopped path counts the symbol; below
/// the stop the absent child is reached, opens with this count, and its pre-factor takes the
/// stopped node's KT face.
fn converge_standing(stream: &[usize], past: usize, depth: usize) -> HashMap<Vec<u64>, Reached> {
    let mut standing: HashMap<Vec<u64>, Reached> = HashMap::new();
    for t in past..stream.len() {
        let codes: Vec<u64> = address(stream, t, depth)
            .into_iter()
            .map(Letter::code)
            .collect();
        let x = stream[t];
        let present = |s: &[u64], standing: &HashMap<Vec<u64>, Reached>| {
            s.is_empty() || standing.get(s).is_some_and(|n| n.count[0] + n.count[1] > 0)
        };
        let mut stop = 0;
        while stop < depth && present(&codes[..stop + 1], &standing) {
            stop += 1;
        }
        if stop < depth {
            let parent = standing.get(&codes[..stop]).map_or([0, 0], |n| n.count);
            let face = rat(2 * parent[x] + 1, 2 * (parent[0] + parent[1]) + 2);
            let child = standing
                .entry(codes[..stop + 1].to_vec())
                .or_insert(Reached {
                    count: [0, 0],
                    opening: [0, 0],
                    pre: Rat::one(),
                });
            child.pre *= face;
            child.opening[x] += 1;
        }
        for d in 0..=(stop + 1).min(depth) {
            let node = standing.entry(codes[..d].to_vec()).or_insert(Reached {
                count: [0, 0],
                opening: [0, 0],
                pre: Rat::one(),
            });
            node.count[x] += 1;
        }
    }
    standing
}

/// **The weight of the convergence standing** (Lean `HNN/ConvergenceFounding.convWeight`):
/// `W_s = E_s` at depth `D`, else `w_d E_s + (1 − w_d) Π_b R_(s b) W_(s b)` over the reached children
/// (an unreached child weighs one), with `E_s = KT(counts)/KT(opening)`.
fn converge_weight(
    standing: &HashMap<Vec<u64>, Reached>,
    s: &[u64],
    depth: usize,
    prior: &StopPrior,
) -> Rat {
    let own = standing
        .get(s)
        .map_or(Rat::one(), |n| kt_mass(n.count) / kt_mass(n.opening));
    if s.len() == depth {
        return own;
    }
    let split: Rat = standing
        .iter()
        .filter(|(k, _)| k.len() == s.len() + 1 && k.starts_with(s))
        .map(|(k, n)| &n.pre * converge_weight(standing, k, depth, prior))
        .product();
    let stop = prior.weight(s.len());
    &stop * own + (Rat::one() - &stop) * split
}

/// **The convergence-founded oracle is the tree with absent children** (Lean
/// `HNN/ConvergenceFounding.{convergence_is_probability, convergence_step, conv_weight_step}`): on a
/// binary stream at every depth up to 5 and under several stop priors, the product of the oracle's
/// faces (`β` exact) equals, exactly in ℚ, the root weight of the convergence standing simulated
/// apart from the tree (each node's KT given its opening count, each absent child's pre-factor);
/// the executed tree founded at the second arrival stays within its certificate of the oracle
/// cell by cell, and its faces are normalized.
#[test]
fn landmark_convergence_oracle_is_the_absent_child_weight() {
    let stream: Vec<usize> = (0..60u64)
        .map(|t| usize::from((t * t + 3 * t + t / 5) % 7 < 3))
        .collect();
    for prior in priors() {
        for depth in 0..=5 {
            let declared = LandmarkDeclaration {
                prior: prior.clone(),
                ..declaration(2, depth)
            };
            let mut oracle = converging_oracle(declared.clone());
            let mut tree = converging(declared);
            let mut ideal = Rat::one();
            for t in depth..stream.len() {
                let here = address(&stream, t, depth);
                let sum =
                    oracle.probability(&here, 0).unwrap() + oracle.probability(&here, 1).unwrap();
                assert_eq!(sum, Rat::one());
                let face = oracle.receive(&here, stream[t]).unwrap();
                let reading = tree.receive(&here, stream[t]).unwrap();
                assert!(within(&reading.executed, &face, &reading.residual));
                assert!(reading.residual <= tree.face_rule());
                ideal *= face;
            }
            let standing = converge_standing(&stream, depth, depth);
            assert_eq!(
                ideal,
                converge_weight(&standing, &[], depth, &prior),
                "{prior}, D = {depth}"
            );
            // The executed tree founds a node for each reached node that met a second arrival.
            let founded = standing
                .iter()
                .filter(|(k, n)| k.is_empty() || n.count[0] + n.count[1] >= 2)
                .count();
            assert_eq!(tree.nodes(), founded, "{prior}, D = {depth}");
            assert_eq!(tree.pending(), standing.len() - founded);
        }
    }
}

/// **A node is founded at its second arrival, opening with its first arrival's count** (Lean
/// `HNN/ConvergenceFounding.second_arrival_opens_with_the_first_count`): the first arrival reads
/// the root alone (the prior `½`), founds only the root and records the child's pending arrival;
/// the second arrival at the same address opens that child with its one count (KT's `3/4` for the
/// same digit), the root mixing over it, and its deposit founds it with both counts and records
/// the grandchild; an arrival at a new context stops at the root. The oracle reads the same faces.
#[test]
fn landmark_convergence_founds_at_the_second_arrival() {
    let declared = declaration(2, 3);
    let mut tree = converging(declared.clone());
    let mut oracle = converging_oracle(declared);
    let here = [Letter::Cell(1), Letter::Cell(0), Letter::Cell(1)];
    let first = tree.opened(&here, 0).unwrap();
    assert_eq!(first[0].founded, 0);
    assert_eq!(first[0].faces, vec![rat(1, 2)]);
    assert_eq!(tree.receive(&here, 0).unwrap().executed, rat(1, 2));
    assert_eq!(oracle.receive(&here, 0).unwrap(), rat(1, 2));
    assert_eq!((tree.nodes(), tree.pending()), (1, 1));
    // The second arrival opens the pending child with its first arrival's count.
    let second = tree.opened(&here, 0).unwrap();
    assert_eq!(second[0].founded, 1);
    assert_eq!(second[0].faces.len(), 2);
    assert_eq!(second[0].faces[1], rat(3, 4));
    let ideal = oracle.opened(&here, 0).unwrap();
    assert_eq!(ideal[0].faces[1], rat(3, 4));
    let executed = tree.receive(&here, 1).unwrap().executed;
    let face = oracle.receive(&here, 1).unwrap();
    assert!(within(&executed, &face, &rat(1, 1 << 20)));
    assert_eq!((tree.nodes(), tree.pending()), (2, 1));
    // The founded child holds its opening count and this arrival's: half-units [3, 3].
    assert_eq!(tree.arena().halves()[1], [3, 3]);
    assert_eq!(tree.arena().children().len(), 1);
    // A new context stops at the root, which reads its KT face alone.
    let other = [Letter::Cell(0), Letter::Cell(0), Letter::Cell(0)];
    let path = tree.opened(&other, 0).unwrap();
    assert_eq!((path[0].founded, path[0].faces.len()), (1, 1));
    tree.receive(&other, 0).unwrap();
    assert_eq!((tree.nodes(), tree.pending()), (2, 2));
    // The root's β stepped at the second arrival only (the first stopped at the root).
    assert_eq!(tree.opened(&here, 0).unwrap()[0].betas[0], Rat::one());
}

/// **Decision 28's tree is the case "found at the first arrival"** (Lean
/// `HNN/ConvergenceFounding.first_arrival_is_decision_28`): declaring the first arrival is the tree
/// `Landmarks::new` declares, exactly; the second arrival reads a different face once a context
/// meets its first arrival; the law is declared before any arrival and never under the node-local
/// law.
#[test]
fn landmark_first_arrival_founding_is_decision_28() {
    let declared = declaration(4, 3);
    let stream: Vec<usize> = (0..40u64).map(|t| ((t * 5 + t / 3) % 4) as usize).collect();
    let mut first = Landmarks::new(declared.clone())
        .unwrap()
        .founded_at(Founding::FirstArrival)
        .unwrap();
    let mut plain = Landmarks::new(declared.clone()).unwrap();
    let mut second = converging(declared.clone());
    assert_eq!(plain.founding(), Founding::FirstArrival);
    assert_eq!(second.founding(), Founding::SecondArrival);
    let mut differs = false;
    for (position, &cell) in stream.iter().enumerate() {
        let here = address(&stream, position, 3);
        let reading = first.receive(&here, cell).unwrap();
        assert_eq!(reading, plain.receive(&here, cell).unwrap());
        differs |= reading.executed != second.receive(&here, cell).unwrap().executed;
    }
    assert_eq!(first, plain);
    assert_eq!(first.pending(), 0);
    assert!(differs);
    assert!(second.nodes() < first.nodes());
    assert!(matches!(
        plain.clone().founded_at(Founding::SecondArrival),
        Err(HnnError::Shape { .. })
    ));
    let local = Landmarks::local(declared.clone(), LocalLaw::new(2).unwrap()).unwrap();
    assert!(local.clone().founded_at(Founding::FirstArrival).is_ok());
    assert!(matches!(
        local.founded_at(Founding::SecondArrival),
        Err(HnnError::Shape { .. })
    ));
    let oracle = IdealLandmarks::local(declared, None, LocalLaw::new(2).unwrap()).unwrap();
    assert!(oracle.founded_at(Founding::SecondArrival).is_err());
}

/// **The executed convergence-founded faces are normalized exactly and certified** over five
/// classes (so a digit is forced) with and without a forced depth (the first-arrival reach), under
/// two stop priors: each face sums to 1, each class is positive and equals the one-class read, each
/// cell's certificate lies within the rule and holds against the oracle.
#[test]
fn landmark_convergence_faces_are_normalized_and_certified() {
    let alphabet = 5;
    let stream: Vec<usize> = (0..70u64).map(|t| ((t * 7 + t / 3) % 5) as usize).collect();
    let laws = [StopPrior::half(), StopPrior::per_depth(vec![1, 3]).unwrap()];
    for (forced, prior) in [0, 1]
        .into_iter()
        .flat_map(|f| laws.clone().map(|p| (f, p)))
    {
        let declared = LandmarkDeclaration {
            forced,
            prior,
            population: 70,
            ..declaration(alphabet, 3)
        };
        let mut tree = converging(declared.clone());
        let mut oracle = converging_oracle(declared);
        for (position, &cell) in stream.iter().enumerate() {
            let here = address(&stream, position, 3);
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
            }
            let reading = tree.receive(&here, cell).unwrap();
            let ideal = oracle.receive(&here, cell).unwrap();
            assert!(reading.residual <= tree.face_rule());
            assert!(within(&reading.executed, &ideal, &reading.residual));
        }
        assert!(tree.pending() > 0);
    }
}

/// **The stopped path's lattice law, recomputed in ℚ** (Lean
/// `HNN/ConvergenceFounding.{stopped_face_normalized, conv_ratio_step}`): on every opened path the
/// stop reads its own face alone (a founded node's `⟦k⟧`, an opened pending node's KT face of its
/// one count, or the prior `½` within the first-arrival reach), each depth above it mixes by
/// `⟦λ̂ k + (1 − λ̂) q̂'⟧`; after the deposit each mixing node's `β` steps by `k/q̂'` (or its rebase)
/// and a founded node where the read stopped keeps its `β`.
#[test]
fn landmark_convergence_lattice_faces_follow_the_law() {
    let stream: Vec<usize> = (0..80u64).map(|t| ((t * t + t / 4) % 4) as usize).collect();
    for (forced, prior) in [
        (0, StopPrior::half()),
        (1, StopPrior::per_depth(vec![1, 4]).unwrap()),
    ] {
        let mut tree = Landmarks::with_carrier(
            LandmarkDeclaration {
                forced,
                prior: prior.clone(),
                population: 80,
                ..declaration(4, 3)
            },
            12,
        )
        .unwrap()
        .founded_at(Founding::SecondArrival)
        .unwrap();
        let scale = Rat::from_integer(BigInt::one() << tree.face_bits() as usize);
        let lattice = |x: &Rat| {
            let rounded = (x * &scale + rat(1, 2)).floor();
            rounded.max(Rat::one()).min(&scale - Rat::one()) / &scale
        };
        let rebase = rat(1, 1 << 11);
        let (mut stops, mut opens) = (0, 0);
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
                    }
                    if top + 1 == path.founded {
                        // The path stops at a founded node: its KT face alone.
                        assert_eq!(zero(&path.faces[top]), lattice(&zero(&path.masses[top])));
                        stops += usize::from(top < 3);
                    } else if top > forced.max(0) || (top == 0 && path.founded == 0 && forced == 0)
                    {
                        // An opened pending node (3/4 or 1/4 of its digit), or the root's prior.
                        let q = &path.faces[top];
                        assert!(q == &rat(1, 2) || q == &rat(3, 4) || q == &rat(1, 4));
                        opens += usize::from(q != &rat(1, 2));
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
                let top = old.faces.len() - 1;
                for d in forced..old.founded.min(top) {
                    let stepped = &old.betas[d] * &old.masses[d] / &old.faces[d + 1];
                    let ratio = &new.betas[d] / &stepped;
                    assert!(ratio <= Rat::one() && ratio > Rat::one() - &rebase);
                }
                if top + 1 == old.founded && top < 3 {
                    assert_eq!(new.betas[top], old.betas[top], "the stop keeps its β");
                }
                for d in old.founded..new.founded {
                    assert_eq!(
                        new.betas[d],
                        Rat::from_integer(BigInt::from(prior.founding(d)))
                    );
                }
            }
        }
        assert!(stops > 0 && opens > 0, "the passage stopped and opened");
    }
}

/// **The memory bounds no depth** (Decision 36, `Founding`'s a-priori size): over a passage of `n`
/// cells the convergence-founded tree founds at most `n B + 2^B − 1` nodes and holds at most `n B`
/// pending first arrivals at every depth, while the first-arrival tree's founded nodes grow with the
/// depth past that bound.
#[test]
fn landmark_convergence_memory_is_bounded_at_every_depth() {
    let stream: Vec<usize> = (0..400u64)
        .map(|t| ((t * 13 + t / 7 + t * t / 29) % 4) as usize)
        .collect();
    let (n, digits) = (stream.len(), 2usize);
    let bound = n * digits + (1 << digits) - 1;
    for depth in [2, 8, 24] {
        let declared = LandmarkDeclaration {
            population: 400,
            ..declaration(4, depth)
        };
        let mut tree = converging(declared.clone());
        let mut first = Landmarks::new(declared).unwrap();
        for (position, &cell) in stream.iter().enumerate() {
            let here = address(&stream, position, depth);
            tree.receive(&here, cell).unwrap();
            first.receive(&here, cell).unwrap();
        }
        assert!(tree.nodes() <= bound, "D = {depth}");
        assert!(tree.pending() <= n * digits, "D = {depth}");
        if depth == 24 {
            assert!(first.nodes() > bound);
        }
    }
}

/// **A window's faces in cell order under the convergence founding** (the working overlay records
/// and opens pending arrivals as the tree does): each phase reads the face of a clone into which
/// the earlier phases were deposited, exactly.
#[test]
fn landmark_convergence_window_faces_read_each_phase_after_the_earlier_deposits() {
    let stream: Vec<usize> = (0..90u64)
        .map(|t| ((t * 7 + t / 3 + t * t / 11) % 5) as usize)
        .collect();
    let declared = LandmarkDeclaration {
        population: 90,
        ..declaration(5, 3)
    };
    let mut tree = Landmarks::with_carrier(declared, 6)
        .unwrap()
        .founded_at(Founding::SecondArrival)
        .unwrap();
    let aperture = 3;
    for start in (0..stream.len()).step_by(aperture) {
        let window = start..(start + aperture).min(stream.len());
        let addresses: Vec<Vec<Letter>> = window
            .clone()
            .map(|position| address(&stream, position, 3))
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
        tree = deposited;
    }
    assert!(tree.pending() > 0);
}

/// **The prequential measurement and the depth sweep under a founding law**: the founded pass's
/// sums enclose the replay's faces and report the founding, its nodes and pending records; the
/// founded sweep reads the development cells only and charges `⌈log₂⌉` of the depths tried.
#[test]
fn landmark_convergence_prequential_partitions_the_cut() {
    let cells: Vec<usize> = (0..60u64).map(|t| ((t * 3 + t / 5) % 4) as usize).collect();
    let tail = 45..60;
    let cut = Cut {
        cells: cells.clone(),
        held_out: vec![tail],
    };
    let declared = declaration(4, 3);
    let letters = cell_letters(&cut.cells);
    let ([development, held], run) =
        tree_prequential_founded(&cut, &letters, &declared, Founding::SecondArrival).unwrap();
    let mut tree = converging(declared.clone());
    let mut products = [Rat::one(), Rat::one()];
    for (position, &cell) in cells.iter().enumerate() {
        let reading = tree.receive(&address(&cells, position, 3), cell).unwrap();
        products[usize::from(position >= 45)] *= &reading.executed;
    }
    for (coded, product) in [(&development, &products[0]), (&held, &products[1])] {
        let whole = code_length(product).unwrap();
        assert!(coded.lower <= whole.upper && whole.lower <= coded.upper);
    }
    assert_eq!(run.founding, Founding::SecondArrival);
    assert_eq!((run.nodes, run.pending), (tree.nodes(), tree.pending()));
    assert_eq!(run.bits, tree.bits());
    let sweep =
        choose_depth_founded(&cut, &letters, &declared, 6, Founding::SecondArrival).unwrap();
    let mut other = cut.clone();
    for cell in &mut other.cells[45..] {
        *cell = 3 - *cell;
    }
    assert_eq!(
        choose_depth_founded(
            &other,
            &cell_letters(&other.cells),
            &declared,
            6,
            Founding::SecondArrival
        )
        .unwrap(),
        sweep
    );
    assert!(sweep.tried.len() <= 6);
    assert_eq!(
        choose_depth_founded(&cut, &letters, &declared, 6, Founding::FirstArrival).unwrap(),
        crate::hnn::landmark::choose_depth_within(&cut, &letters, &declared, 6).unwrap()
    );
}
