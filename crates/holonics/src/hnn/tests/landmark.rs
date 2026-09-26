//! The landmark tree (Decision 28, count-only): the Willems–Shtarkov–Tjalkens fixture and the
//! sequential path law against the block recursion; Decision 27's parity at depth one with the
//! root's split forced; the faces' exact normalization under both emissions (a chart of five
//! classes, so the odometer digits prune); the opened path's telescope; the β chart's rebase and
//! its reported bound; the declared widths; the refusals; and the prequential measurement's parity
//! with the order-0 and order-1 baselines.

use num_bigint::BigInt;
use num_traits::{One, Zero};

use crate::hnn::HnnError;
use crate::hnn::landmark::{
    Beta, Emission, LandmarkDeclaration, Landmarks, Letter, address, carrier_width, choose_depth,
    face_bits, prequential,
};
use crate::hnn::masses::{ClassMasses, MassStep, Regions};
use crate::hnn::reference::Cut;
use crate::ratio::{Rat, integer, rat};

fn declaration(alphabet: usize, depth: usize, emission: Emission) -> LandmarkDeclaration {
    LandmarkDeclaration {
        alphabet,
        depth,
        emission,
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

/// Pass a binary stream's cells after its `past` through a tree; the product of the ideal faces.
fn pass(tree: &mut Landmarks, stream: &[usize], past: usize) -> Rat {
    let depth = tree.declaration().depth;
    (past..stream.len())
        .map(|t| {
            tree.receive(&address(stream, t, depth), stream[t])
                .unwrap()
                .ideal
        })
        .product()
}

/// **The Willems–Shtarkov–Tjalkens fixture** (the 1995 paper's weighted context tree): binary,
/// `D = 3`, the source `x_1^7 = 0110100` after the past `x_(−2) x_(−1) x_0 = 0 1 0`, weighted
/// probability `95/32768` exactly, under both emissions, with no rebase. The brief quoted the
/// source `0100110` after the past `110`; under no reading of which past bit is `x_0` (either order
/// of the past, either order of the source) does that pair give `95/32768` (it gives `7/2048`,
/// `55/16384`, `31/8192` or `3/1024`), and an exhaustive search of all 7-bit sources and 3-bit
/// pasts finds `0110100` after `010` among the 14 pairs that do: the paper's figure. The brief's
/// pair is kept as a second check against the block recursion, `7/2048` in the paper's convention.
#[test]
fn landmark_tree_reproduces_the_willems_shtarkov_tjalkens_fixture() {
    let paper = [0, 1, 0, 0, 1, 1, 0, 1, 0, 0];
    let brief = [1, 1, 0, 0, 1, 0, 0, 1, 1, 0];
    for emission in [Emission::Cell, Emission::Digits] {
        let fixture = LandmarkDeclaration {
            population: 7,
            ..declaration(2, 3, emission)
        };
        let mut tree = Landmarks::new(fixture.clone()).unwrap();
        assert_eq!(pass(&mut tree, &paper, 3), rat(95, 32768));
        assert_eq!(tree.chart().rebases, 0);
        assert_eq!(tree.chart().width, 10);
        let mut tree = Landmarks::new(fixture).unwrap();
        assert_eq!(pass(&mut tree, &brief, 3), rat(7, 2048));
        assert_eq!(block_weight(&brief, 3, &[], 3), rat(7, 2048));
        assert_eq!(block_weight(&paper, 3, &[], 3), rat(95, 32768));
    }
}

/// **The sequential path law is the block recursion** on a longer binary stream at every depth up
/// to 4: the product of the executed (`Cell`) faces is `W_root` exactly. The declared population
/// `2^40` widens the carrier to `W = 48`, so no rebase occurs over these 24 cells and the carried β
/// is the ideal one.
#[test]
fn landmark_path_law_is_the_block_recursion() {
    let stream: Vec<usize> = (0..24u64)
        .map(|t| usize::from((t * t + 3 * t) % 7 < 3))
        .collect();
    for depth in 0..=4 {
        let mut tree = Landmarks::new(LandmarkDeclaration {
            population: 1 << 40,
            ..declaration(2, depth, Emission::Cell)
        })
        .unwrap();
        assert_eq!(tree.chart().width, 48);
        let past = depth;
        let executed: Rat = (past..stream.len())
            .map(|t| {
                tree.receive(&address(&stream, t, depth), stream[t])
                    .unwrap()
                    .executed
            })
            .product();
        assert_eq!(tree.chart().rebases, 0);
        assert_eq!(executed, block_weight(&stream, past, &[], depth));
    }
}

/// **Decision 27's parity** (Lean `HNN/LandmarkTree.depth_one_is_decision_27`): `Cell`, depth 1,
/// the root's split forced (`λ_0 = 0`): at every step and
/// every class the face is `ClassMasses::probability` at the preceding-cell region exactly, the
/// stream's first cell in the empty-window region (the boundary letter).
#[test]
fn landmark_depth_one_forced_is_the_region_class_masses() {
    let alphabet = 3;
    let stream = [0usize, 2, 1, 1, 0, 2, 2, 1, 0, 0, 1, 2, 2, 2, 0];
    let mut tree = Landmarks::new(LandmarkDeclaration {
        forced: 1,
        ..declaration(alphabet, 1, Emission::Cell)
    })
    .unwrap();
    let mut masses = ClassMasses::prior(Regions::PrecedingCell, alphabet);
    for (position, &cell) in stream.iter().enumerate() {
        let window: Vec<Option<usize>> = position
            .checked_sub(1)
            .map(|previous| vec![Some(stream[previous])])
            .unwrap_or_default();
        let region = Regions::PrecedingCell.region(&window, alphabet).unwrap();
        let here = address(&stream, position, 1);
        assert_eq!(here[0].code() as usize, region);
        for class in 0..alphabet {
            assert_eq!(
                tree.probability(&here, class).unwrap(),
                masses.probability(region, class).unwrap()
            );
        }
        let reading = tree.receive(&here, cell).unwrap();
        assert_eq!(reading.executed, masses.probability(region, cell).unwrap());
        masses
            .deposit(&MassStep {
                ring: 0,
                region,
                class: cell,
                weight: integer(1),
            })
            .unwrap();
    }
}

/// **The faces are normalized exactly** (Lean `HNN/LandmarkTree.{path_face_normalized,
/// cell_faces_partition, forced_digits_normalized, digit_log_residual}`) at every step of a short
/// stream, under both emissions, over
/// five classes (so the odometer's third digit is forced where the upper half is empty): the
/// executed face sums to 1, the ideal face sums to 1, each class's face is the one-class read, the
/// grain exponents bracket each face, and each cell's certified residual lies within the rule's
/// a-priori bound, itself below one grain.
#[test]
fn landmark_faces_are_normalized_under_both_emissions() {
    let alphabet = 5;
    let stream: Vec<usize> = (0..30u64).map(|t| ((t * 7 + t / 3) % 5) as usize).collect();
    for emission in [Emission::Digits, Emission::Cell] {
        let mut tree = Landmarks::new(declaration(alphabet, 2, emission)).unwrap();
        assert!(tree.face_rule() < rat(1, 16));
        for (position, &cell) in stream.iter().enumerate() {
            let here = address(&stream, position, 2);
            let face = tree.face(&here, 16).unwrap();
            let sum: Rat = face.probabilities.iter().cloned().sum();
            assert_eq!(sum, Rat::one());
            let ideal: Rat = (0..alphabet)
                .map(|class| tree.ideal_probability(&here, class).unwrap())
                .sum();
            assert_eq!(ideal, Rat::one());
            for class in 0..alphabet {
                let p = &face.probabilities[class];
                assert!(p > &Rat::zero());
                assert_eq!(p, &tree.probability(&here, class).unwrap());
                let k = &face.exponents[class];
                let power = (0..16).fold(Rat::one(), |acc, _| acc * p);
                let two = |k: &BigInt| {
                    let shift = usize::try_from(k.magnitude().clone()).unwrap();
                    let value = Rat::from_integer(BigInt::one() << shift);
                    if k.sign() == num_bigint::Sign::Minus {
                        value.recip()
                    } else {
                        value
                    }
                };
                assert!(two(k) <= power && power < two(&(k + 1)));
            }
            let reading = tree.receive(&here, cell).unwrap();
            assert!(reading.residual <= tree.face_rule());
            if emission == Emission::Cell {
                assert_eq!(reading.executed, reading.ideal);
            } else {
                // The executed face is a dyadic of at most B · M_f bits.
                let bits = tree.digits() * tree.face_bits();
                assert!(reading.executed.denom() <= &(BigInt::one() << bits as usize));
            }
        }
    }
}

/// **The telescope** on an opened path (Lean `HNN/LandmarkTree.path_telescope_exact`):
/// `q_0 = q_D · Π_(d<D) q_d/q_(d+1)`, and the edge ratios'
/// product carries `q_0` to `q_D`, on every tree a class opens, at every founded extent.
#[test]
fn landmark_opened_path_telescopes() {
    let stream: Vec<usize> = (0..24u64).map(|t| ((t * 5 + 1) % 4) as usize).collect();
    for emission in [Emission::Digits, Emission::Cell] {
        let mut tree = Landmarks::new(declaration(4, 3, emission)).unwrap();
        for (position, &cell) in stream.iter().enumerate() {
            let here = address(&stream, position, 3);
            for class in 0..4 {
                for path in tree.opened(&here, class).unwrap() {
                    let depth = path.faces.len() - 1;
                    let product: Rat = (0..depth)
                        .map(|d| &path.faces[d] / &path.faces[d + 1])
                        .product();
                    assert_eq!(path.faces[0], &path.faces[depth] * product);
                    let edges: Rat = path.edge_ratios().into_iter().product();
                    assert_eq!(&path.faces[0] * edges, path.faces[depth]);
                }
            }
            tree.receive(&here, cell).unwrap();
        }
        let founded = tree
            .opened(&address(&stream, stream.len(), 3), stream[0])
            .unwrap();
        assert!(founded.iter().any(|path| path.founded == 4));
    }
}

/// **The β chart rebases** at a declared width of 4 bits: rebases are reported with the summed
/// bound `rebases · 2^(3−W)`, the most-rebased node's bound likewise, each rebase's relative
/// residual lies in `[0, 2^(1−W))`, and the executed face stays exactly normalized.
#[test]
fn landmark_chart_rebases_with_its_reported_bound() {
    let width = 4u64;
    let (carried, rebased) = Beta::carried(&rat(1000, 7), width);
    assert!(rebased);
    let value = rat(1000, 7);
    let residual = (&value - carried.value()) / &value;
    assert!(residual >= Rat::zero() && residual < rat(1, 8));
    let (exact, rebased) = Beta::carried(&rat(96, 5), width);
    assert!(!rebased);
    assert_eq!(exact.value(), rat(96, 5));

    let stream: Vec<usize> = (0..60u64).map(|t| ((t * t) % 3) as usize).collect();
    for emission in [Emission::Digits, Emission::Cell] {
        let mut tree = Landmarks::with_width(declaration(3, 2, emission), width).unwrap();
        for (position, &cell) in stream.iter().enumerate() {
            tree.receive(&address(&stream, position, 2), cell).unwrap();
        }
        let chart = tree.chart();
        assert!(chart.rebases > 0);
        assert!(chart.node_rebases > 0 && chart.node_rebases <= chart.rebases);
        let unit = rat(1, 2); // 2^(3−4)
        assert_eq!(
            chart.residual_bound,
            Rat::from_integer(BigInt::from(chart.rebases)) * &unit
        );
        assert_eq!(
            chart.node_bound,
            Rat::from_integer(BigInt::from(chart.node_rebases)) * &unit
        );
        let face = tree.face(&address(&stream, stream.len(), 2), 16).unwrap();
        let sum: Rat = face.probabilities.into_iter().sum();
        assert_eq!(sum, Rat::one());
    }
}

/// **The declared widths** at the standing real cut's scope: `W = 20` (`2^19 ≤ 8·16·6,148 < 2^20`)
/// and `M_f = 14 + 7 + 2 = 23`; the rule's residual per cell, `B · ε/(μ − ε) · 3/2`, stays within
/// `log₂ e/(4 L_R) < (3/2)/(4 L_R)` and so below one grain (Lean `digit_log_residual_kt`).
#[test]
fn landmark_widths_follow_the_passage_and_the_grain() {
    assert_eq!(carrier_width(6_148, 16), 20);
    assert_eq!(face_bits(6_148, 8, 16), 23);
    let tree = Landmarks::new(LandmarkDeclaration {
        population: 6_148,
        ..declaration(256, 3, Emission::Digits)
    })
    .unwrap();
    assert_eq!(tree.chart().width, 20);
    assert_eq!(tree.face_bits(), 23);
    assert!(tree.face_rule() < rat(1, 16));
    assert!(tree.face_rule() <= rat(3, 2 * 4 * 16));
}

/// **The refusals**: an address of the wrong depth, a class or letter outside the chart, a forced
/// depth past the address, and a passage past the declared population, each before anything moves.
#[test]
fn landmark_refusals() {
    let mut tree = Landmarks::new(LandmarkDeclaration {
        population: 2,
        ..declaration(3, 1, Emission::Cell)
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
    assert_eq!(
        tree.receive(&[Letter::Cell(1)], 2),
        Err(HnnError::PopulationReached { population: 2 })
    );
    assert!(
        Landmarks::new(LandmarkDeclaration {
            forced: 2,
            ..declaration(3, 1, Emission::Cell)
        })
        .is_err()
    );
}

/// **The prequential measurement is symmetric with the baselines**: a `Cell` tree of depth 1 with
/// its root forced is online order-1 KT and one of depth 0 is online order-0 KT, so their code
/// lengths equal the baselines' exactly on both populations; the held-out cells are scored at the
/// standing before their deposit, and deposited, like the baselines'. The depth sweep reads the
/// development cells only.
#[test]
fn landmark_prequential_matches_the_baselines_at_their_orders() {
    let cells: Vec<usize> = (0..48u64).map(|t| ((t * 3 + t / 5) % 4) as usize).collect();
    let tail = 36..48;
    let cut = Cut {
        cells: cells.clone(),
        held_out: vec![tail],
    };
    let digits = declaration(4, 2, Emission::Digits);
    let order_one = LandmarkDeclaration {
        forced: 1,
        ..declaration(4, 1, Emission::Cell)
    };
    let run = prequential(&cut, &digits, &order_one).unwrap();
    assert_eq!(run.development.cells, 36);
    assert_eq!(run.held_out.cells, 12);
    assert_eq!(run.development.cell, run.development.order_one);
    assert_eq!(run.held_out.cell, run.held_out.order_one);
    let order_zero = declaration(4, 0, Emission::Cell);
    let run = prequential(&cut, &digits, &order_zero).unwrap();
    assert_eq!(run.development.cell, run.development.order_zero);
    assert_eq!(run.held_out.cell, run.held_out.order_zero);

    // Changing the held-out cells changes no development reading of the sweep.
    let sweep = choose_depth(&cut, &digits).unwrap();
    let mut other = cut.clone();
    for cell in &mut other.cells[36..] {
        *cell = 3 - *cell;
    }
    assert_eq!(choose_depth(&other, &digits).unwrap(), sweep);
    assert!(sweep.tried.len() >= 2);
    assert_eq!(
        sweep.description_bits,
        crate::compression::cost::ceil_log2(&num_bigint::BigUint::from(sweep.tried.len()))
    );
}

/// **The wide-face reading** ([`code_length`]): a face within `G` bits reads exactly as
/// `log2_enclosure`; a face of hundreds of bits reads within an enclosure that meets the direct
/// series' enclosure (both hold `−log₂ q`), no wider than it by more than the certified widening
/// and the grid.
#[test]
fn landmark_wide_faces_read_within_their_certified_widening() {
    use crate::hnn::landmark::{code_length, reading_bits};
    use crate::hnn::ratio::log2_enclosure;
    let narrow = rat(1537, 12298);
    assert_eq!(
        code_length(&narrow).unwrap(),
        log2_enclosure(&narrow.recip()).unwrap()
    );
    assert_eq!(reading_bits(), 98);
    let wide = Rat::new(
        (BigInt::one() << 300usize) + BigInt::from(12_345),
        (BigInt::one() << 305usize) - BigInt::from(977),
    );
    let read = code_length(&wide).unwrap();
    let direct = log2_enclosure(&wide.recip()).unwrap();
    assert!(read.lower <= direct.upper && direct.lower <= read.upper);
    let slack = rat(1, 1 << 30) * rat(1, 1 << 30) * rat(1, 1 << 30);
    assert!(&read.upper - &read.lower <= &direct.upper - &direct.lower + slack);
}
