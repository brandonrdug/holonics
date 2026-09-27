//! The Born receiver (the Born face; Lean `HNN/BornFace`): the derived widths and their refusals;
//! the opening split, exactly uniform at every state; the executed cell faces, an exact dyadic
//! partition (a chart of five classes, so digits are forced); the floored interference zero beside
//! the nonnegative receiver's positive mass; the tick absorbed by the first digit's operators; the
//! Gram's carry against its exact statistic; the first deposit against the exact prox step in
//! `ℚ(i)`; the solve's certificate; read-then-deposit against receive; and the register carrying
//! context (an alternation coded below the one-dimensional register).

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use crate::compression::landmark::context::code_length;
use crate::hnn::HnnError;
use crate::hnn::born::{Born, BornDeclaration, BornWidths, Emission, Word, born_split};
use crate::ratio::Rat;
use crate::ratio::gaussian::GaussianRat;

fn declaration(alphabet: usize, width: usize, emission: Emission) -> BornDeclaration {
    BornDeclaration {
        alphabet,
        width,
        emission,
        population: 512,
        grain: 16,
    }
}

fn two_power(exponent: i64) -> Rat {
    if exponent >= 0 {
        Rat::from_integer(BigInt::one() << exponent as usize)
    } else {
        Rat::new(BigInt::one(), BigInt::one() << (-exponent) as usize)
    }
}

fn gaussian(word: Word, exponent: i64) -> GaussianRat {
    GaussianRat::new(
        Rat::from_integer(word.0.into()),
        Rat::from_integer(word.1.into()),
    )
    .scale(&two_power(-exponent))
}

fn modulus_bound(z: &GaussianRat) -> Rat {
    z.re.abs().max(z.im.abs())
}

#[test]
fn born_widths_are_derived_from_the_declaration() {
    let standing = BornDeclaration {
        alphabet: 256,
        width: 128,
        emission: Emission::Dyadic,
        population: 6148,
        grain: 16,
    };
    let widths = BornWidths::derived(&standing).expect("the standing cut's declaration");
    // 2^M ≥ 3 B L_R (2n* + 2) = 3·8·16·12298 = 4,722,432: M = 23, as the tree's digit face.
    assert_eq!(widths.face, 23);
    assert_eq!(widths.digits, 8);
    assert_eq!(widths.order, 7);
    assert_eq!(widths.state, 23 + 3 + 4);
    assert_eq!(widths.operator, 23 + 3 + 7);
    // ⌈log₂(2 L_R χ)⌉ = ⌈log₂ 4096⌉.
    assert_eq!(widths.gram, 12);
    assert_eq!(widths.chart, 23 + 4 + 7);
    assert_eq!(widths.solve, 34 + 7 + 3);
    let three = BornDeclaration {
        width: 3,
        ..standing
    };
    assert!(matches!(
        BornWidths::derived(&three),
        Err(HnnError::Shape { .. })
    ));
}

#[test]
fn born_opening_split_is_exactly_uniform_at_every_state() {
    for (width, emission) in [
        (1, Emission::Dyadic),
        (4, Emission::Position),
        (8, Emission::Dyadic),
    ] {
        let mut born = Born::new(declaration(256, width, emission)).expect("a declaration");
        let face_bits = born.widths().face;
        for class in [0usize, 97, 255, 13, 200] {
            // Read without depositing: every locus stays at its opening, the state moves.
            let reception = born.read(class).expect("a reception");
            for digit in &reception.digits {
                assert_eq!(digit.numerator, 1 << (face_bits - 1));
            }
            assert_eq!(reception.face, Rat::new(BigInt::one(), BigInt::from(256)));
        }
    }
}

#[test]
fn born_cell_faces_are_an_exact_dyadic_partition() {
    for (alphabet, emission) in [
        (5, Emission::Dyadic),
        (5, Emission::Position),
        (256, Emission::Dyadic),
    ] {
        let mut born = Born::new(declaration(alphabet, 2, emission)).expect("a declaration");
        let stream: Vec<usize> = (0..24).map(|i| (i * 7 + i / 3) % alphabet).collect();
        for &class in &stream {
            born.receive(class).expect("a cell");
        }
        let total: Rat = (0..alphabet).map(|c| born.face(c).expect("a face")).sum();
        assert_eq!(total, Rat::one());
        for c in 0..alphabet {
            assert!(born.face(c).expect("a face").is_positive());
        }
    }
}

#[test]
fn born_interference_zero_is_floored_where_a_nonnegative_receiver_stays_positive() {
    // Lean `born_interference_zero`: A₁ = [[1, 0], [0, 0]], A₂ = [[0, −1], [0, 0]] at the state
    // (1, 1): each alone has mass, their sum cancels.
    let unit = 1i64 << 20;
    let state: Vec<Word> = vec![(1 << 29, 0), (1 << 29, 0)];
    let left: Vec<Word> = vec![(unit, 0), (0, 0), (0, 0), (0, 0)];
    let right: Vec<Word> = vec![(0, 0), (-unit, 0), (0, 0), (0, 0)];
    let sum: Vec<Word> = vec![(unit, 0), (-unit, 0), (0, 0), (0, 0)];
    let other: Vec<Word> = vec![(unit, 0), (0, 0), (0, 0), (unit, 0)];
    let (face_bits, state_bits) = (23, 30);
    for alone in [&left, &right] {
        let split = born_split([alone, &other], &state, face_bits, state_bits).expect("a split");
        assert!(split.traces[0] > 0);
    }
    let split = born_split([&sum, &other], &state, face_bits, state_bits).expect("a split");
    assert_eq!(split.traces[0], 0);
    // The executed face floors the shadow at 2^(−M): a digit costs at most M bits.
    assert_eq!(split.numerator, 1);
    assert_eq!(
        split.face(0, face_bits),
        Rat::new(BigInt::one(), BigInt::one() << face_bits as usize)
    );
    // The nonnegative receiver of the same width (Lean `hmm_mass_add`, `hmm_mass_pos`): the
    // entries' moduli at the state's diagonal (½, ½); masses add, so the sum's mass is the two
    // positive masses' sum and never zero.
    let half = Rat::new(BigInt::one(), BigInt::from(2));
    let mass = |m: &[Word]| -> Rat {
        m.iter()
            .map(|&(re, im)| Rat::from_integer(BigInt::from(re.abs() + im.abs())) * &half)
            .sum()
    };
    let moduli: Vec<Word> = left
        .iter()
        .zip(&right)
        .map(|(a, b)| (a.0.abs() + b.0.abs(), a.1.abs() + b.1.abs()))
        .collect();
    assert!(mass(&left).is_positive() && mass(&right).is_positive());
    assert_eq!(mass(&moduli), mass(&left) + mass(&right));
}

/// `M·U/2^shift` of word matrices, asserted exact.
fn times(a: &[Word], u: &[Word], n: usize, shift: u32) -> Vec<Word> {
    let mut out = vec![(0i64, 0i64); n * n];
    for i in 0..n {
        for l in 0..n {
            let (mut re, mut im) = (0i128, 0i128);
            for m in 0..n {
                let (a, b) = (a[i * n + m], u[m * n + l]);
                re += i128::from(a.0) * i128::from(b.0) - i128::from(a.1) * i128::from(b.1);
                im += i128::from(a.0) * i128::from(b.1) + i128::from(a.1) * i128::from(b.0);
            }
            assert_eq!(re % (1 << shift), 0);
            assert_eq!(im % (1 << shift), 0);
            out[i * n + l] = ((re >> shift) as i64, (im >> shift) as i64);
        }
    }
    out
}

#[test]
fn born_tick_is_absorbed_by_the_first_digits_operators() {
    // Lean `born_tick_absorbed`: Tr(A UρU† A†) = Tr((AU)ρ(AU)†). U = W₄/2, the Walsh–Hadamard
    // unitary, exact on the dyadics.
    let n: usize = 4;
    let walsh: Vec<Word> = (0..n * n)
        .map(|index| {
            let (k, l) = (index / n, index % n);
            (if (k & l).count_ones() % 2 == 0 { 1 } else { -1 }, 0)
        })
        .collect();
    let mut born = Born::new(declaration(256, n, Emission::Dyadic)).expect("a declaration");
    for class in [97usize, 98, 97, 32, 101] {
        born.receive(class).expect("a cell");
    }
    let operators = born.opening(1);
    let learned = born.locus(1).expect("the root cell is founded");
    let pair = [learned.operators[0].to_vec(), learned.operators[1].to_vec()];
    for operators in [operators, pair] {
        let state: Vec<Word> = vec![
            (6 << 20, 2 << 20),
            (-(4 << 20), 0),
            (2 << 20, 8 << 20),
            (0, -(2 << 20)),
        ];
        // Uψ = W₄ψ/2, exact.
        let ticked: Vec<Word> = (0..n)
            .map(|k| {
                (0..n).fold((0i64, 0i64), |sum, l| {
                    let w = walsh[k * n + l].0;
                    (sum.0 + w * state[l].0 / 2, sum.1 + w * state[l].1 / 2)
                })
            })
            .collect();
        // (AU)ψ = (A W₄)(ψ/2), exact.
        let absorbed = [
            times(&operators[0], &walsh, n, 0),
            times(&operators[1], &walsh, n, 0),
        ];
        let halved: Vec<Word> = state.iter().map(|&(re, im)| (re / 2, im / 2)).collect();
        let direct = born_split([&operators[0], &operators[1]], &ticked, 23, 60).expect("a split");
        let moved = born_split([&absorbed[0], &absorbed[1]], &halved, 23, 60).expect("a split");
        assert_eq!(direct.amplitudes, moved.amplitudes);
        assert_eq!(direct.traces, moved.traces);
        assert_eq!(direct.numerator, moved.numerator);
    }
}

#[test]
fn born_gram_carries_its_exact_statistic_within_its_releases() {
    let mut born = Born::new(declaration(256, 4, Emission::Position)).expect("a declaration");
    let widths = born.widths();
    let n = 4;
    let mut exact = vec![GaussianRat::zero(); n * n];
    for k in 0..n {
        exact[k * n + k] = GaussianRat::one();
    }
    let mut releases = Rat::zero();
    let stream = [
        104usize, 101, 108, 108, 111, 32, 119, 111, 114, 108, 100, 33,
    ];
    for (step, &class) in stream.iter().enumerate() {
        let reception = born.read(class).expect("a reception");
        // Digit 0's locus is position 0: its feature is the state digit 0 read.
        let psi: Vec<GaussianRat> = reception.digits[0]
            .state
            .iter()
            .map(|&x| gaussian(x, 0))
            .collect();
        let norm: Rat = psi.iter().map(GaussianRat::norm_sq).sum();
        for i in 0..n {
            for l in 0..n {
                let term = psi[i].mul(&psi[l].conj()).scale(&norm.recip());
                exact[i * n + l] = exact[i * n + l].add(&term);
            }
        }
        born.deposit(reception).expect("a deposit");
        let view = born.locus(0).expect("founded");
        assert_eq!(view.clock, step as u64 + 1);
        releases += two_power(-(i64::from(widths.gram) + i64::from(view.precision) + 1));
        for (index, exact) in exact.iter().enumerate() {
            let carried = gaussian(view.gram[index], i64::from(widths.gram)).add(&gaussian(
                view.gram_remainder[index],
                i64::from(widths.gram + view.precision),
            ));
            let deviation = modulus_bound(&carried.sub(exact));
            assert!(deviation <= releases, "entry {index} at deposit {step}");
        }
        // Hermitian by construction.
        for i in 0..n {
            for l in 0..n {
                assert_eq!(view.gram[i * n + l].0, view.gram[l * n + i].0);
                assert_eq!(view.gram[i * n + l].1, -view.gram[l * n + i].1);
            }
        }
    }
    // Kraft for the gamma lengths: the releases since founding stay below half a unit.
    assert!(releases < two_power(-(i64::from(widths.gram) + 1)));
}

/// The exact inverse of a Hermitian 2×2 matrix `[[a, b], [b̄, d]]`.
fn inverse2(h: &[GaussianRat]) -> Vec<GaussianRat> {
    let det = h[0].mul(&h[3]).sub(&h[1].mul(&h[2]));
    let inv = det.inverse().expect("a positive definite Gram");
    vec![
        h[3].mul(&inv),
        h[1].neg().mul(&inv),
        h[2].neg().mul(&inv),
        h[0].mul(&inv),
    ]
}

#[test]
fn born_first_deposit_is_the_exact_prox_step_within_its_charts() {
    // χ = 2: A_c′ = A_c + ½(q_c/p̂_c − 1)(A_c ψ)(H′⁻¹ψ)†/‖ψ‖², H′ = I + ψψ†/‖ψ‖², in ℚ(i).
    let n = 2;
    let mut born = Born::new(declaration(256, n, Emission::Position)).expect("a declaration");
    let widths = born.widths();
    // Move the state off the opening ray first (position 0 is founded by this cell).
    born.receive(200).expect("a cell");
    let before = born
        .locus(1)
        .expect("founded")
        .operators
        .map(<[Word]>::to_vec);
    let reception = born.read(37).expect("a reception");
    let digit = reception.digits[1].clone();
    assert_eq!(digit.locus, 1);
    born.deposit(reception).expect("a deposit");
    let psi: Vec<GaussianRat> = digit.state.iter().map(|&x| gaussian(x, 0)).collect();
    let norm: Rat = psi.iter().map(GaussianRat::norm_sq).sum();
    // The Gram before this deposit, exact: I + ψ₀ψ₀†/‖ψ₀‖² for position 1's first reading.
    let view = born.locus(1).expect("founded");
    assert_eq!(view.clock, 2);
    let gram: Vec<GaussianRat> = (0..n * n)
        .map(|index| {
            gaussian(view.gram[index], i64::from(widths.gram)).add(&gaussian(
                view.gram_remainder[index],
                i64::from(widths.gram + view.precision),
            ))
        })
        .collect();
    let solve = inverse2(&gram);
    let v: Vec<GaussianRat> = (0..n)
        .map(|i| {
            (0..n).fold(GaussianRat::zero(), |sum, l| {
                sum.add(&solve[i * n + l].mul(&psi[l]))
            })
        })
        .collect();
    let scale_face = 1u64 << widths.face;
    let executed = [digit.numerator, scale_face - digit.numerator];
    for c in 0..2 {
        let a: Vec<GaussianRat> = (0..n)
            .map(|i| {
                (0..n).fold(GaussianRat::zero(), |sum, l| {
                    sum.add(
                        &gaussian(before[c][i * n + l], i64::from(widths.operator)).mul(&psi[l]),
                    )
                })
            })
            .collect();
        let coefficient = if c == digit.observed {
            Rat::new(executed[1 - c].into(), (2 * executed[c]).into()) / &norm
        } else {
            -Rat::new(BigInt::one(), BigInt::from(2)) / &norm
        };
        let mut largest = Rat::zero();
        let mut steps = Vec::new();
        for left in &a {
            for right in &v {
                let step = left.mul(&right.conj()).scale(&coefficient);
                largest = largest.max(modulus_bound(&step));
                steps.push(step);
            }
        }
        // Tolerance: three charts of relative 2^(1−C) each on the step's largest part (with its
        // cross terms, 4·2^(1−C)), plus the two carries' releases and the carried remainder.
        let tolerance =
            &largest * Rat::from_integer(BigInt::from(8)) * two_power(1 - i64::from(widths.chart))
                + two_power(-i64::from(widths.operator));
        for index in 0..n * n {
            let old = gaussian(before[c][index], i64::from(widths.operator));
            let new =
                gaussian(view.operators[c][index], i64::from(widths.operator)).add(&gaussian(
                    view.remainders[c][index],
                    i64::from(widths.operator + view.precision),
                ));
            let moved = new.sub(&old);
            let deviation = modulus_bound(&moved.sub(&steps[index]));
            assert!(deviation <= tolerance, "operator {c}, entry {index}");
        }
        assert!(largest.is_positive());
    }
}

#[test]
fn born_solve_is_certified_and_read_then_deposit_is_receive() {
    let mut born = Born::new(declaration(256, 8, Emission::Dyadic)).expect("a declaration");
    let mut twin = born.clone();
    let text = b"the quick brown fox jumps over the lazy dog, the quick brown fox again";
    for &byte in text.iter() {
        let face = born.receive(usize::from(byte)).expect("a cell");
        let reception = twin.read(usize::from(byte)).expect("a reception");
        assert_eq!(reception.face, face);
        twin.deposit(reception).expect("a deposit");
    }
    assert_eq!(born, twin);
    let report = born.report();
    assert_eq!(report.deposits, text.len() as u64);
    assert_eq!(report.locus_deposits, 8 * text.len() as u64);
    assert!(report.largest_certificate <= two_power(-i64::from(born.widths().chart)));
}

/// The code length of a stream's last `tail` cells, prequential, as the enclosure's upper end.
fn tail_bits(born: &mut Born, stream: &[usize], tail: usize) -> Rat {
    let mut bits = Rat::zero();
    for (position, &class) in stream.iter().enumerate() {
        let face = born.receive(class).expect("a cell");
        if position + tail >= stream.len() {
            bits += code_length(&face).expect("a code length").upper;
        }
    }
    bits
}

#[test]
fn born_register_carries_context_an_order_zero_face_cannot() {
    // An alternation of two classes: order-0 codes it at one bit a cell; a register of width 2
    // carries the last cell and codes below the one-dimensional register (an order-0 dyadic face).
    let stream: Vec<usize> = (0..400).map(|i| if i % 2 == 0 { 97 } else { 98 }).collect();
    let mut one = Born::new(declaration(256, 1, Emission::Dyadic)).expect("a declaration");
    let mut two = Born::new(declaration(256, 2, Emission::Dyadic)).expect("a declaration");
    let tail = 100;
    let (flat, carried) = (
        tail_bits(&mut one, &stream, tail),
        tail_bits(&mut two, &stream, tail),
    );
    assert!(flat > Rat::from_integer(BigInt::from(tail as i64 / 2)));
    assert!(carried < flat, "χ = 2 codes the alternation below χ = 1");
}

#[test]
fn born_refuses_outside_its_chart_and_at_a_vanished_image() {
    let mut born = Born::new(declaration(5, 2, Emission::Dyadic)).expect("a declaration");
    assert!(matches!(
        born.read(5),
        Err(HnnError::CellOutside {
            code: 5,
            alphabet: 5
        })
    ));
    let zero: Vec<Word> = vec![(0, 0); 4];
    let state: Vec<Word> = vec![(1, 0), (1, 0)];
    assert!(matches!(
        born_split([&zero, &zero], &state, 23, 30),
        Err(HnnError::BornZero { .. })
    ));
    assert!(born.face(4).expect("a face").is_positive());
}
