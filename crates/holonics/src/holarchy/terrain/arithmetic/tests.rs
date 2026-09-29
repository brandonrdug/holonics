//! Each truth of the arithmetic terrain checked exactly on hand-computed fixtures, each tied to the
//! Lean theorem of `Mathematics/RadixWindowReceiver` it realizes: multiplication as convolution
//! with carry (`111₂ × 11₂`, `FF₁₆ × FF₁₆`, the square of `(b−1)(b−1)`), a decimal record's cells,
//! classes, trailing face and leading fibre, drawn records in bases 2, 10 and 16, the "…17"
//! column's gratings, the cheap-face table for bases 2, 6, 10, 16 and 30, and a prime window's
//! emission and density read through a face.

use num_bigint::BigUint;
use num_traits::Zero;

use super::*;
use crate::holarchy::terrain::Draw;
use crate::ratio::primality::is_prime;
use crate::ratio::rat;
use crate::ratio::surprisal::SymbolicSurprisal;

/// `Σ_j w_j b^j` of a word's slice, for the carry invariant.
fn value_of(word: &[u64], base: u64) -> BigUint {
    horner(word, base)
}

/// Lean `digit_product_is_carry_of_convolution`, `carry_step_value` and
/// `carried_word_is_product_digits` (the record's §7.1). `111₂ × 11₂`: `[1,1,1] ∗ [1,1] = [1,2,2,1]`,
/// carried with the carries `[0,1,1,1,0]` to `10101₂ = 21 = 3·7`. `FF₁₆ × FF₁₆`:
/// `[F,F] ∗ [F,F] = [225, 450, 225]` (`225 = 3²·5²`), carried with `[14, 29, 15, 0]` to
/// `FE01₁₆ = 65025 = 3²·5²·17²`. After each place `j` the value is kept: the digits read so far plus
/// `b^(j+1)` times the carry and the unread convolution (`carry_step_value`, iterated). The square of
/// the two-digit `(b−1)(b−1)` reads `(b−1)(b−2)01` in every base (`(x² − 1)² = (x − 1)x³ +
/// (x − 2)x² + 1` at `x = b`), and each carried word is the product's digit word.
#[test]
fn multiplication_is_convolution_with_carry() {
    let binary = digit_product(2, &[1, 1, 1], &[1, 1]).unwrap();
    assert_eq!(binary.convolution, vec![1, 2, 2, 1]);
    assert_eq!(binary.carries, vec![0, 1, 1, 1, 0]);
    assert_eq!(binary.digits, vec![1, 0, 1, 0, 1]);
    assert_eq!(binary.convolution_value(), BigUint::from(21u32));
    assert_eq!(binary.value(), BigUint::from(21u32));
    let hex = digit_product(16, &[15, 15], &[15, 15]).unwrap();
    assert_eq!(hex.convolution, vec![225, 450, 225]);
    assert_eq!(hex.carries, vec![14, 29, 15, 0]);
    assert_eq!(hex.digits, vec![1, 0, 14, 15]);
    assert_eq!(hex.value(), BigUint::from(65025u32));
    assert_eq!(factorization(65025), Some(vec![(3, 2), (5, 2), (17, 2)]));
    for product in [&binary, &hex] {
        let whole = product.convolution_value();
        let radix = BigUint::from(product.base);
        for j in 0..product.digits.len() {
            let unread = product
                .convolution
                .get(j + 1..)
                .map_or_else(BigUint::zero, |tail| value_of(tail, product.base));
            let kept = value_of(&product.digits[..=j], product.base)
                + radix.pow(j as u32 + 1) * (BigUint::from(product.carries[j]) + unread);
            assert_eq!(kept, whole);
        }
    }
    for base in [2u64, 6, 10, 16, 30] {
        let square = digit_product(base, &[base - 1, base - 1], &[base - 1, base - 1]).unwrap();
        assert_eq!(square.digits, vec![1, 0, base - 2, base - 1]);
        let value = (base * base - 1).pow(2);
        assert_eq!(square.value(), BigUint::from(value));
        assert_eq!(
            square.digits,
            digits(value, base, digit_count(value, base)).unwrap()
        );
    }
    // A zero product's digit word is empty (Lean's `Nat.digits b 0 = []`); a base below two is
    // refused.
    assert!(digit_product(10, &[0, 0], &[3]).unwrap().digits.is_empty());
    assert!(digit_product(1, &[1], &[1]).is_err());
    assert!(digits(100, 10, 2).is_err());
}

fn decimal(order: DigitOrder) -> ProductFamily {
    ProductFamily {
        base: 10,
        digits: 4,
        face: 2,
        order,
    }
}

/// The record `0347 ⊗ 5102 = 01770394 ;` in base 10, `L = 4`, `k = 2`. The convolution of
/// `[7,4,3,0]` and `[2,0,1,5]` is `[14, 8, 13, 39, 23, 15, 0]` (value `1770394 = 2·347·2551`),
/// carried with `[1,0,1,4,2,1,0]` to `[4,9,3,0,7,7,1]`. The trailing face is `94 = 47·02 mod 100`
/// (Mathlib `Nat.mul_mod`). The operands' leading faces `03` and `51` confine the product to
/// `[3·51·10^4, 399·5199] = [1530000, 2074401]`, whose first two digits of eight read the fibre
/// `[01, 02]`; the product reads `01`. Least first, the product's cells are trailing, middle,
/// leading; most first, leading, middle, trailing. The family's alphabet is `13`, a record `19`
/// cells, its span `18`, its operand code `8 log₂ 10 = 8 + 8 log₂ 5` and its key description
/// `⌈log₂ 10^8⌉ = 27` bits (`2^26 < 10^8 < 2^27`).
#[test]
fn a_decimal_record_has_its_cells_classes_and_faces() {
    use ProductCell::{Leading, Mark, Middle, Operand, Trailing};
    let family = decimal(DigitOrder::LeastFirst);
    let products = Products::new(family.clone(), vec![(347, 5102)]).unwrap();
    assert_eq!(
        products.emit(),
        vec![7, 4, 3, 0, 10, 2, 0, 1, 5, 11, 4, 9, 3, 0, 7, 7, 1, 0, 12]
    );
    let mut classes = vec![Operand; 4];
    classes.push(Mark);
    classes.extend([Operand; 4]);
    classes.push(Mark);
    classes.extend([
        Trailing, Trailing, Middle, Middle, Middle, Middle, Leading, Leading, Mark,
    ]);
    assert_eq!(products.classes(), classes);
    let truth = &products.truth().unwrap()[0];
    assert_eq!(truth.value, 1770394);
    assert_eq!(
        truth.factorizations,
        (Some(vec![(347, 1)]), Some(vec![(2, 1), (2551, 1)]))
    );
    assert_eq!(truth.product.convolution, vec![14, 8, 13, 39, 23, 15, 0]);
    assert_eq!(truth.product.carries, vec![1, 0, 1, 4, 2, 1, 0]);
    assert_eq!(truth.product.digits, vec![4, 9, 3, 0, 7, 7, 1]);
    assert_eq!(truth.trailing, 94);
    assert_eq!(
        truth.leading,
        LeadingFace {
            operands: (3, 51),
            products: (1530000, 2074401),
            fibre: (1, 2),
            reading: 1,
        }
    );
    assert_eq!(truth.leading.width(), 2);

    let most = Products::new(decimal(DigitOrder::MostFirst), vec![(347, 5102)]).unwrap();
    assert_eq!(
        most.emit(),
        vec![0, 3, 4, 7, 10, 5, 1, 0, 2, 11, 0, 1, 7, 7, 0, 3, 9, 4, 12]
    );
    assert_eq!(
        most.classes()[10..],
        [
            Leading, Leading, Middle, Middle, Middle, Middle, Trailing, Trailing, Mark
        ]
    );

    assert_eq!(family.alphabet(), 13);
    assert_eq!(family.record_length(), 19);
    assert_eq!(family.record_span(), 18);
    assert_eq!(family.key_bits().unwrap(), 27);
    let code = SymbolicSurprisal::term(2, rat(8, 1))
        .unwrap()
        .plus(&SymbolicSurprisal::term(5, rat(8, 1)).unwrap());
    assert_eq!(family.operand_code().unwrap(), code);
    // Refused: an operand outside [0, b^L), a face outside 1 ≤ k ≤ L, and b^(2L) past the word.
    assert!(Products::new(family.clone(), vec![(10000, 1)]).is_err());
    assert!(
        ProductFamily {
            face: 0,
            ..family.clone()
        }
        .operands()
        .is_err()
    );
    assert!(
        ProductFamily {
            face: 5,
            ..family.clone()
        }
        .operands()
        .is_err()
    );
    assert!(
        ProductFamily {
            base: 16,
            digits: 9,
            ..family
        }
        .operands()
        .is_err()
    );
}

/// Drawn records in bases 2, 10 and 16 (`L = 4`, `k = 2`, both orders): every truth holds exactly:
/// the convolution's value and the carried word's are the product (Lean
/// `digit_product_is_carry_of_convolution`, `carried_word_is_product_digits`), the factorizations
/// multiply back, the trailing face is the product of the operands' trailing faces mod `b²`, and
/// the product lies in its leading interval with its leading reading in the fibre. The key
/// descriptions are `8`, `27` and `32` bits.
#[test]
fn drawn_products_keep_both_exact_faces() {
    for (base, order, key_bits) in [
        (2u64, DigitOrder::LeastFirst, 8),
        (10, DigitOrder::MostFirst, 27),
        (16, DigitOrder::LeastFirst, 32),
    ] {
        let family = ProductFamily {
            base,
            digits: 4,
            face: 2,
            order,
        };
        assert_eq!(family.key_bits().unwrap(), key_bits);
        let products = Products::draw(&family, 64, &mut Draw::new(31)).unwrap();
        let cells = products.emit();
        assert_eq!(cells.len(), 64 * 19);
        assert!(cells.iter().all(|cell| *cell < family.alphabet()));
        let modulus = base * base;
        let multiplied = |factors: &Option<Vec<(u64, u32)>>| {
            factors.as_ref().map_or(0, |factors| {
                factors.iter().map(|(p, e)| p.pow(*e)).product()
            })
        };
        for (truth, &(a, c)) in products.truth().unwrap().iter().zip(products.pairs()) {
            let value = a * c;
            assert_eq!(truth.value, value);
            assert_eq!(truth.product.convolution_value(), BigUint::from(value));
            assert_eq!(truth.product.value(), BigUint::from(value));
            let word = if value == 0 {
                Vec::new()
            } else {
                digits(value, base, digit_count(value, base)).unwrap()
            };
            assert_eq!(truth.product.digits, word);
            assert_eq!(multiplied(&truth.factorizations.0), a);
            assert_eq!(multiplied(&truth.factorizations.1), c);
            assert_eq!(truth.trailing, (a % modulus) * (c % modulus) % modulus);
            let (lower, upper) = truth.leading.products;
            assert!(lower <= value && value <= upper);
            let (first, last) = truth.leading.fibre;
            assert!(first <= truth.leading.reading && truth.leading.reading <= last);
        }
    }
}

/// Lean `grating_on_digit_index` (the record's §7.3): in the column `n = 100k + 17`, `k < 30`, each
/// prime `p ∤ 10` is a grating of period `p` on `k`: 3 covers `k ≡ 1 mod 3` (117, 417, 717, 1017,
/// …), 7 covers `k ≡ 2 mod 7` (217, 917, 1617, 2317), 11 covers `k ≡ 5 mod 11` (517, 1617, 2717),
/// 13 covers `k ≡ 1 mod 13` (117, 1417, 2717), 19 covers `k ≡ 8 mod 19` (817, 2717). The gaps are
/// the primes 17, 317, 617, 1117, 1217, 2017, 2417, 2617 and 2917: exactly the column's integers no
/// grating covers (`1717 = 17·101` is covered by 17 at `k ≡ 0` and by 101 at `k ≡ 17`, since
/// `100 ≡ −1 mod 101`). The primes of the base are not gratings; the law holds over bases 2, 6, 10 and
/// 16, trailing widths 0 to 2, every integer below 2000 and every prime up to 31.
#[test]
fn the_seventeen_column_is_covered_by_its_gratings() {
    let primes = [3u64, 7, 11, 13, 19];
    let classes: Vec<u64> = primes
        .iter()
        .map(|p| grating_class(10, 2, 17, *p).unwrap())
        .collect();
    assert_eq!(classes, vec![1, 2, 5, 1, 8]);
    let covered: Vec<Vec<u64>> = primes
        .iter()
        .map(|p| (0..30u64).filter(|k| (100 * k + 17) % p == 0).collect())
        .collect();
    for ((p, class), covered) in primes.iter().zip(&classes).zip(&covered) {
        let grating: Vec<u64> = (0..30u64).filter(|k| k % p == *class).collect();
        assert_eq!(*covered, grating);
    }
    assert_eq!(covered[0], vec![1, 4, 7, 10, 13, 16, 19, 22, 25, 28]);
    assert_eq!(covered[1], vec![2, 9, 16, 23]);
    assert_eq!(covered[2], vec![5, 16, 27]);
    assert_eq!(covered[3], vec![1, 14, 27]);
    assert_eq!(covered[4], vec![8, 27]);

    let window = PrimeWindow {
        base: 10,
        start: 0,
        end: 3000,
        digits: 4,
        trailing: 2,
        order: DigitOrder::MostFirst,
        emission: PrimeEmission::Digits,
    };
    let truth = window.truth().unwrap();
    let column: Vec<&IntegerTruth> = truth.iter().filter(|t| t.residue == 17).collect();
    assert_eq!(column.len(), 30);
    let gaps: Vec<u64> = column.iter().filter(|t| t.prime).map(|t| t.value).collect();
    assert_eq!(gaps, vec![17, 317, 617, 1117, 1217, 2017, 2417, 2617, 2917]);
    for t in &column {
        assert_eq!(t.prime, t.gratings.is_empty());
        for cover in &t.gratings {
            assert_eq!(t.leading % cover.prime, cover.class);
            assert_eq!(t.value % cover.prime, 0);
        }
    }
    let covers = |value: u64| -> Vec<(u64, u64)> {
        truth[value as usize]
            .gratings
            .iter()
            .map(|cover| (cover.prime, cover.class))
            .collect()
    };
    assert_eq!(covers(2717), vec![(11, 5), (13, 1), (19, 8)]);
    assert_eq!(covers(1617), vec![(3, 1), (7, 2), (11, 5)]);
    assert_eq!(covers(1717), vec![(17, 0), (101, 17)]);
    assert_eq!(grating_class(10, 2, 17, 2), None);
    assert_eq!(grating_class(10, 2, 17, 5), None);
    assert_eq!(grating_class(10, 2, 17, 9), None);

    let small: Vec<u64> = (2..=31).filter(|p| is_prime(*p)).collect();
    for base in [2u64, 6, 10, 16] {
        for trailing in 0..=2usize {
            let unit = base.pow(trailing as u32);
            for n in 0..2000u64 {
                for &p in small.iter().filter(|p| base % *p != 0) {
                    let class = grating_class(base, trailing, n % unit, p).unwrap();
                    assert_eq!(n % p == 0, (n / unit) % p == class);
                }
            }
        }
    }
}

/// Lean `cheap_faces` (the record's §7.3 table): the last digit reads the primes of `b`, the digit
/// sum those of `b − 1`, the alternating sum those of `b + 1`: base 2 reads 2, none, 3; base 6 reads
/// 2 and 3, 5, 7; base 10 reads 2 and 5, 3, 11; base 16 reads 2, 3 and 5, 17; base 30 reads 2, 3
/// and 5, 29, 31. Each reading is congruent to `n` modulo every divisor of its modulus, for every
/// `n` below 3000 in each base; `1617 = 3·7²·11` reads last digit 7, digit sum `15 = 3·5` and
/// alternating sum `7 − 1 + 6 − 1 = 11`.
#[test]
fn the_cheap_faces_read_the_base_and_its_neighbours() {
    let table: [(u64, [Vec<u64>; 3]); 5] = [
        (2, [vec![2], vec![], vec![3]]),
        (6, [vec![2, 3], vec![5], vec![7]]),
        (10, [vec![2, 5], vec![3], vec![11]]),
        (16, [vec![2], vec![3, 5], vec![17]]),
        (30, [vec![2, 3, 5], vec![29], vec![31]]),
    ];
    for (base, primes) in &table {
        assert_eq!(CheapFaces::of(*base).unwrap().primes(), *primes);
    }
    assert_eq!(CheapFaces::of(10).unwrap().sum, vec![(3, 2)]);
    assert_eq!(CheapFaces::of(16).unwrap().sum, vec![(3, 1), (5, 1)]);
    for (base, _) in &table {
        let base = *base;
        for n in 0..3000u64 {
            let reading = IntegerTruth::of(n, base, 1).unwrap().cheap;
            for d in 1..=base + 1 {
                if base % d == 0 {
                    assert_eq!(n % d, reading.last % d);
                }
                if (base - 1) % d == 0 {
                    assert_eq!(n % d, reading.sum % d);
                }
                if (base + 1) % d == 0 {
                    assert_eq!(
                        (n as i64).rem_euclid(d as i64),
                        reading.alternating.rem_euclid(d as i64)
                    );
                }
            }
        }
    }
    let reading = IntegerTruth::of(1617, 10, 2).unwrap().cheap;
    assert_eq!(
        reading,
        CheapReading {
            last: 7,
            sum: 15,
            alternating: 11,
        }
    );
    assert!(CheapFaces::of(1).is_err());
}

/// A prime window `[0, 30)` in base 6, two digits most significant first: `00₆` and `01₆` close with
/// the mark 6, `02₆`, `03₆` and `11₆ = 7` with the prime mark 7. Its indicator marks the ten primes
/// below 30. Its density's code is `30 H(1/3) = 30 log₂ 3 − 20` bits; read through the last digit
/// (`n mod 6`) the classes hold `(5, 0), (5, 3), (5, 1), (5, 1), (5, 0), (5, 5)` integers and
/// primes, and the code is `5 H(3/5) + 2·5 H(1/5) = 15 log₂ 5 − 3 log₂ 3 − 18` bits. `0` has no
/// factorization, `1` the empty one, neither is prime; every truth's primality agrees with the
/// crate's decided primality, and the window `[0, 10^4)` holds `1229` primes.
#[test]
fn a_prime_window_emits_its_records_and_reads_its_density() {
    let window = PrimeWindow {
        base: 6,
        start: 0,
        end: 30,
        digits: 2,
        trailing: 1,
        order: DigitOrder::MostFirst,
        emission: PrimeEmission::Digits,
    };
    let cells = window.emit().unwrap();
    assert_eq!(cells.len(), 90);
    assert_eq!(&cells[..12], &[0, 0, 6, 0, 1, 6, 0, 2, 7, 0, 3, 7]);
    assert_eq!(&cells[21..24], &[1, 1, 7]);
    assert_eq!(window.alphabet(), 8);
    let classes = window.classes();
    assert_eq!(classes.len(), 90);
    assert_eq!(
        classes[..3],
        [PrimeCell::Digit, PrimeCell::Digit, PrimeCell::Primality]
    );
    let indicator = PrimeWindow {
        emission: PrimeEmission::Indicator,
        ..window.clone()
    };
    assert_eq!(
        indicator.emit().unwrap(),
        vec![
            0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0,
            1
        ]
    );
    assert_eq!(indicator.alphabet(), 2);
    assert!(
        indicator
            .classes()
            .iter()
            .all(|c| *c == PrimeCell::Primality)
    );

    let density = window.face_code(1).unwrap();
    assert_eq!(
        density.classes,
        vec![ClassCount {
            residue: 0,
            integers: 30,
            primes: 10,
        }]
    );
    let expected = SymbolicSurprisal::term(2, rat(-20, 1))
        .unwrap()
        .plus(&SymbolicSurprisal::term(3, rat(30, 1)).unwrap());
    assert_eq!(density.code, expected);
    let face = window.face_code(6).unwrap();
    let counts: Vec<(u64, u64)> = face
        .classes
        .iter()
        .map(|c| (c.integers, c.primes))
        .collect();
    assert_eq!(counts, vec![(5, 0), (5, 3), (5, 1), (5, 1), (5, 0), (5, 5)]);
    let expected = SymbolicSurprisal::term(2, rat(-18, 1))
        .unwrap()
        .plus(&SymbolicSurprisal::term(3, rat(-3, 1)).unwrap())
        .plus(&SymbolicSurprisal::term(5, rat(15, 1)).unwrap());
    assert_eq!(face.code, expected);

    let truth = window.truth().unwrap();
    assert_eq!(truth[0].factors, None);
    assert_eq!(truth[1].factors, Some(Vec::new()));
    assert!(!truth[0].prime && !truth[1].prime);
    assert_eq!(truth[0].least_factor, None);
    assert_eq!(truth[25].least_factor, Some(5));
    assert_eq!(
        truth[25].gratings,
        vec![GratingCover { prime: 5, class: 4 }]
    );
    for t in &truth {
        assert_eq!(t.prime, is_prime(t.value));
    }
    let wide = PrimeWindow {
        start: 0,
        end: 10_000,
        digits: 6,
        ..window.clone()
    };
    assert_eq!(wide.face_code(1).unwrap().classes[0].primes, 1229);
    assert!(wide.face_code(0).is_err());
    assert!(
        PrimeWindow {
            end: 37,
            ..window.clone()
        }
        .emit()
        .is_err()
    );
    assert!(
        PrimeWindow {
            start: 30,
            ..window
        }
        .truth()
        .is_err()
    );
}

/// Lean `ArithmeticContract.{carryWord_cons, carryWord_value, carryWord_lt, encode, decode}`: the
/// cascade carries Brandon's `7 · 3` (`[1,2,2,1]` to `10101₂`, carries `[0,1,1,1,0]`) and
/// `FF₁₆ · FF₁₆` (`[225,450,225]` to `FE01₁₆`, carries `[14,29,15,0]`), keeps the value and emits
/// digits below the base on words of any naturals; encoding reads the odometer, decoding inverts it.
#[test]
fn the_carry_cascade_keeps_the_value_and_emits_digits() {
    assert_eq!(
        carry_cascade(2, &[1, 2, 2, 1]).unwrap(),
        (vec![1, 0, 1, 0, 1], vec![0, 1, 1, 1, 0])
    );
    assert_eq!(
        carry_cascade(16, &[225, 450, 225]).unwrap(),
        (vec![1, 0, 14, 15], vec![14, 29, 15, 0])
    );
    assert_eq!(carry_cascade(10, &[0, 0]).unwrap(), (vec![], vec![]));
    let mut draw = Draw::new(2_026_092_933);
    for base in BASES {
        for _ in 0..64 {
            let word: Vec<u64> = (0..1 + draw.below(8))
                .map(|_| draw.below(1 << 12) as u64)
                .collect();
            let (digits, _) = carry_cascade(base, &word).unwrap();
            assert_eq!(decode(base, &digits), decode(base, &word));
            assert!(digits.iter().all(|&digit| digit < base));
            assert_ne!(digits.last(), Some(&0));
        }
    }
    assert_eq!(
        encode(10, &BigUint::from(1_770_394u32)).unwrap(),
        vec![4, 9, 3, 0, 7, 7, 1]
    );
    assert_eq!(encode(2, &BigUint::zero()).unwrap(), Vec::<u64>::new());
    assert_eq!(
        decode(16, &[10, 9, 3, 0, 11, 1]),
        BigUint::from(0x1B_039Au32)
    );
    assert!(encode(1, &BigUint::from(3u32)).is_err());
}

/// Lean `ArithmeticContract.{consumer_add, consumer_mul, consumer_pow, consumer_rebase}` and
/// `PhaseCarry.carried_circle_is_not_the_split_product`: on seeded operands below `2^13` (exponents
/// below 4) in bases 2, 10 and 16, every producer's native consequence decodes to its scalar `T`, its
/// digits lie below the base, and it rebases alike; the carry-free sum's released windings are the
/// operands' common bits, `a + c = (a ⊕ c) + 2 (a ∧ c)`. Fixtures: `347 ⊕ 5102 = 0x12B5 = 4789` with
/// `347 ∧ 5102 = 0x14A = 330`, and `347^3 = 41781923`.
#[test]
fn every_producer_closes_the_consumer_square_and_rebases() {
    let mut draw = Draw::new(2_026_092_943);
    for base in BASES {
        for _ in 0..64 {
            let (a, c, e) = (
                draw.below(1 << 13) as u64,
                draw.below(1 << 13) as u64,
                draw.below(4) as u64,
            );
            for producer in Producer::ALL {
                let right = if producer == Producer::Power { e } else { c };
                let (x, y) = (BigUint::from(a), BigUint::from(right));
                let scalar = producer.scalar(&x, &y).unwrap();
                let native = producer
                    .consequence(base, &encode(base, &x).unwrap(), &encode(base, &y).unwrap())
                    .unwrap();
                assert_eq!(
                    native.value(),
                    scalar,
                    "{producer:?} {a} {right} base {base}"
                );
                assert!(native.digits.iter().all(|&digit| digit < base));
                for other in BASES {
                    let rebased = producer
                        .consequence(
                            other,
                            &encode(other, &x).unwrap(),
                            &encode(other, &y).unwrap(),
                        )
                        .unwrap();
                    assert_eq!(rebased.value(), scalar);
                }
                if producer == Producer::CarryFree {
                    let common = decode(2, &native.carries[0]);
                    assert_eq!(common, BigUint::from(a & c));
                    assert_eq!(&scalar + &common * 2u32, BigUint::from(a + c));
                }
            }
        }
    }
    let xor = Producer::CarryFree
        .consequence(16, &[11, 5, 1], &[14, 14, 3, 1])
        .unwrap();
    assert_eq!(xor.digits, vec![5, 11, 2, 1]);
    assert_eq!(decode(2, &xor.carries[0]), BigUint::from(330u32));
    let power = Producer::Power.consequence(10, &[7, 4, 3], &[3]).unwrap();
    assert_eq!(power.value(), BigUint::from(41_781_923u32));
    assert_eq!(power.carries.len(), 3);
    let zero = Producer::Power.consequence(10, &[], &[]).unwrap();
    assert_eq!(zero.digits, vec![1]);
}

/// The record's §6 lines: `so 347 × 5102 = 1770394.`, `assert!(0x15B * 0x13EE == 0x1B039A);` and
/// `example : 0x15B * 0x13EE = 0x1B039A := by norm_num`; the truth's result glyphs and the numeral's
/// end; `1770394 = 2·347·2551`; the chart's `^` the power in prose and Lean and the carry-free sum in
/// Rust; a request refused where its chart wears no glyph for the producer; the glyph set reads
/// numerals back.
#[test]
fn the_three_charts_write_the_records_lines() {
    let drawn = vec![
        Drawn {
            slot: Slot::Product,
            left: 347,
            right: 5102,
            exponent: 3,
        },
        Drawn {
            slot: Slot::Caret,
            left: 347,
            right: 5102,
            exponent: 3,
        },
    ];
    let text = |stream: &ExpressionStream| -> String {
        String::from_utf8(stream.cells.iter().map(|&cell| cell as u8).collect()).unwrap()
    };
    let family = |base| ExpressionFamily {
        base,
        operands: 1 << 13,
        exponents: 4,
    };
    let decimal = Expressions::new(family(10), drawn.clone()).unwrap();
    let hex = Expressions::new(family(16), drawn).unwrap();
    let prose = decimal.emit(Chart::Prose).unwrap();
    assert_eq!(
        text(&prose),
        "so 347 × 5102 = 1770394.\nso 347 ^ 3 = 41781923.\n"
    );
    let rust = hex.emit(Chart::Rust).unwrap();
    assert_eq!(
        text(&rust),
        "assert!(0x15B * 0x13EE == 0x1B039A);\nassert!(0x15B ^ 0x13EE == 0x12B5);\n"
    );
    let lean = hex.emit(Chart::Lean).unwrap();
    assert_eq!(
        text(&lean),
        "example : 0x15B * 0x13EE = 0x1B039A := by norm_num\nexample : 0x15B ^ 0x3 = 0x27D8AA3 := by norm_num\n"
    );
    let truth = &rust.truths[0];
    let glyphs: Vec<u8> = rust.cells[truth.result.clone()]
        .iter()
        .map(|&cell| cell as u8)
        .collect();
    assert_eq!(glyphs, b"0x1B039A");
    assert_eq!(rust.cells[truth.end], usize::from(b')'));
    assert_eq!(truth.value, BigUint::from(1_770_394u32));
    assert_eq!(truth.factorization, Some(vec![(2, 1), (347, 1), (2551, 1)]));
    assert_eq!(rust.truths[1].producer, Producer::CarryFree);
    assert_eq!(lean.truths[1].producer, Producer::Power);
    assert_eq!(lean.truths[1].operands, (347, 3));
    assert_eq!(lean.cells[lean.truths[0].end], usize::from(b' '));
    assert!(Chart::Rust.request(Producer::Power, 10, 2, 2).is_err());
    assert!(Chart::Lean.request(Producer::CarryFree, 10, 2, 2).is_err());
    assert_eq!(
        read_numeral(b"0x1B039A"),
        Some((16, BigUint::from(1_770_394u32)))
    );
    assert_eq!(read_numeral(b"0b101"), Some((2, BigUint::from(5u32))));
    assert_eq!(read_numeral(b"0x"), None);
    assert_eq!(read_numeral(b"12A"), None);
    assert!(
        Expressions::new(
            family(10),
            vec![Drawn {
                slot: Slot::Sum,
                left: 1 << 13,
                right: 0,
                exponent: 0
            }]
        )
        .is_err()
    );
    assert!(Expressions::new(family(8), Vec::new()).is_err());
}
