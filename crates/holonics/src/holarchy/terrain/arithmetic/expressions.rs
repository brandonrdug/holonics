//! **Expressions: sums, products and powers as prose, Rust and Lean write them, with their exact
//! truths** (the arithmetic contract's record,
//! `2026-09-29_THE_ARITHMETIC_CONTRACT_A_NUMERAL_IS_A_FACE_OF_A_COUNTING_NAVIGATOR_AND_ITS_PRODUCER_IS_A_KEY.md`,
//! §2 and §6; THE_REBUILD U6 item 3; #73, #148).
//!
//! [definition] **The declared glyph set** (the record's §2), one for every chart: a numeral is a
//! base declaration, `0b` (two), `0x` (sixteen) or none (ten), then its digits most significant
//! first, `0–9` and `A–F` (read in either case, written upper: [`digit_of`], [`glyph_of`],
//! [`numeral`]); the operator glyphs `+` (the sum), `*`, `×` and `·` (the product) and `^`, the one
//! glyph the set declares plural ([`Operator::producers`]: the power or the carry-free sum, its
//! pairing located per stream by the receiver); the relation glyphs `=` and `==`. The receiver's
//! numeral port (`receiver::population::arithmetic::ExpressionPort`) reads this set and nothing of a
//! chart.
//!
//! [definition] **The producers** ([`Producer`]), each a navigator whose key is its operands: the
//! sum, the product, the power (the right operand read as a count) and the carry-free sum (Rust's
//! `^`, exclusive or: the base-2 sum with its carry released, the circle without the helix, Lean
//! `PhaseCarry.carried_circle_is_not_the_split_product`). Each has two readings joined by the
//! consumer equation `decode_b(T_native(encode_b a, encode_b c)) = T(a, c)` (Lean
//! `ArithmeticContract.{consumer_add, consumer_mul, consumer_pow}`):
//! - `T` ([`Producer::scalar`]): the chart-free integer consequence;
//! - `T_native` ([`Producer::consequence`]): the operands' digit words joined at a pair port
//!   (pointwise for the sum, by convolution for the product, by repeated convolution for the power)
//!   and carried by one cascade ([`super::carry_cascade`], [`super::digit_product`]); the carry-free
//!   sum rebases both words to base 2, joins them pointwise and keeps each place's phase, releasing
//!   its winding (the released windings are the operands' common bits), then rebases the phases to
//!   `b`. The [`Consequence`] carries the digit word and each cascade's carry word.
//!
//! [definition; agent-inferred] **The chart layouts** ([`Chart`]; the record's §6), one line an
//! expression:
//!
//! | Chart | Line | Its producers' glyphs |
//! |---|---|---|
//! | prose | `so 347 × 5102 = 1770394.` | `+`, `×`, `^` the power |
//! | Rust | `assert!(0x15B * 0x13EE == 0x1B039A);` | `+`, `*`, `^` the carry-free sum (Rust has no power glyph) |
//! | Lean | `example : 0x15B * 0x13EE = 0x1B039A := by norm_num` | `+`, `*`, `^` the power |
//!
//! Every numeral of a line is written in the stream's base. Every Rust line is Rust whose integers
//! stay within its default `i32` for the declared operands below `2^13`, and every Lean line is a
//! statement `norm_num` proves; neither is read here (Lean verifies mathematics outside the HNN).
//!
//! [definition; agent-inferred] **The draw** ([`Expressions::draw`]): per expression, a slot among
//! three (the sum, the product, and the chart's third producer, the one its `^` wears), the left and
//! right operands uniform below the declared bound and an exponent uniform below its declared
//! bound, in that order, from the seeded draw. One draw serves the three charts of a base, so the
//! sum and product expressions are equal in all three and the power expressions in prose and Lean;
//! the carry-free sum takes the drawn right operand, the power the drawn exponent.
//!
//! [proved-derived; implemented-exact] **The truth** ([`ExpressionTruth`]) of each line: its key
//! (the producer and the operands), the consequence's digit word and carry words, the value `T` and
//! its factorization, and where the line, its result's glyphs and the cell after them (the
//! numeral's end) lie in the stream.
//!
//! [definition] The computational object is the helical pair interaction: the operands' digit words
//! meet at a pair port (digit `i` with digit `l` at place `i + l` for the product), and each place's
//! wheel carries its winding up. Of the winding guide's six general objects this owner touches the
//! **helix** (each place's wheel and its carry), the **pair** (the operands' pair port) and **faces
//! and placement** (the numeral face in a declared base); the **tower thread** (base 2 restricts to
//! 16 by grouping, the carry-free sum's rebase), the **cell holonomy** (none: the digits exchange no
//! power) and the **tube** (the stream's span, one line an expression) stay attached.

use std::ops::Range;

use num_bigint::BigUint;
use num_traits::{ToPrimitive, Zero};

use super::super::{Draw, TerrainError, refuse};
use super::{Factorization, carry_cascade, check_base, decode, digit_product, encode};
use crate::geometry::winding::{phase, winding};
use crate::ratio::surprisal::factor_biguint;

// -------------------------------------------------------------------------------------------
// the declared glyph set

/// [definition] **The bases the glyph set declares**: two (`0b`), ten (no prefix), sixteen (`0x`).
pub const BASES: [u64; 3] = [2, 10, 16];

/// **A base's declaration glyphs** (module header): `0b`, none, `0x`; refused for a base the glyph
/// set does not declare.
pub fn prefix(base: u64) -> Result<&'static [u8], TerrainError> {
    match base {
        2 => Ok(b"0b"),
        10 => Ok(b""),
        16 => Ok(b"0x"),
        _ => Err(refuse(
            "a numeral's base",
            "the glyph set declares bases 2, 10 and 16",
        )),
    }
}

/// **The base a prefix letter declares** after a numeral's leading `0`: `b`/`B` two, `x`/`X`
/// sixteen.
pub fn prefixed(glyph: u8) -> Option<u64> {
    match glyph {
        b'b' | b'B' => Some(2),
        b'x' | b'X' => Some(16),
        _ => None,
    }
}

/// **A digit glyph's digit**: `0–9`, and `A–F` or `a–f` for ten to fifteen; none for any other
/// glyph. Whether it is a digit of a base is `digit < b`.
pub fn digit_of(glyph: u8) -> Option<u64> {
    match glyph {
        b'0'..=b'9' => Some(u64::from(glyph - b'0')),
        b'A'..=b'F' => Some(u64::from(glyph - b'A') + 10),
        b'a'..=b'f' => Some(u64::from(glyph - b'a') + 10),
        _ => None,
    }
}

/// **A digit's glyph**, written upper; none past fifteen.
pub fn glyph_of(digit: u64) -> Option<u8> {
    match digit {
        0..=9 => Some(b'0' + digit as u8),
        10..=15 => Some(b'A' + (digit - 10) as u8),
        _ => None,
    }
}

/// **A numeral**: the base's declaration, then the word's digits (least significant first) most
/// significant first; `0` for the empty word. Refused for an undeclared base or a digit at or past
/// the base.
pub fn numeral(base: u64, word: &[u64]) -> Result<Vec<u8>, TerrainError> {
    let mut glyphs = prefix(base)?.to_vec();
    if word.is_empty() {
        glyphs.push(b'0');
    }
    for &digit in word.iter().rev() {
        if digit >= base {
            return Err(refuse("a numeral's digit", "it lies below its base"));
        }
        glyphs.push(glyph_of(digit).expect("a digit below a declared base"));
    }
    Ok(glyphs)
}

/// **A numeral read back** through the glyph set: its base and its value; none unless the glyphs are
/// exactly one numeral.
pub fn read_numeral(glyphs: &[u8]) -> Option<(u64, BigUint)> {
    let (base, digits) = match glyphs {
        [b'0', letter, rest @ ..] if prefixed(*letter).is_some() => (prefixed(*letter)?, rest),
        _ => (10, glyphs),
    };
    if digits.is_empty() {
        return None;
    }
    let word = digits
        .iter()
        .rev()
        .map(|&glyph| digit_of(glyph).filter(|&digit| digit < base))
        .collect::<Option<Vec<u64>>>()?;
    Some((base, decode(base, &word)))
}

/// [definition] **An operator glyph** of the declared set (module header).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Operator {
    Plus,
    Star,
    Cross,
    Dot,
    Caret,
}

impl Operator {
    /// The declared operator glyphs.
    pub const ALL: [Operator; 5] = [
        Operator::Plus,
        Operator::Star,
        Operator::Cross,
        Operator::Dot,
        Operator::Caret,
    ];

    /// The glyph's bytes: `+`, `*`, `×`, `·`, `^`.
    pub fn glyphs(self) -> &'static [u8] {
        match self {
            Operator::Plus => b"+",
            Operator::Star => b"*",
            Operator::Cross => "×".as_bytes(),
            Operator::Dot => "·".as_bytes(),
            Operator::Caret => b"^",
        }
    }

    /// **The producers the glyph set declares for the glyph**: one, or the plural glyph's
    /// admitted pairings, whose key the receiver locates per stream (module header).
    pub fn producers(self) -> &'static [Producer] {
        match self {
            Operator::Plus => &[Producer::Sum],
            Operator::Star | Operator::Cross | Operator::Dot => &[Producer::Product],
            Operator::Caret => &[Producer::Power, Producer::CarryFree],
        }
    }
}

// -------------------------------------------------------------------------------------------
// the producers

/// [definition] **A producer** (module header): a navigator whose key is its two operands.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Producer {
    Sum,
    Product,
    Power,
    CarryFree,
}

/// [definition] **A consequence on digit words** (module header): the producer, the base, the
/// digit word least significant first with no zero at its top (empty for zero), and each cascade's
/// carry word: one for the sum and the product, one a factor for the power, and for the carry-free
/// sum the windings its base-2 places released.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Consequence {
    pub producer: Producer,
    pub base: u64,
    pub digits: Vec<u64>,
    pub carries: Vec<Vec<u64>>,
}

impl Consequence {
    /// `decode_b` of the digit word.
    pub fn value(&self) -> BigUint {
        decode(self.base, &self.digits)
    }
}

/// The pointwise sum of two words, least significant first, before carry (Lean
/// `ArithmeticContract.zipAdd`).
fn zip_add(left: &[u64], right: &[u64]) -> Result<Vec<u64>, TerrainError> {
    (0..left.len().max(right.len()))
        .map(|place| {
            let (x, y) = (
                left.get(place).copied().unwrap_or(0),
                right.get(place).copied().unwrap_or(0),
            );
            x.checked_add(y)
                .ok_or_else(|| refuse("a pointwise sum", "its terms stay within the machine word"))
        })
        .collect()
}

impl Producer {
    /// The declared producers.
    pub const ALL: [Producer; 4] = [
        Producer::Sum,
        Producer::Product,
        Producer::Power,
        Producer::CarryFree,
    ];

    /// The producer's name.
    pub fn name(self) -> &'static str {
        match self {
            Producer::Sum => "the sum",
            Producer::Product => "the product",
            Producer::Power => "the power",
            Producer::CarryFree => "the carry-free sum",
        }
    }

    /// **`T(a, c)`, the chart-free integer consequence** (module header); the power's exponent is
    /// the right operand read as a count, refused past the machine's 32-bit exponent.
    pub fn scalar(self, left: &BigUint, right: &BigUint) -> Result<BigUint, TerrainError> {
        Ok(match self {
            Producer::Sum => left + right,
            Producer::Product => left * right,
            Producer::Power => left.pow(
                right
                    .to_u32()
                    .ok_or_else(|| refuse("a power's exponent", "it is a count within 32 bits"))?,
            ),
            Producer::CarryFree => left ^ right,
        })
    }

    /// **`T_native` on digit words** (module header): the operands' words in base `b`, least
    /// significant first, joined at the pair port and carried by one cascade. Refused for a base
    /// below two, a term past the machine word, or a power's exponent past 32 bits.
    pub fn consequence(
        self,
        base: u64,
        left: &[u64],
        right: &[u64],
    ) -> Result<Consequence, TerrainError> {
        check_base(base)?;
        let (digits, carries) = match self {
            Producer::Sum => {
                let (digits, carries) = carry_cascade(base, &zip_add(left, right)?)?;
                (digits, vec![carries])
            }
            Producer::Product => {
                let product = digit_product(base, left, right)?;
                (product.digits, vec![product.carries])
            }
            Producer::Power => {
                let exponent = decode(base, right)
                    .to_u32()
                    .ok_or_else(|| refuse("a power's exponent", "it is a count within 32 bits"))?;
                // Lean `powWord`: `[1]` at zero, then each factor carried before the next.
                let (mut word, mut carries) = (vec![1u64], Vec::new());
                for _ in 0..exponent {
                    let product = digit_product(base, &word, left)?;
                    word = product.digits;
                    carries.push(product.carries);
                }
                (word, carries)
            }
            Producer::CarryFree => {
                let two = BigUint::from(2u32);
                let (x, y) = (
                    encode(2, &decode(base, left))?,
                    encode(2, &decode(base, right))?,
                );
                let sum = zip_add(&x, &y)?;
                let (mut phases, mut released) = (Vec::new(), Vec::new());
                for total in sum.iter().map(|&t| BigUint::from(t)) {
                    let place = phase(&two, &total).expect("two steps");
                    let carry = winding(&two, &total).expect("two steps");
                    phases.push(place.to_u64().expect("a binary phase"));
                    released.push(carry.to_u64().expect("a binary winding"));
                }
                let digits = encode(base, &decode(2, &phases))?;
                (digits, vec![released])
            }
        };
        Ok(Consequence {
            producer: self,
            base,
            digits,
            carries,
        })
    }
}

// -------------------------------------------------------------------------------------------
// the charts

/// [definition; agent-inferred] **A chart** (module header): prose, Rust or Lean.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Chart {
    Prose,
    Rust,
    Lean,
}

impl Chart {
    /// The declared charts.
    pub const ALL: [Chart; 3] = [Chart::Prose, Chart::Rust, Chart::Lean];

    /// The chart's name.
    pub fn name(self) -> &'static str {
        match self {
            Chart::Prose => "prose",
            Chart::Rust => "Rust",
            Chart::Lean => "Lean",
        }
    }

    /// **The glyph the chart wears for a producer** (module header); none where it wears none.
    pub fn operator(self, producer: Producer) -> Option<Operator> {
        match (self, producer) {
            (_, Producer::Sum) => Some(Operator::Plus),
            (Chart::Prose, Producer::Product) => Some(Operator::Cross),
            (Chart::Rust | Chart::Lean, Producer::Product) => Some(Operator::Star),
            (Chart::Prose | Chart::Lean, Producer::Power) => Some(Operator::Caret),
            (Chart::Rust, Producer::CarryFree) => Some(Operator::Caret),
            _ => None,
        }
    }

    /// The producer the chart's `^` wears: the carry-free sum in Rust, the power otherwise.
    pub fn caret(self) -> Producer {
        match self {
            Chart::Rust => Producer::CarryFree,
            Chart::Prose | Chart::Lean => Producer::Power,
        }
    }

    fn opening(self) -> &'static [u8] {
        match self {
            Chart::Prose => b"so ",
            Chart::Rust => b"assert!(",
            Chart::Lean => b"example : ",
        }
    }

    fn relation(self) -> &'static [u8] {
        match self {
            Chart::Rust => b"==",
            Chart::Prose | Chart::Lean => b"=",
        }
    }

    /// **The line's close after its result**: `.`, `);` or ` := by norm_num`, then the line's end.
    pub fn close(self) -> &'static [u8] {
        match self {
            Chart::Prose => b".\n",
            Chart::Rust => b");\n",
            Chart::Lean => b" := by norm_num\n",
        }
    }

    /// **A request's glyphs** (module header): the line up to its result, `so a × c = `,
    /// `assert!(a * c == ` or `example : a * c = `, every numeral in `base`. Refused where the chart
    /// wears no glyph for the producer (the power in Rust, the carry-free sum in prose and Lean) or
    /// the base is undeclared.
    pub fn request(
        self,
        producer: Producer,
        base: u64,
        left: u64,
        right: u64,
    ) -> Result<Vec<u8>, TerrainError> {
        let operator = self.operator(producer).ok_or_else(|| {
            refuse(
                "a request's producer",
                "its chart wears a declared glyph for it",
            )
        })?;
        let mut glyphs = self.opening().to_vec();
        glyphs.extend(numeral(base, &encode(base, &BigUint::from(left))?)?);
        glyphs.push(b' ');
        glyphs.extend(operator.glyphs());
        glyphs.push(b' ');
        glyphs.extend(numeral(base, &encode(base, &BigUint::from(right))?)?);
        glyphs.push(b' ');
        glyphs.extend(self.relation());
        glyphs.push(b' ');
        Ok(glyphs)
    }
}

// -------------------------------------------------------------------------------------------
// the drawn expressions

/// [definition; agent-inferred] **The declared expression family** (module header): the stream's
/// base, the operands' bound (operands uniform on `[0, operands)`) and the exponents' bound.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExpressionFamily {
    pub base: u64,
    pub operands: u64,
    pub exponents: u64,
}

/// [definition] **A drawn expression's slot**: the sum, the product, or the chart's `^`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Slot {
    Sum,
    Product,
    Caret,
}

/// [definition] **A drawn expression** (module header): its slot, its two operands and its
/// exponent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Drawn {
    pub slot: Slot,
    pub left: u64,
    pub right: u64,
    pub exponent: u64,
}

impl Drawn {
    /// The producer the expression carries in a chart.
    pub fn producer(&self, chart: Chart) -> Producer {
        match self.slot {
            Slot::Sum => Producer::Sum,
            Slot::Product => Producer::Product,
            Slot::Caret => chart.caret(),
        }
    }

    /// The operands the expression carries in a chart: the exponent is the power's right operand.
    pub fn operands(&self, chart: Chart) -> (u64, u64) {
        match self.producer(chart) {
            Producer::Power => (self.left, self.exponent),
            _ => (self.left, self.right),
        }
    }
}

/// [proved-derived; implemented-exact] **An expression's exact truth** (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExpressionTruth {
    pub index: usize,
    pub producer: Producer,
    pub operands: (u64, u64),
    pub base: u64,
    pub consequence: Consequence,
    pub value: BigUint,
    pub factorization: Option<Factorization>,
    /// The line's cells.
    pub line: Range<usize>,
    /// The result numeral's glyph cells.
    pub result: Range<usize>,
    /// The cell after the result's glyphs: where the numeral ends.
    pub end: usize,
}

/// [definition] **A chart's stream** of a base's expressions: its cells (bytes) and each line's
/// truth.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExpressionStream {
    pub chart: Chart,
    pub base: u64,
    pub cells: Vec<usize>,
    pub truths: Vec<ExpressionTruth>,
}

/// [definition] **A base's drawn expressions** (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expressions {
    family: ExpressionFamily,
    drawn: Vec<Drawn>,
}

impl Expressions {
    /// The declared expressions; refused for an undeclared base, an empty bound, or an operand or
    /// exponent at or past its bound.
    pub fn new(family: ExpressionFamily, drawn: Vec<Drawn>) -> Result<Self, TerrainError> {
        prefix(family.base)?;
        if family.operands == 0 || family.exponents == 0 {
            return Err(refuse(
                "an expression family",
                "its operands' and exponents' bounds hold a value",
            ));
        }
        if drawn.iter().any(|expression| {
            expression.left >= family.operands
                || expression.right >= family.operands
                || expression.exponent >= family.exponents
        }) {
            return Err(refuse(
                "a drawn expression",
                "its operands and exponent lie below their declared bounds",
            ));
        }
        Ok(Self { family, drawn })
    }

    /// **`count` expressions drawn from the family** (module header): the slot, the left and right
    /// operands and the exponent, in that order, each uniform below its bound.
    pub fn draw(
        family: ExpressionFamily,
        count: usize,
        draw: &mut Draw,
    ) -> Result<Self, TerrainError> {
        let bound = |value: u64| {
            usize::try_from(value)
                .map_err(|_| refuse("a bound", "it lies within the address space"))
        };
        let (operands, exponents) = (bound(family.operands)?, bound(family.exponents)?);
        let drawn = (0..count)
            .map(|_| {
                let slot = [Slot::Sum, Slot::Product, Slot::Caret][draw.below(3)];
                Drawn {
                    slot,
                    left: draw.below(operands) as u64,
                    right: draw.below(operands) as u64,
                    exponent: draw.below(exponents) as u64,
                }
            })
            .collect();
        Self::new(family, drawn)
    }

    pub fn family(&self) -> ExpressionFamily {
        self.family
    }

    pub fn drawn(&self) -> &[Drawn] {
        &self.drawn
    }

    /// **A chart's stream** (module header): every expression's line, with its truth.
    pub fn emit(&self, chart: Chart) -> Result<ExpressionStream, TerrainError> {
        let base = self.family.base;
        let mut cells: Vec<usize> = Vec::new();
        let mut truths = Vec::with_capacity(self.drawn.len());
        for (index, expression) in self.drawn.iter().enumerate() {
            let producer = expression.producer(chart);
            let (left, right) = expression.operands(chart);
            let (a, c) = (BigUint::from(left), BigUint::from(right));
            let consequence = producer.consequence(base, &encode(base, &a)?, &encode(base, &c)?)?;
            let value = producer.scalar(&a, &c)?;
            let start = cells.len();
            cells.extend(
                chart
                    .request(producer, base, left, right)?
                    .into_iter()
                    .map(usize::from),
            );
            let result_start = cells.len();
            cells.extend(
                numeral(base, &encode(base, &value)?)?
                    .into_iter()
                    .map(usize::from),
            );
            let end = cells.len();
            cells.extend(chart.close().iter().map(|&glyph| usize::from(glyph)));
            let factorization = if value.is_zero() {
                None
            } else {
                Some(factor_biguint(&value).map_err(|_| {
                    refuse(
                        "a consequence's factorization",
                        "its primes fit a machine word",
                    )
                })?)
            };
            truths.push(ExpressionTruth {
                index,
                producer,
                operands: (left, right),
                base,
                consequence,
                value,
                factorization,
                line: start..cells.len(),
                result: result_start..end,
                end,
            });
        }
        Ok(ExpressionStream {
            chart,
            base,
            cells,
            truths,
        })
    }
}
