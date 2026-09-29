//! **The numeral port and the expression egg: a written result coded at its operands' cost, its
//! producer's key kept, and its release as egg packing** (the arithmetic contract's record,
//! `2026-09-29_THE_ARITHMETIC_CONTRACT_A_NUMERAL_IS_A_FACE_OF_A_COUNTING_NAVIGATOR_AND_ITS_PRODUCER_IS_A_KEY.md`,
//! §4a, §5 and §6; THE_REBUILD U6 item 3; #73, #148; Lean `Mathematics/ArithmeticContract`,
//! `Compression/Landmark/Context/Composition`).
//!
//! [definition; agent-inferred] **The numeral port** ([`ExpressionPort`]) is a keystone of one key
//! read from the coded past, as the boundary egg's part clock is: it locates nothing, so its
//! chain-rule term is zero, and its keys are cells the byte tree codes anyway. It reads the declared
//! glyph set of `holarchy::terrain::arithmetic` (numerals `0b…`, `0x…` or bare decimal, the operator
//! glyphs `+ * × · ^`, the relations `=` and `==`, spaces between) and nothing of a chart: no
//! prose, Rust or Lean branch exists. At each cell it exposes the expression's phase
//! ([`ExpressionPhase`]): outside, operand 1 at its place, the operator awaited, operand 2, the
//! relation awaited, the result awaited, or the result's place `j`. A numeral begins at a decimal
//! digit preceded neither by an identifier glyph (so Rust's `u64` holds no numeral) nor by a digit
//! and a separator `,` (the tail of `1,000`), and a glyph that ends a numeral is read again in the
//! phase its end opens. While an expression is open the port
//! holds its operand words; at its close they are released, since no admitted future reads them
//! (the record's §5: nothing of the raw stream is kept).
//!
//! [definition; agent-inferred] **The glyph pairing** of the one plural glyph `^` ([`PLURAL`]): its
//! keys are the producers the glyph set admits for it (the power, the carry-free sum), under the
//! uniform prior, weighed by Bayes on the result cells (the composition law's mixture,
//! `Composition.{composedFace_nonneg, composedFace_sum_one, composed_telescope}`), and **located by
//! which pairing's results hold** (the record's §2): at an expression's close, when one living key's
//! consequence held, every living key whose consequence did not hold (it failed, or it was not
//! computed: a power past the admitted exponents) dies with a receipt ([`PairingDeath`]). A false
//! result stated in a stream holds under no key and kills none. The keys share the port and the
//! byte tree, which no key changes, so they are one egg rather than a `Composed` of copies: a common
//! factor cancels from the posterior. With a key killed, the product of the faces is at least the
//! located key's prior share times its likelihood, so the pairing costs at most `log₂ |K| = 1` bit a
//! stream (the chain rule's `log₂ |K| − log₂ #S` with the survivor located).
//!
//! [definition; agent-inferred] **The holds sheet** (the record's §4a): each pairing key carries a
//! two-key keystone `{holds, free}` whose prior at each expression is the Krichevsky–Trofimov face
//! of the key's past expressions, `P(holds) = (2h + 1)/(2n + 2)` (`h` of `n` held). Under `holds` the
//! face is the consequence's glyph, one-hot; under `free` it is the byte tree's face. A false result
//! kills `holds` for that expression only. Each cell's face factors as `q(x) = c(x) · s(x)`, a
//! **chart** part `c` the byte tree decides and a **sheet** part `s` the result decides
//! ([`CellReading`]; the staged form, `Composition.{staged_chain_rule, staged_code}`):
//!
//! | The cell | `c(x)` | `s(x)` under a key, `A` and `B` its holds and free contributions so far |
//! |---|---|---|
//! | outside the result | `T(x)` | `1` |
//! | the result awaited, `x` a decimal digit (`S`) | `T(S)`, the numeral's start | `(A[x = x̂₀] + B T(x)/T(S))/(A + B)` |
//! | the result awaited, any other glyph | `T(x)` | `1` |
//! | the result's place `j`, `x` continuing the numeral | `1` | `(A[x = x̂_j] + B T(x))/(A + B)` |
//! | the result's place `j`, `x` ending it (`N`) | `T(x)/T(N)`, the glyph after it | `(A[j = ℓ] + B T(N))/(A + B)`, the numeral's end |
//!
//! `T` is the byte tree's face, `x̂` the consequence's numeral of `ℓ` glyphs in the left operand's
//! base. So **the result cells, digits and end together** multiply their sheet parts to
//! `A_final + B_final ≥ P(holds)` on a holding result: `N` holding results cost at most
//! `2N − log₂ C(2N, N)` bits (`ArithmeticContract.holds_sheet_telescope`, atlas `code.holds-sheet`),
//! whatever their length, and the chart parts are the byte tree's own on the cells around them.
//!
//! [definition] **The receipt** of each closed expression ([`ExpressionReceipt`]): the key the port
//! read, the result read, and under each living pairing key its producer, weight, consequence (digit
//! word and carry words), numeral, value and factorization, the consumer square
//! `decode_b(T_native(encode_b a, encode_b c)) = T(a, c)` read back from the numeral's glyphs and its
//! rebase through the other declared bases, the sheet's prior and its two contributions (**each
//! family's contribution**, holds and free), and the fibre of admitted producers whose consequence
//! on the same operands is the face read (`2 + 2`, `2 · 2`, `2 ^ 2`; atlas `arith.producer-jets`).
//! The carried producer is the operator glyph's key: this is the key-to-contribution relation
//! `receiver::population::provenance` lists as missing for a family-level mixture. The egg keeps the
//! last receipt only.
//!
//! [proved-derived; formal-checked] **Generation is egg packing** ([`ExpressionEgg::release`]; the
//! record's §5): a request read at the port to its awaited result releases each glyph of the
//! consequence's numeral by the certified draw at tolerance zero from its one-hot face
//! (`receiver::release::draw_exact`; Lean `Population.certified_draw_is_released_at_zero_tolerance`),
//! then the numeral's end from the stage face `{continues, ends}`. The release carries the key, the
//! carry words and the decoder (the base and its declaration glyphs), and the consumer square is
//! checked at release on the released glyphs. A pairing still plural whose keys' consequences part
//! is held, never forced.
//!
//! [definition] The computational object is the helical pair interaction: the operands' digit words
//! join at the pair port (pointwise for `+`, by convolution for `·`) and each place's wheel carries
//! its winding (`holarchy::terrain::arithmetic::{carry_cascade, digit_product}`, through
//! `geometry::winding::Odometer`). Of the winding guide's six general objects this owner touches the
//! **helix** (each place's wheel and its carry), the **pair** (the operands' pair port) and **faces
//! and placement** (the numeral face, its start and its end); the **cell holonomy**, the **tube**
//! (the stream, one expression a line) and the **tower thread** (the declared bases' restrictions)
//! stay attached.

use std::collections::BTreeSet;

use num_bigint::BigUint;
use num_traits::{One, Zero};

use super::super::{
    Act, Declaration, Family, KeyReadout, Likelihood, PopulationError, Readout, TreeFamily, Work,
    refuse,
};
use crate::compression::landmark::context::PassageCode;
use crate::holarchy::terrain::arithmetic::{
    BASES, Consequence, Factorization, Operator, Producer, decode, digit_of, encode, numeral,
    prefix, prefixed, read_numeral,
};
use crate::ratio::Rat;
use crate::ratio::surprisal::factor_biguint;
use crate::receiver::release::{CertifiedDraw, ReleaseReturn, draw_exact};

/// [definition; agent-inferred] **The exponents the egg admits**: those whose power of two fits the
/// machine word, `e < 64`. A power past them is not computed; its expression is unreached.
pub const EXPONENTS: u64 = u64::BITS as u64;

/// [definition] **The glyph the declared set holds plural**: `^`, its pairing located per stream.
pub const PLURAL: Operator = Operator::Caret;

/// The byte chart: every cell is a glyph.
const BYTES: usize = 256;

// -------------------------------------------------------------------------------------------
// the numeral port

/// A numeral being read: a leading `0` whose base is undecided, a prefix awaiting its first digit,
/// or digits (most significant first) in a declared base.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Numeral {
    Zero,
    Prefix(u64),
    Digits { base: u64, digits: Vec<u64> },
}

/// What a glyph does to a numeral being read.
enum Reading {
    /// The glyph continues the numeral.
    Continues(Numeral),
    /// The numeral ends before the glyph: its base and word (least significant first, no zero at
    /// its top), or none when it ended at a bare prefix.
    Ends(Option<(u64, Vec<u64>)>),
}

impl Numeral {
    /// A numeral begins at a decimal digit glyph.
    fn start(glyph: u8) -> Option<Self> {
        match digit_of(glyph)? {
            0 => Some(Numeral::Zero),
            digit if digit < 10 => Some(Numeral::Digits {
                base: 10,
                digits: vec![digit],
            }),
            _ => None,
        }
    }

    /// The numeral read so far as a whole: its base and word; none at a bare prefix.
    fn whole(&self) -> Option<(u64, Vec<u64>)> {
        match self {
            Numeral::Zero => Some((10, Vec::new())),
            Numeral::Prefix(_) => None,
            Numeral::Digits { base, digits } => {
                let mut word: Vec<u64> = digits.iter().rev().copied().collect();
                while word.last() == Some(&0) {
                    word.pop();
                }
                Some((*base, word))
            }
        }
    }

    /// **The glyph read against the numeral** (the declared glyph set): after a lone `0`, a prefix
    /// letter declares the base and a decimal digit continues in base ten; after a prefix, a digit
    /// of its base; after digits, a digit of their base. Any other glyph ends the numeral.
    fn read(&self, glyph: u8) -> Reading {
        let digit = digit_of(glyph);
        match self {
            Numeral::Zero => match (prefixed(glyph), digit) {
                (Some(base), _) => Reading::Continues(Numeral::Prefix(base)),
                (None, Some(digit)) if digit < 10 => Reading::Continues(Numeral::Digits {
                    base: 10,
                    digits: vec![0, digit],
                }),
                _ => Reading::Ends(self.whole()),
            },
            Numeral::Prefix(base) => match digit {
                Some(digit) if digit < *base => Reading::Continues(Numeral::Digits {
                    base: *base,
                    digits: vec![digit],
                }),
                _ => Reading::Ends(None),
            },
            Numeral::Digits { base, digits } => match digit {
                Some(digit) if digit < *base => {
                    let mut digits = digits.clone();
                    digits.push(digit);
                    Reading::Continues(Numeral::Digits {
                        base: *base,
                        digits,
                    })
                }
                _ => Reading::Ends(self.whole()),
            },
        }
    }

    /// Whether the glyph ends the numeral ([`Self::read`]'s `Ends`).
    fn ends_at(&self, glyph: u8) -> bool {
        let digit = digit_of(glyph);
        match self {
            Numeral::Zero => prefixed(glyph).is_none() && digit.is_none_or(|digit| digit >= 10),
            Numeral::Prefix(base) | Numeral::Digits { base, .. } => {
                digit.is_none_or(|digit| digit >= *base)
            }
        }
    }
}

/// [definition] **An operand the port read**: its declared base and its digit word, least
/// significant first with no zero at its top.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Operand {
    pub base: u64,
    pub word: Vec<u64>,
}

impl Operand {
    /// Its value.
    pub fn value(&self) -> BigUint {
        decode(self.base, &self.word)
    }
}

/// [definition] **An expression's key as the port read it** (module header): the two operands and
/// the operator glyph.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ExpressionKey {
    pub left: Operand,
    pub operator: Operator,
    pub right: Operand,
}

/// [definition] **The numeral port's phase** (module header): outside an expression, operand 1 at
/// its `place`-th glyph, the operator awaited, operand 2 awaited or at its `place`-th glyph, the
/// relation awaited, the result awaited, or the result's `place` glyphs read.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ExpressionPhase {
    Outside,
    Left { place: usize },
    Operator,
    BeforeRight,
    Right { place: usize },
    Relation,
    Awaiting,
    Result { place: usize },
}

/// [definition] **What a cell did to the port**: nothing to a keyed expression, the key read whole
/// (at the relation glyph), the result's numeral ended (whole, or at a bare prefix), or a keyed
/// expression dropped before its result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PortEvent {
    None,
    Keyed,
    Closed { result: Option<Operand> },
    Broken,
}

/// Whether a glyph belongs to an identifier: a numeral cannot begin after one (Rust's `u64`).
fn identifier(glyph: Option<u8>) -> bool {
    matches!(glyph, Some(b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'_'))
}

/// [definition; agent-inferred] **Whether a numeral may begin after the two glyphs before it**:
/// not after an identifier glyph, and not after a digit and a separator `,` (the tail of a separated
/// numeral, `1,000`, is not a numeral of its own; `_` is an identifier glyph already). Revised for
/// every chart on the acceptance run's failure branch: without it the port read `1,000 + 1 = 1,001`
/// as `000 + 1 = 1`.
fn begins(before: Option<u8>, last: Option<u8>) -> bool {
    let separated = last == Some(b',') && before.is_some_and(|glyph| glyph.is_ascii_digit());
    !(identifier(last) || separated)
}

/// [definition; agent-inferred] **The numeral port** (module header): a keystone of one key read
/// from the coded past through the declared glyph set.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExpressionPort {
    phase: ExpressionPhase,
    numeral: Option<Numeral>,
    left: Option<Operand>,
    operator: Option<Operator>,
    pending: Vec<u8>,
    right: Option<Operand>,
    equals: u8,
    before: Option<u8>,
    last: Option<u8>,
}

impl Default for ExpressionPort {
    fn default() -> Self {
        Self::new()
    }
}

impl ExpressionPort {
    /// The port outside any expression.
    pub fn new() -> Self {
        Self {
            phase: ExpressionPhase::Outside,
            numeral: None,
            left: None,
            operator: None,
            pending: Vec::new(),
            right: None,
            equals: 0,
            before: None,
            last: None,
        }
    }

    /// The phase the next cell meets.
    pub fn phase(&self) -> ExpressionPhase {
        self.phase
    }

    /// **The expression's key**, once the relation is read (the result awaited or being read).
    pub fn key(&self) -> Option<ExpressionKey> {
        match self.phase {
            ExpressionPhase::Awaiting | ExpressionPhase::Result { .. } => Some(ExpressionKey {
                left: self.left.clone()?,
                operator: self.operator?,
                right: self.right.clone()?,
            }),
            _ => None,
        }
    }

    /// Whether the glyph begins the result's numeral while the result is awaited.
    fn starts(&self, glyph: u8) -> bool {
        self.phase == ExpressionPhase::Awaiting && Numeral::start(glyph).is_some()
    }

    /// Whether the glyph ends the result's numeral while it is being read.
    fn ends(&self, glyph: u8) -> bool {
        matches!(self.phase, ExpressionPhase::Result { .. })
            && self
                .numeral
                .as_ref()
                .is_some_and(|numeral| numeral.ends_at(glyph))
    }

    /// The glyphs that continue the numeral being read.
    fn continuing(&self) -> Vec<u8> {
        match &self.numeral {
            Some(numeral) => (0..=u8::MAX)
                .filter(|&glyph| !numeral.ends_at(glyph))
                .collect(),
            None => Vec::new(),
        }
    }

    fn outside(&mut self) {
        self.phase = ExpressionPhase::Outside;
        self.numeral = None;
        self.left = None;
        self.operator = None;
        self.pending.clear();
        self.right = None;
        self.equals = 0;
    }

    /// One glyph read in the current phase; true when it is to be read again in the phase it
    /// opened.
    fn step(&mut self, glyph: u8, event: &mut PortEvent) -> bool {
        let space = glyph == b' ';
        match self.phase {
            ExpressionPhase::Outside => {
                if begins(self.before, self.last)
                    && let Some(numeral) = Numeral::start(glyph)
                {
                    self.numeral = Some(numeral);
                    self.phase = ExpressionPhase::Left { place: 1 };
                }
                false
            }
            ExpressionPhase::Left { place } | ExpressionPhase::Right { place } => {
                let left = matches!(self.phase, ExpressionPhase::Left { .. });
                let numeral = self.numeral.take().expect("a numeral being read");
                match numeral.read(glyph) {
                    Reading::Continues(numeral) => {
                        self.numeral = Some(numeral);
                        let place = place + 1;
                        self.phase = if left {
                            ExpressionPhase::Left { place }
                        } else {
                            ExpressionPhase::Right { place }
                        };
                        false
                    }
                    Reading::Ends(Some((base, word))) => {
                        let operand = Some(Operand { base, word });
                        if left {
                            self.left = operand;
                            self.phase = ExpressionPhase::Operator;
                        } else {
                            self.right = operand;
                            self.phase = ExpressionPhase::Relation;
                        }
                        true
                    }
                    Reading::Ends(None) => {
                        self.outside();
                        true
                    }
                }
            }
            ExpressionPhase::Operator => {
                if space && self.pending.is_empty() {
                    return false;
                }
                self.pending.push(glyph);
                let whole = Operator::ALL
                    .iter()
                    .find(|operator| operator.glyphs() == self.pending.as_slice());
                if let Some(&operator) = whole {
                    self.operator = Some(operator);
                    self.pending.clear();
                    self.phase = ExpressionPhase::BeforeRight;
                    return false;
                }
                let partial = Operator::ALL
                    .iter()
                    .any(|operator| operator.glyphs().starts_with(&self.pending));
                if !partial {
                    self.outside();
                    return true;
                }
                false
            }
            ExpressionPhase::BeforeRight => {
                if space {
                    return false;
                }
                match Numeral::start(glyph) {
                    Some(numeral) => {
                        self.numeral = Some(numeral);
                        self.phase = ExpressionPhase::Right { place: 1 };
                        false
                    }
                    None => {
                        self.outside();
                        true
                    }
                }
            }
            ExpressionPhase::Relation => {
                if glyph == b'=' {
                    self.equals = 1;
                    self.phase = ExpressionPhase::Awaiting;
                    *event = PortEvent::Keyed;
                    false
                } else if space {
                    false
                } else {
                    self.outside();
                    true
                }
            }
            ExpressionPhase::Awaiting => {
                if glyph == b'=' && self.equals == 1 {
                    self.equals = 2;
                    false
                } else if let Some(numeral) = Numeral::start(glyph) {
                    self.numeral = Some(numeral);
                    self.phase = ExpressionPhase::Result { place: 1 };
                    false
                } else if space {
                    false
                } else {
                    *event = PortEvent::Broken;
                    self.outside();
                    true
                }
            }
            ExpressionPhase::Result { place } => {
                let numeral = self.numeral.take().expect("a result being read");
                match numeral.read(glyph) {
                    Reading::Continues(numeral) => {
                        self.numeral = Some(numeral);
                        self.phase = ExpressionPhase::Result { place: place + 1 };
                        false
                    }
                    Reading::Ends(whole) => {
                        *event = PortEvent::Closed {
                            result: whole.map(|(base, word)| Operand { base, word }),
                        };
                        self.outside();
                        true
                    }
                }
            }
        }
    }

    /// **Advance by one received cell** (module header): a byte read as a glyph, a glyph that ends
    /// a numeral read again in the phase its end opens; a cell past the bytes closes a result being
    /// read, breaks a keyed expression and leaves the port outside.
    pub fn advance(&mut self, cell: usize) -> PortEvent {
        let mut event = PortEvent::None;
        let Ok(glyph) = u8::try_from(cell) else {
            event = match self.phase {
                ExpressionPhase::Result { .. } => PortEvent::Closed {
                    result: self
                        .numeral
                        .as_ref()
                        .and_then(Numeral::whole)
                        .map(|(base, word)| Operand { base, word }),
                },
                ExpressionPhase::Awaiting => PortEvent::Broken,
                _ => PortEvent::None,
            };
            self.outside();
            (self.before, self.last) = (None, None);
            return event;
        };
        while self.step(glyph, &mut event) {}
        (self.before, self.last) = (self.last, Some(glyph));
        event
    }
}

// -------------------------------------------------------------------------------------------
// the pairing and the holds sheet

/// [definition] **A pairing key's death** (module header): the expression whose results parted the
/// keys, the producers whose consequences held, the dead key's consequence value and the result read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairingDeath {
    pub key: ExpressionKey,
    pub held: Vec<Producer>,
    pub value: Option<BigUint>,
    pub read: Option<BigUint>,
}

/// [definition] **A key of the plural glyph's pairing** (module header): its producer, its exact
/// weight, its holds sheet's counts (expressions held and not) and its death.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairingKey {
    pub producer: Producer,
    pub weight: Rat,
    pub held: u64,
    pub free: u64,
    pub death: Option<PairingDeath>,
}

impl PairingKey {
    /// **The holds sheet's prior** at the next expression (module header): the
    /// Krichevsky–Trofimov face `(2h + 1)/(2n + 2)`.
    pub fn prior(&self) -> Rat {
        let (held, total) = (self.held, self.held + self.free);
        Rat::new((2 * held + 1).into(), (2 * total + 2).into())
    }
}

/// One living key's holds sheet over an open expression: its producer, consequence and numeral,
/// its prior and weight at the key, and its holds and free contributions so far.
#[derive(Clone, Debug)]
struct Sheet {
    producer: Producer,
    consequence: Option<Consequence>,
    glyphs: Vec<u8>,
    prior: Rat,
    weight: Rat,
    holds: Rat,
    free: Rat,
}

/// The open expression: its key and each pairing key's sheet (none for a dead key).
#[derive(Clone, Debug)]
struct Open {
    key: ExpressionKey,
    sheets: Vec<Option<Sheet>>,
}

/// The producer a pairing key's operator glyph wears: the glyph's one producer, or the key's own
/// for the plural glyph.
fn producer_of(operator: Operator, paired: Producer) -> Producer {
    match operator.producers() {
        [one] => *one,
        _ => paired,
    }
}

/// **The consequence the egg computes** for a key: in the left operand's base, each operand's value
/// re-encoded there; none for a power past [`EXPONENTS`] or a refused term.
fn consequence_of(producer: Producer, key: &ExpressionKey) -> Option<Consequence> {
    let base = key.left.base;
    if producer == Producer::Power && key.right.value() >= BigUint::from(EXPONENTS) {
        return None;
    }
    let left = encode(base, &key.left.value()).ok()?;
    let right = encode(base, &key.right.value()).ok()?;
    producer.consequence(base, &left, &right).ok()
}

/// **Whether a producer's `T` on the operands is `face`**, exactly: the power by repeated products
/// that stop once they pass the face.
fn produces(producer: Producer, left: &BigUint, right: &BigUint, face: &BigUint) -> bool {
    match producer {
        Producer::Power => {
            if left.is_zero() || left.is_one() {
                let value = if left.is_zero() && !right.is_zero() {
                    BigUint::zero()
                } else {
                    BigUint::one()
                };
                return &value == face;
            }
            let mut value = BigUint::one();
            let mut count = BigUint::zero();
            while &count < right {
                value *= left;
                count += 1u32;
                if &value > face {
                    return false;
                }
            }
            &value == face
        }
        _ => producer
            .scalar(left, right)
            .is_ok_and(|value| &value == face),
    }
}

/// **The square and its rebase** (module header): the numeral's glyphs read back are `T(a, c)`, and
/// the consequence computed in every other declared base has the same value.
fn square(producer: Producer, key: &ExpressionKey, glyphs: &[u8]) -> (bool, bool) {
    let (a, c) = (key.left.value(), key.right.value());
    let Ok(value) = producer.scalar(&a, &c) else {
        return (false, false);
    };
    let square = read_numeral(glyphs) == Some((key.left.base, value.clone()));
    let rebase = BASES
        .iter()
        .filter(|&&base| base != key.left.base)
        .all(|&base| {
            let (Ok(left), Ok(right)) = (encode(base, &a), encode(base, &c)) else {
                return false;
            };
            producer
                .consequence(base, &left, &right)
                .is_ok_and(|consequence| consequence.value() == value)
        });
    (square, rebase)
}

fn factored(value: &BigUint) -> Option<Factorization> {
    if value.is_zero() {
        return None;
    }
    factor_biguint(value).ok()
}

// -------------------------------------------------------------------------------------------
// the receipts

/// [definition] **A pairing key's reading of a closed expression** (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KeyReading {
    pub key: usize,
    pub producer: Producer,
    /// The key's weight at the expression's key.
    pub weight: Rat,
    pub consequence: Option<Consequence>,
    /// The consequence's numeral.
    pub glyphs: Vec<u8>,
    pub value: Option<BigUint>,
    pub factorization: Option<Factorization>,
    /// `decode_b(T_native(encode_b a, encode_b c)) = T(a, c)`, read back from the numeral.
    pub square: bool,
    /// The same consequence computed in every other declared base.
    pub rebase: bool,
    /// The holds sheet's prior at the key.
    pub prior: Rat,
    /// The holds contribution `P(holds) L_holds` over the result cells.
    pub holds: Rat,
    /// The free contribution `P(free) L_free` over the result cells.
    pub free: Rat,
    pub held: bool,
}

/// [definition] **A closed expression's receipt** (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExpressionReceipt {
    pub key: ExpressionKey,
    /// The result's numeral as read (none at a bare prefix).
    pub result: Option<Operand>,
    /// Each pairing key living at the key.
    pub readings: Vec<KeyReading>,
    /// The admitted producers (the sum, the product and the living keys' of the plural glyph)
    /// whose consequence on the operands is the result read.
    pub fibre: Vec<Producer>,
    /// The pairing keys this expression killed.
    pub deaths: Vec<Producer>,
}

/// [definition] **A received cell's reading** (module header): the phase it met, the egg's face,
/// the byte tree's own face, and the face's chart and sheet parts (`face = chart · sheet`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CellReading {
    pub phase: ExpressionPhase,
    pub face: Rat,
    pub tree: Rat,
    pub chart: Rat,
    pub sheet: Rat,
}

/// [definition] **The egg's counts** (never a record of cells): expressions keyed, closed, broken
/// before a result, unreached (closed with no consequence computed), held under a living key,
/// failed under every key that computed; squares and rebases checked over the keys that computed;
/// consequences computed.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExpressionCounts {
    pub keyed: u64,
    pub closed: u64,
    pub broken: u64,
    pub unreached: u64,
    pub held: u64,
    pub failed: u64,
    pub squares: u64,
    pub square_failures: u64,
    pub rebases: u64,
    pub rebase_failures: u64,
    pub consequences: u64,
}

// -------------------------------------------------------------------------------------------
// the egg

/// A cell's parts under the open expression: the chart part, the free key's sheet factor `t`, and
/// each living key's holds factor `h` (none outside the result, where every factor is one).
struct Parts {
    chart: Rat,
    free: Rat,
    holds: Option<Vec<Option<Rat>>>,
}

/// [definition; agent-inferred] **The expression egg** (module header): the numeral port ⊳ the
/// plural glyph's pairing ⊳ the holds sheet over the byte tree.
#[derive(Clone)]
pub struct ExpressionEgg {
    label: String,
    description: u64,
    tree: TreeFamily,
    port: ExpressionPort,
    pairing: Vec<PairingKey>,
    open: Option<Open>,
    passage: PassageCode,
    last: Option<CellReading>,
    receipt: Option<ExpressionReceipt>,
    counts: ExpressionCounts,
}

impl ExpressionEgg {
    /// **The egg over a byte tree** (its alphabet the 256 bytes), the plural glyph's pairing uniform
    /// over its admitted producers.
    pub fn new(description: u64, tree: TreeFamily) -> Result<Self, PopulationError> {
        if tree.alphabet() != BYTES {
            return Err(refuse(
                "an expression egg",
                "its byte tree reads the 256 bytes, every cell a glyph",
            ));
        }
        let producers = PLURAL.producers();
        let weight = Rat::new(1.into(), (producers.len() as u64).into());
        let label = format!(
            "expression egg: the numeral port ⊳ the `^` pairing {{{}}} ⊳ the holds sheet over the byte tree ({})",
            producers
                .iter()
                .map(|producer| producer.name())
                .collect::<Vec<_>>()
                .join(", "),
            tree.label()
        );
        Ok(Self {
            label,
            description,
            tree,
            port: ExpressionPort::new(),
            pairing: producers
                .iter()
                .map(|&producer| PairingKey {
                    producer,
                    weight: weight.clone(),
                    held: 0,
                    free: 0,
                    death: None,
                })
                .collect(),
            open: None,
            passage: PassageCode::new(),
            last: None,
            receipt: None,
            counts: ExpressionCounts::default(),
        })
    }

    /// The numeral port.
    pub fn port(&self) -> &ExpressionPort {
        &self.port
    }

    /// The plural glyph's pairing keys, living and dead.
    pub fn pairing(&self) -> &[PairingKey] {
        &self.pairing
    }

    /// **The located producer of the plural glyph**: the one living key's, once one is left.
    pub fn located(&self) -> Option<Producer> {
        let mut living = self.pairing.iter().filter(|key| key.death.is_none());
        match (living.next(), living.next()) {
            (Some(key), None) => Some(key.producer),
            _ => None,
        }
    }

    /// The last received cell's reading.
    pub fn last(&self) -> Option<&CellReading> {
        self.last.as_ref()
    }

    /// The last closed expression's receipt.
    pub fn receipt(&self) -> Option<&ExpressionReceipt> {
        self.receipt.as_ref()
    }

    /// The egg's counts.
    pub fn counts(&self) -> &ExpressionCounts {
        &self.counts
    }

    /// The byte tree (its own faces are the egg's reading without the port).
    pub fn byte_tree(&self) -> &TreeFamily {
        &self.tree
    }

    /// **The stage masses** of the byte tree's face: `T(S)` of the numeral's start while the result is
    /// awaited, `T(N)` of its end while it is being read (none elsewhere).
    fn stages(&self, vector: &[Rat]) -> Option<Rat> {
        self.open.as_ref()?;
        match self.port.phase() {
            ExpressionPhase::Awaiting => Some(
                (b'0'..=b'9')
                    .map(|glyph| vector[usize::from(glyph)].clone())
                    .sum(),
            ),
            ExpressionPhase::Result { .. } => Some(
                Rat::one()
                    - self
                        .port
                        .continuing()
                        .into_iter()
                        .map(|glyph| vector[usize::from(glyph)].clone())
                        .sum::<Rat>(),
            ),
            _ => None,
        }
    }

    /// **A cell's parts** (module header's table), read at the port's phase before the cell; the
    /// stage mass ([`Self::stages`]) is read where the start or the end needs it.
    fn parts(&self, glyph: u8, tree: &Rat, stage: Option<&Rat>) -> Parts {
        let outside = Parts {
            chart: tree.clone(),
            free: Rat::one(),
            holds: None,
        };
        let Some(open) = &self.open else {
            return outside;
        };
        let mass = || stage.expect("the stage's mass").clone();
        let each = |holds: &dyn Fn(&Sheet) -> bool| -> Vec<Option<Rat>> {
            open.sheets
                .iter()
                .map(|sheet| {
                    sheet.as_ref().map(|sheet| {
                        if holds(sheet) {
                            Rat::one()
                        } else {
                            Rat::zero()
                        }
                    })
                })
                .collect()
        };
        if self.port.starts(glyph) {
            let start = mass();
            return Parts {
                chart: start.clone(),
                free: tree / &start,
                holds: Some(each(&|sheet| sheet.glyphs.first() == Some(&glyph))),
            };
        }
        let ExpressionPhase::Result { place } = self.port.phase() else {
            return outside;
        };
        if self.port.ends(glyph) {
            let end = mass();
            return Parts {
                chart: tree / &end,
                free: end,
                holds: Some(each(&|sheet| sheet.glyphs.len() == place)),
            };
        }
        Parts {
            chart: Rat::one(),
            free: tree.clone(),
            holds: Some(each(&|sheet| sheet.glyphs.get(place) == Some(&glyph))),
        }
    }

    /// The pairing's sheet part of a cell and each living key's: `s_k = (A h + B t)/(A + B)`, mixed
    /// by the keys' weights.
    fn sheet(&self, parts: &Parts) -> (Rat, Vec<Option<Rat>>) {
        let (Some(open), Some(holds)) = (&self.open, &parts.holds) else {
            return (Rat::one(), Vec::new());
        };
        let each: Vec<Option<Rat>> = open
            .sheets
            .iter()
            .zip(holds)
            .map(|(sheet, h)| {
                let (sheet, h) = (sheet.as_ref()?, h.as_ref()?);
                Some((&sheet.holds * h + &sheet.free * &parts.free) / (&sheet.holds + &sheet.free))
            })
            .collect();
        let mixed = self
            .pairing
            .iter()
            .zip(&each)
            .filter_map(|(key, s)| s.as_ref().map(|s| &key.weight * s))
            .sum();
        (mixed, each)
    }

    /// **The key read whole** (module header): each living key's sheet opened at its prior.
    fn key(&mut self) {
        let Some(key) = self.port.key() else {
            return;
        };
        self.counts.keyed += 1;
        let mut computed = 0;
        let sheets = self
            .pairing
            .iter()
            .map(|paired| {
                if paired.death.is_some() {
                    return None;
                }
                let producer = producer_of(key.operator, paired.producer);
                let consequence = consequence_of(producer, &key);
                let glyphs = consequence
                    .as_ref()
                    .and_then(|consequence| numeral(consequence.base, &consequence.digits).ok())
                    .unwrap_or_default();
                let prior = paired.prior();
                let (holds, free) = if consequence.is_some() {
                    computed += 1;
                    (prior.clone(), Rat::one() - &prior)
                } else {
                    (Rat::zero(), Rat::one())
                };
                Some(Sheet {
                    producer,
                    consequence,
                    glyphs,
                    prior,
                    weight: paired.weight.clone(),
                    holds,
                    free,
                })
            })
            .collect();
        self.counts.consequences += computed;
        self.open = Some(Open { key, sheets });
    }

    /// **The expression closed** (module header): each key's sheet tallied, the pairing's failed
    /// keys killed where another held, the receipt returned.
    fn close(&mut self, result: Option<Operand>) {
        let Some(open) = self.open.take() else {
            return;
        };
        self.counts.closed += 1;
        let read = result.as_ref().map(Operand::value);
        let mut readings = Vec::new();
        let (mut computing, mut holding) = (Vec::new(), Vec::new());
        for (index, sheet) in open.sheets.iter().enumerate() {
            let Some(sheet) = sheet else {
                continue;
            };
            let held = sheet.consequence.is_some() && !sheet.holds.is_zero();
            let (mut checked, mut rebased) = (false, false);
            if sheet.consequence.is_some() {
                computing.push(index);
                if held {
                    holding.push(index);
                    self.pairing[index].held += 1;
                } else {
                    self.pairing[index].free += 1;
                }
                (checked, rebased) = square(sheet.producer, &open.key, &sheet.glyphs);
                self.counts.squares += u64::from(checked);
                self.counts.square_failures += u64::from(!checked);
                self.counts.rebases += u64::from(rebased);
                self.counts.rebase_failures += u64::from(!rebased);
            }
            let value = sheet.consequence.as_ref().map(Consequence::value);
            readings.push(KeyReading {
                key: index,
                producer: sheet.producer,
                weight: sheet.weight.clone(),
                consequence: sheet.consequence.clone(),
                glyphs: sheet.glyphs.clone(),
                factorization: value.as_ref().and_then(factored),
                value,
                square: checked,
                rebase: rebased,
                prior: sheet.prior.clone(),
                holds: sheet.holds.clone(),
                free: sheet.free.clone(),
                held,
            });
        }
        if computing.is_empty() {
            self.counts.unreached += 1;
        } else if holding.is_empty() {
            self.counts.failed += 1;
        } else {
            self.counts.held += 1;
        }
        let mut deaths = Vec::new();
        let living: Vec<usize> = (0..open.sheets.len())
            .filter(|&index| open.sheets[index].is_some())
            .collect();
        if !holding.is_empty() && holding.len() < living.len() {
            let held: Vec<Producer> = holding
                .iter()
                .map(|&index| self.pairing[index].producer)
                .collect();
            for &index in living.iter().filter(|index| !holding.contains(index)) {
                let sheet = open.sheets[index]
                    .as_ref()
                    .expect("a computing key's sheet");
                let key = &mut self.pairing[index];
                key.death = Some(PairingDeath {
                    key: open.key.clone(),
                    held: held.clone(),
                    value: sheet.consequence.as_ref().map(Consequence::value),
                    read: read.clone(),
                });
                key.weight = Rat::zero();
                deaths.push(key.producer);
            }
            let total: Rat = self.pairing.iter().map(|key| key.weight.clone()).sum();
            for key in &mut self.pairing {
                key.weight = &key.weight / &total;
            }
        }
        let (a, c) = (open.key.left.value(), open.key.right.value());
        let mut admitted: BTreeSet<Producer> = BTreeSet::new();
        for operator in Operator::ALL {
            for &producer in operator.producers() {
                let living = operator != PLURAL
                    || living
                        .iter()
                        .any(|&index| self.pairing[index].producer == producer);
                if living {
                    admitted.insert(producer);
                }
            }
        }
        let fibre = match &read {
            Some(face) => admitted
                .into_iter()
                .filter(|&producer| produces(producer, &a, &c, face))
                .collect(),
            None => Vec::new(),
        };
        self.receipt = Some(ExpressionReceipt {
            key: open.key,
            result,
            readings,
            fibre,
            deaths,
        });
    }

    /// **A request released as egg packing** (module header): the request's cells read at a copy of
    /// the port to its awaited result; each glyph of the living keys' one consequence released by
    /// the certified draw at tolerance zero from its one-hot face under the declared key
    /// `keys[j]`, then the numeral's end from the stage face `{continues, ends}` under
    /// `keys[ℓ]`; the square checked on the released glyphs. A pairing whose living keys'
    /// consequences part is held. Refused unless the request reaches the awaited result, some key
    /// computes its consequence, and a key is declared for each glyph and the end.
    pub fn release(
        &self,
        request: &[usize],
        keys: &[Rat],
    ) -> Result<ExpressionRelease, PopulationError> {
        let mut port = self.port.clone();
        for &cell in request {
            port.advance(cell);
        }
        let key = port
            .key()
            .filter(|_| port.phase() == ExpressionPhase::Awaiting)
            .ok_or_else(|| {
                refuse(
                    "a request",
                    "it reads to the result awaited at the numeral port",
                )
            })?;
        let mut outcomes: Vec<(Producer, Consequence, Vec<u8>)> = Vec::new();
        for paired in self.pairing.iter().filter(|key| key.death.is_none()) {
            let producer = producer_of(key.operator, paired.producer);
            if outcomes.iter().any(|(known, _, _)| *known == producer) {
                continue;
            }
            if let Some(consequence) = consequence_of(producer, &key) {
                let glyphs = numeral(consequence.base, &consequence.digits)?;
                outcomes.push((producer, consequence, glyphs));
            }
        }
        let Some((producer, consequence, glyphs)) = outcomes.first().cloned() else {
            return Err(refuse("a request", "a living key computes its consequence"));
        };
        if outcomes.iter().any(|(_, _, other)| *other != glyphs) {
            return Ok(ExpressionRelease::Hold {
                key,
                producers: outcomes.iter().map(|(producer, _, _)| *producer).collect(),
            });
        }
        if keys.len() <= glyphs.len() {
            return Err(refuse(
                "a release's keys",
                "one is declared for each glyph and one for the end",
            ));
        }
        let drawn = |face: &[Rat],
                     key: &Rat,
                     class: usize|
         -> Result<CertifiedDraw, PopulationError> {
            match draw_exact(face, key) {
                Ok(ReleaseReturn::Drawn(certified)) if certified.class == class => Ok(certified),
                _ => Err(refuse(
                    "a certified draw of a released glyph",
                    "a one-hot exact face releases its class under every key in [0, 1)",
                )),
            }
        };
        let mut draws = Vec::with_capacity(glyphs.len());
        for (glyph, key) in glyphs.iter().zip(keys) {
            let mut face = vec![Rat::zero(); BYTES];
            face[usize::from(*glyph)] = Rat::one();
            draws.push(drawn(&face, key, usize::from(*glyph))?);
        }
        let end = drawn(&[Rat::zero(), Rat::one()], &keys[glyphs.len()], 1)?;
        let released: Vec<u8> = draws.iter().map(|draw| draw.class as u8).collect();
        let (checked, rebased) = square(producer, &key, &released);
        let value = consequence.value();
        Ok(ExpressionRelease::Released(Box::new(ReleasedResult {
            prefix: prefix(consequence.base)?.to_vec(),
            factorization: factored(&value),
            key,
            producer,
            glyphs: released,
            draws,
            end,
            consequence,
            value,
            square: checked,
            rebase: rebased,
        })))
    }
}

/// [definition] **A released result** (module header): the key the request was read to, the
/// producer its operator glyph wears under the living pairing, the released glyphs with each
/// certified draw and the end's, the consequence (digit word and carry words), its value and
/// factorization, the decoder's declaration glyphs, and the square and its rebase checked at release.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReleasedResult {
    pub key: ExpressionKey,
    pub producer: Producer,
    pub glyphs: Vec<u8>,
    pub draws: Vec<CertifiedDraw>,
    pub end: CertifiedDraw,
    pub consequence: Consequence,
    pub value: BigUint,
    pub factorization: Option<Factorization>,
    pub prefix: Vec<u8>,
    pub square: bool,
    pub rebase: bool,
}

/// [definition] **A request's release** (module header): released, or held while the plural
/// glyph's living keys' consequences part.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExpressionRelease {
    Released(Box<ReleasedResult>),
    Hold {
        key: ExpressionKey,
        producers: Vec<Producer>,
    },
}

impl Family for ExpressionEgg {
    fn branch_future(&self) -> Option<Box<dyn Family>> {
        Some(Box::new(self.clone()))
    }

    fn label(&self) -> String {
        self.label.clone()
    }

    fn alphabet(&self) -> usize {
        BYTES
    }

    fn description(&self) -> u64 {
        self.description
    }

    /// `q(x) = c(x) · Σ_k W_k s_k(x)` over the bytes, exact.
    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        let vector = self.tree.face()?;
        let stage = self.stages(&vector);
        Ok((0..BYTES)
            .map(|cell| {
                let parts = self.parts(cell as u8, &vector[cell], stage.as_ref());
                &parts.chart * &self.sheet(&parts).0
            })
            .collect())
    }

    /// **Receive one cell** (module header): its parts at the port's phase, the byte tree's face
    /// and deposit, the sheet's and the pairing's Bayes moves; then the port advances, opening a
    /// key's sheets at the relation and closing them at the result's end.
    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        if cell >= BYTES {
            return Err(PopulationError::CellOutside {
                cell,
                alphabet: BYTES,
            });
        }
        let glyph = cell as u8;
        let phase = self.port.phase();
        let staged = self.open.is_some() && (self.port.starts(glyph) || self.port.ends(glyph));
        let stage = if staged {
            self.stages(&self.tree.face()?)
        } else {
            None
        };
        let tree = self.tree.receive(cell)?;
        let parts = self.parts(glyph, &tree, stage.as_ref());
        let (sheet, each) = self.sheet(&parts);
        let face = &parts.chart * &sheet;
        if let (Some(open), Some(holds)) = (&mut self.open, &parts.holds) {
            for ((slot, h), (key, s)) in open
                .sheets
                .iter_mut()
                .zip(holds)
                .zip(self.pairing.iter_mut().zip(&each))
            {
                let (Some(open), Some(h), Some(s)) = (slot.as_mut(), h, s) else {
                    continue;
                };
                open.holds = &open.holds * h;
                open.free = &open.free * &parts.free;
                key.weight = &key.weight * s / &sheet;
            }
        }
        self.passage.face(&face)?;
        self.last = Some(CellReading {
            phase,
            face: face.clone(),
            tree,
            chart: parts.chart,
            sheet,
        });
        match self.port.advance(cell) {
            PortEvent::Keyed => self.key(),
            PortEvent::Closed { result } => self.close(result),
            PortEvent::Broken => {
                if self.open.take().is_some() {
                    self.counts.broken += 1;
                }
            }
            PortEvent::None => {}
        }
        Ok(face)
    }

    fn admits(&self, cells: &[usize]) -> Result<(), PopulationError> {
        self.tree.admits(cells)
    }

    fn likelihood(&self) -> Likelihood {
        Likelihood::Enclosed(self.passage)
    }

    /// The pairing's living keys and their weights (its one factor).
    fn readout(&self) -> Readout<'_> {
        let living: Vec<(usize, &PairingKey)> = self
            .pairing
            .iter()
            .enumerate()
            .filter(|(_, key)| key.death.is_none())
            .collect();
        Readout::Keys(KeyReadout {
            spaces: vec![self.pairing.len() as u64],
            survivors: vec![
                living
                    .iter()
                    .map(|(index, _)| vec![*index as u64])
                    .collect(),
            ],
            masses: vec![living.iter().map(|(_, key)| key.weight.clone()).collect()],
            dormant: Vec::new(),
        })
    }

    /// The admitted exponents, the port's declared bases, the pairing's producers and the byte
    /// tree's declaration.
    fn declaration(&self) -> Declaration {
        Declaration::new("expression egg", vec![EXPONENTS]).with(vec![
            Declaration::new("numeral port", BASES.to_vec()),
            Declaration::new(
                "glyph pairing",
                PLURAL
                    .producers()
                    .iter()
                    .map(|&producer| producer as u64)
                    .collect(),
            ),
            self.tree.declaration(),
        ])
    }

    /// The byte tree's deposits and nodes, and the consequences computed.
    fn work(&self) -> Work {
        let mut work = self.tree.work();
        work.add(Act::Product, self.counts.consequences);
        work
    }
}

#[cfg(test)]
#[path = "expressions_tests.rs"]
mod tests;
