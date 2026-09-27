//! **Products: `a ⊗ c = a·c` as digit cells, with the convolution, the carry and the two exact
//! faces** (the record's §7.1 and §7.2).
//!
//! [definition; agent-inferred] **The layout** ([`ProductFamily`]). Each record is `a ⊗ c = P ;`:
//! the `L` digit cells of `a`, the mark `⊗` (cell `b`), the `L` digit cells of `c`, the mark `=`
//! (cell `b + 1`), the `2L` digit cells of `P = a·c` and the record mark `;` (cell `b + 2`), each
//! word zero-padded to its declared length and emitted in the declared order ([`DigitOrder`]). The
//! alphabet is `b + 3` and a record is `4L + 3` cells. The operands are drawn uniformly on
//! `[0, b^L)` by the seeded draw ([`Products::draw`]), so each operand cell carries `log₂ b` bits
//! and a record's operands `2L log₂ b` ([`ProductFamily::operand_code`], the key description
//! `⌈log₂ b^(2L)⌉`); every other cell is determined by the cells before it.
//!
//! [proved-derived; implemented-exact] **The truth** ([`ProductTruth`]) of each record, with `k`
//! the declared face width and `s = L − k`:
//! - the operands and their factorizations;
//! - the digit product ([`super::digit_product`]): the convolution before carry (`2L − 1` places),
//!   the carry word and the product's digit word (Lean `RadixWindowReceiver`
//!   `digit_product_is_carry_of_convolution`, `carry_step_value`, `carried_word_is_product_digits`);
//! - **the trailing face** `P mod b^k = (a mod b^k)(c mod b^k) mod b^k`: the residue map is a ring
//!   homomorphism (Mathlib `Nat.mul_mod`), so the product's `k` least significant cells are
//!   determined by the operands' `k` least significant digits: the carry flows up, never down;
//! - **the leading face** ([`LeadingFace`]): the operands' first `k` digits `A = ⌊a/b^s⌋` and
//!   `C = ⌊c/b^s⌋` confine the product to the exact interval
//!   `[A C b^(2s), ((A + 1) b^s − 1)((C + 1) b^s − 1)]`, and its first `k` digits `⌊P/b^(2L−k)⌋`
//!   to the **carry fibre**, the readings of that interval's two ends: the unread lower places carry
//!   into the leading face, so it is multiplicative only up to that fibre (the float's mantissa;
//!   the grain reading `carry + phase/L + ε` is this face).
//!
//! [definition] **The cell classes** ([`ProductCell`]): the operand cells (drawn), the marks, and
//! the product's trailing `k`, middle `2L − 2k` and leading `k` cells, read by significance in
//! either order. **The record span** `4L + 2` ([`ProductFamily::record_span`]): at that depth every
//! determined cell's context holds the whole record before it and the previous record's mark, so
//! the cells before it determine it. It is a sufficient depth, the receipt's control; the least
//! such depth can be smaller (in the least-first order the product's lower digits, once read, with
//! the operands' upper digits fix the rest), and none is claimed.

use num_bigint::BigUint;

use super::super::{Draw, TerrainError, refuse};
use super::{
    DigitOrder, DigitProduct, Factorization, check_base, checked_power, digit_product, digits,
    factorization,
};
use crate::compression::cost::ceil_log2;
use crate::ratio::Rat;
use crate::ratio::surprisal::SymbolicSurprisal;

/// [definition] **The declared product family** (module header): base `b`, `L` digits an
/// operand, the face width `k` (`1 ≤ k ≤ L`) and the digit order. `b^(2L)` must fit a machine
/// word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProductFamily {
    pub base: u64,
    pub digits: usize,
    pub face: usize,
    pub order: DigitOrder,
}

/// [definition] **A cell's class** (module header).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ProductCell {
    Operand,
    Mark,
    Trailing,
    Middle,
    Leading,
}

impl ProductFamily {
    fn check(&self) -> Result<(), TerrainError> {
        check_base(self.base)?;
        if self.digits == 0 || self.face == 0 || self.face > self.digits {
            return Err(refuse("a product family", "it needs 1 ≤ k ≤ L digits"));
        }
        checked_power(self.base, 2 * self.digits)?;
        Ok(())
    }

    /// `b^L`: the operands' range.
    pub fn operands(&self) -> Result<u64, TerrainError> {
        self.check()?;
        checked_power(self.base, self.digits)
    }

    /// The mark `⊗`, cell `b`.
    pub fn times(&self) -> usize {
        self.base as usize
    }

    /// The mark `=`, cell `b + 1`.
    pub fn equals(&self) -> usize {
        self.base as usize + 1
    }

    /// The record mark `;`, cell `b + 2`.
    pub fn record_mark(&self) -> usize {
        self.base as usize + 2
    }

    /// The alphabet `b + 3`.
    pub fn alphabet(&self) -> usize {
        self.base as usize + 3
    }

    /// A record's cells, `4L + 3`.
    pub fn record_length(&self) -> usize {
        4 * self.digits + 3
    }

    /// **The record span** `4L + 2` (module header): a sufficient depth, the receipt's control.
    pub fn record_span(&self) -> usize {
        4 * self.digits + 2
    }

    /// **The class of the cell at `offset` of a record** (module header).
    pub fn class(&self, offset: usize) -> ProductCell {
        let l = self.digits;
        match offset % self.record_length() {
            o if o < l || (l + 1..2 * l + 1).contains(&o) => ProductCell::Operand,
            o if (2 * l + 2..4 * l + 2).contains(&o) => {
                let place = self.order.place(o - (2 * l + 2), 2 * l);
                if place < self.face {
                    ProductCell::Trailing
                } else if place >= 2 * l - self.face {
                    ProductCell::Leading
                } else {
                    ProductCell::Middle
                }
            }
            _ => ProductCell::Mark,
        }
    }

    /// **A record's operand code** `2L log₂ b` bits, exactly: the operands are uniform on
    /// `[0, b^L)²`.
    pub fn operand_code(&self) -> Result<SymbolicSurprisal, TerrainError> {
        let base = Rat::from_integer(self.base.into());
        Ok(SymbolicSurprisal::log2_of_ratio(&base)?
            .scaled(&Rat::from_integer((2 * self.digits as u64).into())))
    }

    /// **A record's key description** `⌈log₂ b^(2L)⌉` bits.
    pub fn key_bits(&self) -> Result<u64, TerrainError> {
        self.check()?;
        Ok(ceil_log2(
            &BigUint::from(self.base).pow(2 * self.digits as u32),
        ))
    }
}

/// [definition] **The leading face with its carry fibre** (module header): the operands' first
/// `k` digits `(A, C)`, the exact interval of products consistent with them, the first `k` digits
/// of that interval's ends (the fibre) and the product's own first `k` digits.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeadingFace {
    pub operands: (u64, u64),
    pub products: (u64, u64),
    pub fibre: (u64, u64),
    pub reading: u64,
}

impl LeadingFace {
    /// The fibre's width: the number of leading readings consistent with the operands' leading
    /// faces (one when the leading face is determined by them).
    pub fn width(&self) -> u64 {
        self.fibre.1 - self.fibre.0 + 1
    }
}

/// [definition] **A record's exact truth receipt** (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProductTruth {
    pub operands: (u64, u64),
    pub factorizations: (Option<Factorization>, Option<Factorization>),
    pub product: DigitProduct,
    pub value: u64,
    pub trailing: u64,
    pub leading: LeadingFace,
}

impl ProductTruth {
    /// **The truth of the record `a ⊗ c`** under the family (module header); refused when an
    /// operand lies outside `[0, b^L)`.
    pub fn of(family: &ProductFamily, left: u64, right: u64) -> Result<Self, TerrainError> {
        let range = family.operands()?;
        if left >= range || right >= range {
            return Err(refuse(
                "a product record",
                "its operands lie outside [0, b^L)",
            ));
        }
        let (b, l, k) = (family.base, family.digits, family.face);
        let product = digit_product(b, &digits(left, b, l)?, &digits(right, b, l)?)?;
        let value = left * right;
        let modulus = checked_power(b, k)?;
        let shift = checked_power(b, l - k)?;
        let top = checked_power(b, 2 * l - k)?;
        let (a, c) = (left / shift, right / shift);
        let products = (
            a * c * shift * shift,
            ((a + 1) * shift - 1) * ((c + 1) * shift - 1),
        );
        Ok(Self {
            operands: (left, right),
            factorizations: (factorization(left), factorization(right)),
            product,
            value,
            trailing: value % modulus,
            leading: LeadingFace {
                operands: (a, c),
                products,
                fibre: (products.0 / top, products.1 / top),
                reading: value / top,
            },
        })
    }
}

/// [definition] **The products terrain** (module header): its family and its records' operands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Products {
    family: ProductFamily,
    pairs: Vec<(u64, u64)>,
}

impl Products {
    /// The declared records; refused when the family is malformed or an operand lies outside
    /// `[0, b^L)`.
    pub fn new(family: ProductFamily, pairs: Vec<(u64, u64)>) -> Result<Self, TerrainError> {
        let range = family.operands()?;
        if pairs.iter().any(|(a, c)| *a >= range || *c >= range) {
            return Err(refuse(
                "a product record",
                "its operands lie outside [0, b^L)",
            ));
        }
        Ok(Self { family, pairs })
    }

    /// **`records` records drawn from the family** (module header): each operand uniform on
    /// `[0, b^L)`, the left first.
    pub fn draw(
        family: &ProductFamily,
        records: usize,
        draw: &mut Draw,
    ) -> Result<Self, TerrainError> {
        let range = usize::try_from(family.operands()?)
            .map_err(|_| refuse("a product family", "b^L exceeds the address space"))?;
        let pairs = (0..records)
            .map(|_| (draw.below(range) as u64, draw.below(range) as u64))
            .collect();
        Self::new(family.clone(), pairs)
    }

    pub fn family(&self) -> &ProductFamily {
        &self.family
    }

    pub fn pairs(&self) -> &[(u64, u64)] {
        &self.pairs
    }

    /// **The cells** (module header): every record `a ⊗ c = P ;` in the declared order.
    pub fn emit(&self) -> Vec<usize> {
        let (b, l, order) = (self.family.base, self.family.digits, self.family.order);
        let word = |value: u64, length: usize| {
            order
                .arrange(&digits(value, b, length).expect("a declared operand fits its word"))
                .into_iter()
                .map(|digit| digit as usize)
        };
        let mut cells = Vec::with_capacity(self.pairs.len() * self.family.record_length());
        for &(a, c) in &self.pairs {
            cells.extend(word(a, l));
            cells.push(self.family.times());
            cells.extend(word(c, l));
            cells.push(self.family.equals());
            cells.extend(word(a * c, 2 * l));
            cells.push(self.family.record_mark());
        }
        cells
    }

    /// **Each cell's class** (module header), in emission order.
    pub fn classes(&self) -> Vec<ProductCell> {
        (0..self.pairs.len() * self.family.record_length())
            .map(|position| self.family.class(position))
            .collect()
    }

    /// **The records' exact truths** (module header).
    pub fn truth(&self) -> Result<Vec<ProductTruth>, TerrainError> {
        self.pairs
            .iter()
            .map(|&(a, c)| ProductTruth::of(&self.family, a, c))
            .collect()
    }
}
