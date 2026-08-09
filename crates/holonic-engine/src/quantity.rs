//! A quantity carries its dimension, and `c` is a declared cast rather than an erased one.
//!
//! Measured 2026-08-09: `speed_of_light|lightspeed|SPEED_OF_LIGHT|c_squared` has **zero
//! occurrences** anywhere under `crates/` or `soma/`, and no type carries a physical dimension —
//! every "dimension" in the tree is geometric. So every quantity is a bare `Rat` and the cast has
//! been performed implicitly everywhere and erased. That is the float defect one level up: a float
//! keeps the magnitude and deletes the residual; a dimensionless exact rational keeps the magnitude
//! and deletes the unit.
//!
//! ## A dimension is a vector, and the base units are the caller's
//!
//! There is no enum of named units in this module and no `(M, L, T)` anywhere in it. A caller
//! declares its own [`BaseUnits`] and every [`Dimension`] is an exponent word over exactly those.
//! `M`, `L`, `T` appear only in the tests below and in `examples/the_shorthand_is_one_angle.rs`,
//! where they are a **declared fixture**.
//!
//! ## Why the exponent group is over `Rat` and not `i32`
//!
//! **There is no theorem forcing integer exponents**, and pinning one would be exactly the authored
//! level `CLAUDE.md` §8 convicts. The free abelian group `Z^k` is a *subgroup* of the `Q`-vector
//! space `Q^k`; taking `Q` is the unrestricted carrier and `Z` is the restriction that must justify
//! itself. Three reasons it cannot:
//!
//! - **`Z` refuses the square root.** `sqrt(x) = x^(2^-1)`, and §2b makes the half-turn the object
//!   the whole signed floor is about. The geometric mean of a length and a time has dimension
//!   `L^(1/2) T^(1/2)`, which is not in `Z^k` at all. A dimension carrier that cannot take a square
//!   root has deleted the exact operation this project convicts deletion of.
//! - **Buckingham's theorem is a statement over a field.** `n - rank(M)` and `ker M` are rank and
//!   kernel, and a kernel basis is only determined up to `Q`-linear recombination either way.
//! - **The `Z` structure is not thrown away, it is *read off*.** [`Dimension::integral`] returns the
//!   integer word when there is one, [`PiGroup::primitive`] normalises a rational group to a
//!   primitive integer word with a fixed sign, and [`PiGroups::invariant_factors`] carries the Smith
//!   invariant factors of the integral rescaling — an invariant factor above one is a dimension the
//!   declared quantities reach **only in a multiple**, which is the `ReachableOnlyInMultiple` shape
//!   `CLAUDE.md` §11 already models.
//!
//! ## The refusals, and what shape each takes
//!
//! - **Addition and subtraction refuse by type**, returning [`QuantityError::DimensionMismatch`]
//!   naming *both* dimensions. Never a runtime bool.
//! - **Comparison returns [`ExactOrdering::Open`]** on mismatched dimension. Two quantities of
//!   different dimension are not *unequal*; the question has no answer inside the declared receiver
//!   family, and `Open` is the carrier this tree already owns for exactly that
//!   (`exact_value.rs:72`).
//! - **A bare `Rat` is only readable off a dimensionless quantity** ([`Quantity::rational`]) or
//!   against a declared unit ([`Quantity::measured_in`]). There is no accessor that hands out the
//!   magnitude alone. That is the erasure made unavailable at the API boundary.
//!
//! ## `c` is a declared cast and has no default
//!
//! [`Cast`] is a *declared* quantity whose dimension is non-trivial, and applying it returns a
//! [`CastApplication`] carrying the cast, the power, and both dimensions — so a chart change cannot
//! happen without appearing in the return. **There is no `Default` impl in this module**, and
//! [`Cast::declare`] refuses a dimensionless cast by name
//! ([`QuantityError::CastErasesTheDimension`]).
//!
//! The distinction that refusal draws is the load-bearing one: **the erasure is dimensional, not
//! numerical.** Choosing units in which `c` has *value* `1` is a lawful choice of units and this
//! module permits it. Declaring `c` to have *no dimension* is the erasure, and it is refused.
//!
//! And the erasure has an exact certificate. [`PiGroups::undetectable_base_rescalings`] is a basis
//! of the **left** kernel of the dimension matrix: a rescaling of the declared base units that no
//! declared quantity can detect. For `(E, m, c, p)` over `(M, L, T)` it is one-dimensional and
//! spanned by `(0, 1, 1)` — rescaling length and time together. *That* is what "set `c = 1`" is,
//! computed rather than conventional, and its dimension is `k - rank`, so it says exactly how much
//! of the declared base the material cannot see.
//!
//! ## Buckingham pi, over three existing organs and no fourth
//!
//! ```text
//!   independent dimensionless groups = n - rank(M)          the groups = a basis of ker M
//! ```
//!
//! - **rank and kernel**: `inverse_transport::ExactAffineVersionFiber`, whose `validate` at
//!   `inverse_transport.rs:337` *enforces* full reduced row echelon form — unit pivot, zeros left of
//!   it, strictly increasing pivots, and no other row nonzero in a pivot column. A kernel basis
//!   reads straight off that.
//! - **an independent rank**: `rebase_invariants::smith_normal_form` on an integral column
//!   rescaling. Column scaling is an invertible diagonal rebase, so the rank is unmoved. The two
//!   ranks are **required to agree** and [`QuantityError::RankDisagreement`] fires when they do not.
//!   A third reading, `rank(M^T)`, is taken by the same elimination on the transpose.
//! - **the annihilation certificate**: `exact_linear::ExactRatMatrix::apply`, which is asked to
//!   return the zero word for every returned group. It is not asserted; it is computed.
//!
//! `smith_normal_form` **cannot** supply the kernel — `SmithNormalForm` is
//! `{ factors: Vec<BigInt> }` and nothing else (`rebase_invariants.rs:223`), so no transformation
//! matrix leaves it — and `matroid_chow.rs:788 null_space` is a **private** `fn`, callable from
//! neither this module nor any driver. The RREF carrier is the one that is both public enough and
//! shaped right.

use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::fmt;

use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use relational_geometry::{Rat, format_rat};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact_linear::ExactRatMatrix;
use crate::exact_value::ExactOrdering;
use crate::inverse_transport::ExactAffineVersionFiber;
use crate::rebase_invariants::{IntegerMatrix, PivotRule, smith_normal_form};

// ===============================================================================================
// the declared base

/// The base units a caller declares. Nothing in this module names a unit; this is where they enter.
///
/// Two dimensions are only composable when they were declared over the *same* base. That is not
/// pedantry: a dimension word is meaningless without the declaration it indexes, and silently
/// zipping two words of equal length from different declarations is the absolute-frame defect at
/// the smallest possible scale.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct BaseUnits {
    symbols: Vec<String>,
}

impl BaseUnits {
    /// Declare the base. Refuses an empty declaration, an empty symbol, and a repeated symbol.
    pub fn declare<I, S>(symbols: I) -> Result<Self, QuantityError>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let symbols: Vec<String> = symbols.into_iter().map(Into::into).collect();
        if symbols.is_empty() {
            return Err(QuantityError::NoBaseUnits);
        }
        let mut seen = BTreeSet::new();
        for symbol in &symbols {
            if symbol.trim().is_empty() {
                return Err(QuantityError::EmptyBaseUnitSymbol);
            }
            if !seen.insert(symbol.clone()) {
                return Err(QuantityError::DuplicateBaseUnit {
                    symbol: symbol.clone(),
                });
            }
        }
        Ok(Self { symbols })
    }

    pub fn arity(&self) -> usize {
        self.symbols.len()
    }

    pub fn symbols(&self) -> &[String] {
        &self.symbols
    }

    pub fn position(&self, symbol: &str) -> Option<usize> {
        self.symbols.iter().position(|present| present == symbol)
    }

    /// The identity of the group: every exponent zero.
    pub fn dimensionless(&self) -> Dimension {
        Dimension {
            base: self.clone(),
            exponents: vec![Rat::zero(); self.arity()],
        }
    }

    /// The generator named by `symbol`.
    pub fn unit(&self, symbol: &str) -> Result<Dimension, QuantityError> {
        let position = self
            .position(symbol)
            .ok_or_else(|| QuantityError::UnknownBaseUnit {
                symbol: symbol.to_owned(),
                declared: self.symbols.join(", "),
            })?;
        let mut exponents = vec![Rat::zero(); self.arity()];
        exponents[position] = Rat::one();
        Ok(Dimension {
            base: self.clone(),
            exponents,
        })
    }

    /// A dimension given as an exponent word in declaration order.
    pub fn dimension(&self, exponents: Vec<Rat>) -> Result<Dimension, QuantityError> {
        if exponents.len() != self.arity() {
            return Err(QuantityError::ExponentWordLength {
                expected: self.arity(),
                supplied: exponents.len(),
            });
        }
        Ok(Dimension {
            base: self.clone(),
            exponents,
        })
    }

    /// A dimension given as `(symbol, exponent)` terms. Repeated symbols accumulate.
    pub fn dimension_of(&self, terms: &[(&str, Rat)]) -> Result<Dimension, QuantityError> {
        let mut exponents = vec![Rat::zero(); self.arity()];
        for (symbol, exponent) in terms {
            let position =
                self.position(symbol)
                    .ok_or_else(|| QuantityError::UnknownBaseUnit {
                        symbol: (*symbol).to_owned(),
                        declared: self.symbols.join(", "),
                    })?;
            exponents[position] = &exponents[position] + exponent;
        }
        Ok(Dimension {
            base: self.clone(),
            exponents,
        })
    }

    /// The integer-exponent convenience, for a caller whose word happens to be integral.
    pub fn integer_dimension(&self, exponents: &[i64]) -> Result<Dimension, QuantityError> {
        self.dimension(
            exponents
                .iter()
                .map(|value| Rat::from_integer(BigInt::from(*value)))
                .collect(),
        )
    }
}

// ===============================================================================================
// the dimension

/// A vector in the free `Q`-module on the declared base units.
///
/// Multiplication of quantities **adds** these words; a rational power **scales** one. Addition of
/// quantities does neither: it requires the two words to be equal and refuses otherwise.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Dimension {
    base: BaseUnits,
    exponents: Vec<Rat>,
}

impl Dimension {
    pub fn base(&self) -> &BaseUnits {
        &self.base
    }

    pub fn exponents(&self) -> &[Rat] {
        &self.exponents
    }

    pub fn is_dimensionless(&self) -> bool {
        self.exponents.iter().all(Zero::is_zero)
    }

    fn require_same_base(&self, other: &Self) -> Result<(), QuantityError> {
        if self.base == other.base {
            return Ok(());
        }
        Err(QuantityError::IncomparableBaseUnits {
            left: self.base.symbols.join(", "),
            right: other.base.symbols.join(", "),
        })
    }

    /// The product of two dimensions: exponent words add.
    pub fn product(&self, other: &Self) -> Result<Self, QuantityError> {
        self.require_same_base(other)?;
        Ok(Self {
            base: self.base.clone(),
            exponents: self
                .exponents
                .iter()
                .zip(&other.exponents)
                .map(|(left, right)| left + right)
                .collect(),
        })
    }

    /// The ratio of two dimensions: exponent words subtract.
    pub fn ratio(&self, other: &Self) -> Result<Self, QuantityError> {
        self.require_same_base(other)?;
        Ok(Self {
            base: self.base.clone(),
            exponents: self
                .exponents
                .iter()
                .zip(&other.exponents)
                .map(|(left, right)| left - right)
                .collect(),
        })
    }

    /// A rational power: the exponent word scales. This is total — it is the *value* that can
    /// refuse a rational power, never the dimension.
    pub fn powed(&self, exponent: &Rat) -> Self {
        Self {
            base: self.base.clone(),
            exponents: self
                .exponents
                .iter()
                .map(|value| value * exponent)
                .collect(),
        }
    }

    pub fn inverted(&self) -> Self {
        self.powed(&-Rat::one())
    }

    /// The integer exponent word, when there is one. `None` says the dimension left `Z^k` — which
    /// is lawful and is why this carrier is over `Q`.
    pub fn integral(&self) -> Option<Vec<BigInt>> {
        self.exponents
            .iter()
            .map(|value| value.is_integer().then(|| value.to_integer()))
            .collect()
    }

    pub fn render(&self) -> String {
        let mut terms: Vec<String> = Vec::new();
        for (symbol, exponent) in self.base.symbols.iter().zip(&self.exponents) {
            if exponent.is_zero() {
                continue;
            }
            if exponent.is_one() {
                terms.push(symbol.clone());
            } else {
                terms.push(format!("{symbol}^{}", format_rat(exponent)));
            }
        }
        if terms.is_empty() {
            "1".to_owned()
        } else {
            terms.join(" ")
        }
    }
}

impl fmt::Display for Dimension {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.render())
    }
}

// ===============================================================================================
// the quantity

/// An exact magnitude that carries the dimension it is a magnitude *of*.
///
/// There is deliberately **no** accessor returning the magnitude alone. [`Quantity::rational`]
/// hands one out only when the dimension is trivial, [`Quantity::measured_in`] only against a
/// declared unit of the same dimension, and [`Quantity::parts`] hands the pair together so the two
/// cannot be separated by accident. A bare number is a number *of* something, and losing the
/// second half is the deletion this module exists to refuse.
///
/// **No `Default`.** A default quantity would have to invent both a magnitude and a base.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Quantity {
    value: Rat,
    dimension: Dimension,
}

impl Quantity {
    pub fn new(value: Rat, dimension: Dimension) -> Self {
        Self { value, dimension }
    }

    pub fn integer(value: i64, dimension: Dimension) -> Self {
        Self::new(Rat::from_integer(BigInt::from(value)), dimension)
    }

    pub fn dimensionless(value: Rat, base: &BaseUnits) -> Self {
        Self::new(value, base.dimensionless())
    }

    pub fn dimension(&self) -> &Dimension {
        &self.dimension
    }

    /// The magnitude and the dimension, together. The only unconditional reader, and it never
    /// hands out one without the other.
    pub fn parts(&self) -> (&Rat, &Dimension) {
        (&self.value, &self.dimension)
    }

    /// The magnitude as a bare rational — **only** when the dimension is trivial.
    pub fn rational(&self) -> Result<&Rat, QuantityError> {
        if self.dimension.is_dimensionless() {
            Ok(&self.value)
        } else {
            Err(QuantityError::NotDimensionless {
                dimension: self.dimension.render(),
            })
        }
    }

    /// This quantity's magnitude in units of `unit`. Exact, and refuses when `unit` carries a
    /// different dimension or has no magnitude.
    pub fn measured_in(&self, unit: &Self) -> Result<Rat, QuantityError> {
        self.dimension.require_same_base(&unit.dimension)?;
        if self.dimension != unit.dimension {
            return Err(QuantityError::DimensionMismatch {
                operation: "measurement",
                left: self.dimension.render(),
                right: unit.dimension.render(),
            });
        }
        if unit.value.is_zero() {
            return Err(QuantityError::DivisionByZero);
        }
        Ok(&self.value / &unit.value)
    }

    pub fn is_zero(&self) -> bool {
        self.value.is_zero()
    }

    /// Refuses on mismatched dimension, naming both. This is the type check, not a convention.
    pub fn sum(&self, other: &Self) -> Result<Self, QuantityError> {
        self.combine(other, "addition", true)
    }

    /// Refuses on mismatched dimension, naming both.
    pub fn difference(&self, other: &Self) -> Result<Self, QuantityError> {
        self.combine(other, "subtraction", false)
    }

    fn combine(&self, other: &Self, operation: &'static str, add: bool) -> Result<Self, QuantityError> {
        self.dimension.require_same_base(&other.dimension)?;
        if self.dimension != other.dimension {
            return Err(QuantityError::DimensionMismatch {
                operation,
                left: self.dimension.render(),
                right: other.dimension.render(),
            });
        }
        let value = if add {
            &self.value + &other.value
        } else {
            &self.value - &other.value
        };
        Ok(Self {
            value,
            dimension: self.dimension.clone(),
        })
    }

    /// Always lawful between quantities over one base: the exponent words add.
    pub fn product(&self, other: &Self) -> Result<Self, QuantityError> {
        Ok(Self {
            value: &self.value * &other.value,
            dimension: self.dimension.product(&other.dimension)?,
        })
    }

    /// The exponent words subtract. Refuses a zero divisor.
    pub fn ratio(&self, other: &Self) -> Result<Self, QuantityError> {
        if other.value.is_zero() {
            return Err(QuantityError::DivisionByZero);
        }
        Ok(Self {
            value: &self.value / &other.value,
            dimension: self.dimension.ratio(&other.dimension)?,
        })
    }

    /// A rational power. The dimension always scales; the **magnitude** refuses when the root it
    /// asks for is irrational, which is a typed refusal and never an approximation.
    pub fn powed(&self, exponent: &Rat) -> Result<Self, QuantityError> {
        Ok(Self {
            value: exact_rational_power(&self.value, exponent)?,
            dimension: self.dimension.powed(exponent),
        })
    }

    /// `Open` when the dimensions differ. Two quantities of different dimension are not unequal —
    /// the question has no answer inside the declared base, and `Open` is what says so.
    pub fn compare(&self, other: &Self) -> ExactOrdering {
        if self.dimension.base != other.dimension.base || self.dimension != other.dimension {
            return ExactOrdering::Open;
        }
        match self.value.cmp(&other.value) {
            Ordering::Less => ExactOrdering::Less,
            Ordering::Equal => ExactOrdering::Equal,
            Ordering::Greater => ExactOrdering::Greater,
        }
    }

    pub fn render(&self) -> String {
        format!("{} [{}]", format_rat(&self.value), self.dimension.render())
    }
}

impl fmt::Display for Quantity {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.render())
    }
}

// ===============================================================================================
// the cast

/// A declared cast between dimensions. `c` is one; nothing here names it.
///
/// A cast is a quantity with a **non-trivial** dimension. Applying it at a power is a chart change,
/// and it can only be obtained through a [`CastApplication`] that records which cast, at which
/// power, from which dimension to which.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Cast {
    symbol: String,
    quantity: Quantity,
}

impl Cast {
    /// Refuses a dimensionless cast by name. That refusal *is* the "`c = 1` must not be the
    /// default" rule, made checkable: a cast whose dimension is trivial performs no chart change,
    /// so declaring one is the erasure rather than a shorthand for it.
    ///
    /// A cast whose *magnitude* is one is fine and is a choice of units.
    pub fn declare(symbol: impl Into<String>, quantity: Quantity) -> Result<Self, QuantityError> {
        let symbol = symbol.into();
        if symbol.trim().is_empty() {
            return Err(QuantityError::EmptyCastSymbol);
        }
        if quantity.dimension.is_dimensionless() {
            return Err(QuantityError::CastErasesTheDimension { symbol });
        }
        if quantity.value.is_zero() {
            return Err(QuantityError::CastHasNoMagnitude { symbol });
        }
        Ok(Self { symbol, quantity })
    }

    pub fn symbol(&self) -> &str {
        &self.symbol
    }

    pub fn quantity(&self) -> &Quantity {
        &self.quantity
    }

    pub fn dimension(&self) -> &Dimension {
        &self.quantity.dimension
    }

    /// `subject * cast^power`, with the chart change carried in the return.
    pub fn apply(&self, subject: &Quantity, power: &Rat) -> Result<CastApplication, QuantityError> {
        let raised = self.quantity.powed(power)?;
        let returned = subject.product(&raised)?;
        Ok(CastApplication {
            cast: self.symbol.clone(),
            power: power.clone(),
            from: subject.dimension.clone(),
            to: returned.dimension.clone(),
            returned,
        })
    }
}

/// What a cast did, returned rather than performed silently.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CastApplication {
    pub cast: String,
    pub power: Rat,
    pub from: Dimension,
    pub to: Dimension,
    pub returned: Quantity,
}

impl CastApplication {
    /// True when the cast moved nothing. A caller seeing this has performed a chart change that
    /// was not one.
    pub fn is_inert(&self) -> bool {
        self.from == self.to
    }

    pub fn render(&self) -> String {
        format!(
            "{}^{}  :  [{}] -> [{}]   returning {}",
            self.cast,
            format_rat(&self.power),
            self.from.render(),
            self.to.render(),
            self.returned.render()
        )
    }
}

// ===============================================================================================
// the dimension matrix and Buckingham pi

/// `k x n`: one row per declared base unit, one column per declared quantity.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionMatrix {
    base: BaseUnits,
    names: Vec<String>,
    columns: Vec<Dimension>,
}

impl DimensionMatrix {
    /// Refuses an empty column list, a repeated quantity name, and a column declared over a
    /// different base.
    pub fn declare(
        base: BaseUnits,
        columns: Vec<(String, Dimension)>,
    ) -> Result<Self, QuantityError> {
        if columns.is_empty() {
            return Err(QuantityError::NoQuantities);
        }
        let mut seen = BTreeSet::new();
        let mut names = Vec::with_capacity(columns.len());
        let mut dimensions = Vec::with_capacity(columns.len());
        for (name, dimension) in columns {
            if name.trim().is_empty() {
                return Err(QuantityError::EmptyQuantityName);
            }
            if !seen.insert(name.clone()) {
                return Err(QuantityError::DuplicateQuantityName { name });
            }
            if dimension.base != base {
                return Err(QuantityError::IncomparableBaseUnits {
                    left: base.symbols.join(", "),
                    right: dimension.base.symbols.join(", "),
                });
            }
            names.push(name);
            dimensions.push(dimension);
        }
        Ok(Self {
            base,
            names,
            columns: dimensions,
        })
    }

    pub fn base(&self) -> &BaseUnits {
        &self.base
    }

    pub fn names(&self) -> &[String] {
        &self.names
    }

    pub fn dimensions(&self) -> &[Dimension] {
        &self.columns
    }

    /// `n`, the number of declared quantities.
    pub fn extent(&self) -> usize {
        self.columns.len()
    }

    /// `k`, the number of declared base units.
    pub fn base_extent(&self) -> usize {
        self.base.arity()
    }

    pub fn entry(&self, unit: usize, quantity: usize) -> Option<&Rat> {
        self.columns.get(quantity)?.exponents.get(unit)
    }

    /// The `k` rows, each of length `n`.
    pub fn rows(&self) -> Vec<Vec<Rat>> {
        (0..self.base_extent())
            .map(|unit| {
                self.columns
                    .iter()
                    .map(|dimension| dimension.exponents[unit].clone())
                    .collect()
            })
            .collect()
    }

    pub fn as_exact_matrix(&self) -> Result<ExactRatMatrix, QuantityError> {
        ExactRatMatrix::new(self.rows())
            .map_err(|error| QuantityError::ExactLinear(error.to_string()))
    }

    pub fn render(&self) -> String {
        let mut lines = Vec::new();
        let width = self
            .names
            .iter()
            .map(String::len)
            .chain([5])
            .max()
            .unwrap_or(5)
            .max(5);
        let unit_width = self
            .base
            .symbols
            .iter()
            .map(String::len)
            .max()
            .unwrap_or(1)
            .max(1);
        let header: Vec<String> = self
            .names
            .iter()
            .map(|name| format!("{name:>width$}"))
            .collect();
        lines.push(format!(
            "{:unit_width$}  {}",
            "",
            header.join("  "),
            unit_width = unit_width
        ));
        for (unit, symbol) in self.base.symbols.iter().enumerate() {
            let row: Vec<String> = self
                .columns
                .iter()
                .map(|dimension| format!("{:>width$}", format_rat(&dimension.exponents[unit])))
                .collect();
            lines.push(format!(
                "{symbol:unit_width$}  {}",
                row.join("  "),
                unit_width = unit_width
            ));
        }
        lines.join("\n")
    }

    /// The Buckingham pi return: the rank three ways, the count, the kernel basis, the left kernel,
    /// and the integral invariant factors.
    pub fn buckingham(&self) -> Result<PiGroups, QuantityError> {
        let extent = self.extent();
        let base_extent = self.base_extent();
        let rows = self.rows();

        // The right kernel: the pi-groups themselves.
        let right = eliminate(&rows, extent)?;

        // The left kernel: base-unit rescalings no declared quantity can detect.
        let transposed: Vec<Vec<Rat>> = self
            .columns
            .iter()
            .map(|dimension| dimension.exponents.clone())
            .collect();
        let left = eliminate(&transposed, base_extent)?;

        if right.rank != left.rank {
            return Err(QuantityError::RankDisagreement {
                by_elimination: right.rank,
                by_transpose: left.rank,
                by_smith_normal_form: right.rank,
            });
        }

        // The independent reading. Column scaling by a positive integer is an invertible diagonal
        // rebase, so it moves neither rank nor the kernel's dimension.
        let (integral, column_scales) = self.integral_rescaling()?;
        let smith = smith_normal_form(&integral, PivotRule::SmallestMagnitude);
        if smith.rank() != right.rank {
            return Err(QuantityError::RankDisagreement {
                by_elimination: right.rank,
                by_transpose: left.rank,
                by_smith_normal_form: smith.rank(),
            });
        }

        let matrix = self.as_exact_matrix()?;
        let basis: Vec<PiGroup> = right
            .kernel
            .iter()
            .map(|word| PiGroup {
                exponents: word.clone(),
            })
            .collect();
        for group in &basis {
            let image = matrix
                .apply(&group.exponents)
                .map_err(|error| QuantityError::ExactLinear(error.to_string()))?;
            if !image.iter().all(Zero::is_zero) {
                return Err(QuantityError::KernelDoesNotAnnihilate {
                    group: group.render(&self.names),
                });
            }
        }
        let primitive_basis: Vec<PiGroup> = basis.iter().map(PiGroup::primitive).collect();
        for group in &primitive_basis {
            let image = matrix
                .apply(&group.exponents)
                .map_err(|error| QuantityError::ExactLinear(error.to_string()))?;
            if !image.iter().all(Zero::is_zero) {
                return Err(QuantityError::KernelDoesNotAnnihilate {
                    group: group.render(&self.names),
                });
            }
        }

        Ok(PiGroups {
            quantities: self.names.clone(),
            base_units: self.base.symbols.clone(),
            rank: right.rank,
            rank_by_smith_normal_form: smith.rank(),
            rank_by_transpose: left.rank,
            independent_group_count: extent - right.rank,
            free_positions: right.free.clone(),
            basis,
            primitive_basis,
            undetectable_rescaling_count: base_extent - left.rank,
            undetectable_base_rescalings: left.kernel,
            invariant_factors: smith.factors,
            column_scales,
            eliminations: right.eliminations.saturating_add(left.eliminations),
        })
    }

    /// `M * D` for a positive diagonal `D` clearing every column's denominators, plus that diagonal.
    fn integral_rescaling(&self) -> Result<(IntegerMatrix, Vec<BigInt>), QuantityError> {
        let mut scales = Vec::with_capacity(self.extent());
        for dimension in &self.columns {
            let mut scale = BigInt::one();
            for exponent in &dimension.exponents {
                scale = integer_lcm(&scale, exponent.denom());
            }
            scales.push(scale);
        }
        let mut matrix = IntegerMatrix::zeros(self.base_extent(), self.extent());
        for (quantity, dimension) in self.columns.iter().enumerate() {
            for (unit, exponent) in dimension.exponents.iter().enumerate() {
                let scaled = exponent * Rat::from_integer(scales[quantity].clone());
                if !scaled.is_integer() {
                    return Err(QuantityError::IntegralRescalingFailed {
                        quantity: self.names[quantity].clone(),
                    });
                }
                matrix.set(unit, quantity, scaled.to_integer());
            }
        }
        Ok((matrix, scales))
    }
}

/// One dimensionless group: an exponent word over the declared quantities.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PiGroup {
    pub exponents: Vec<Rat>,
}

impl PiGroup {
    pub fn new(exponents: Vec<Rat>) -> Self {
        Self { exponents }
    }

    /// The primitive integer word with a fixed sign: denominators cleared, content removed, first
    /// nonzero made positive. Scaling a group by a nonzero rational leaves it a group, so this is a
    /// choice of representative and never a change of content.
    ///
    /// `exact_value::canonical_homogeneous` does the same normalisation and cannot be reused: it is
    /// const-generic over `[Rat; N]` and the arity here is a runtime declaration.
    pub fn primitive(&self) -> Self {
        if self.exponents.iter().all(Zero::is_zero) {
            return self.clone();
        }
        let mut scale = BigInt::one();
        for exponent in &self.exponents {
            scale = integer_lcm(&scale, exponent.denom());
        }
        let mut integral: Vec<BigInt> = self
            .exponents
            .iter()
            .map(|exponent| exponent.numer() * (&scale / exponent.denom()))
            .collect();
        let content = integral
            .iter()
            .filter(|value| !value.is_zero())
            .map(Signed::abs)
            .reduce(|left, right| integer_gcd(&left, &right))
            .unwrap_or_else(BigInt::one);
        if !content.is_zero() {
            for value in &mut integral {
                *value /= &content;
            }
        }
        if integral
            .iter()
            .find(|value| !value.is_zero())
            .is_some_and(Signed::is_negative)
        {
            for value in &mut integral {
                *value = -value.clone();
            }
        }
        Self {
            exponents: integral.into_iter().map(Rat::from_integer).collect(),
        }
    }

    pub fn negated(&self) -> Self {
        Self {
            exponents: self.exponents.iter().map(|value| -value.clone()).collect(),
        }
    }

    /// The product `prod values[i]^exponents[i]`, which must come out dimensionless.
    ///
    /// This can refuse, and both refusals are content: a non-integral exponent asks for a root the
    /// magnitude may not have, and a zero magnitude under a negative exponent says the group has
    /// left the chart at that point.
    pub fn evaluate(&self, values: &[Quantity]) -> Result<Quantity, QuantityError> {
        if values.len() != self.exponents.len() {
            return Err(QuantityError::ExponentWordLength {
                expected: self.exponents.len(),
                supplied: values.len(),
            });
        }
        let Some(first) = values.first() else {
            return Err(QuantityError::NoQuantities);
        };
        let mut product = Quantity::new(Rat::one(), first.dimension.base.dimensionless());
        for (value, exponent) in values.iter().zip(&self.exponents) {
            if exponent.is_zero() {
                continue;
            }
            product = product.product(&value.powed(exponent)?)?;
        }
        if !product.dimension.is_dimensionless() {
            return Err(QuantityError::NotDimensionless {
                dimension: product.dimension.render(),
            });
        }
        Ok(product)
    }

    pub fn render(&self, names: &[String]) -> String {
        let mut terms = Vec::new();
        for (name, exponent) in names.iter().zip(&self.exponents) {
            if exponent.is_zero() {
                continue;
            }
            if exponent.is_one() {
                terms.push(name.clone());
            } else {
                terms.push(format!("{name}^{}", format_rat(exponent)));
            }
        }
        if terms.is_empty() {
            "1".to_owned()
        } else {
            terms.join(" ")
        }
    }
}

/// What the Buckingham computation returned.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PiGroups {
    pub quantities: Vec<String>,
    pub base_units: Vec<String>,
    /// `rank(M)` by exact rational elimination.
    pub rank: usize,
    /// `rank(M)` again, by `smith_normal_form` on the integral rescaling. Independent, and required
    /// to agree.
    pub rank_by_smith_normal_form: usize,
    /// `rank(M^T)`, by the same elimination on the transpose. Row rank equals column rank; a third
    /// reading, also required to agree.
    pub rank_by_transpose: usize,
    /// `n - rank`. Buckingham's count.
    pub independent_group_count: usize,
    /// The free columns the kernel basis is indexed by. A receiver coordinate of the elimination,
    /// returned so a caller can expand a proposed group in this basis; never an invariant.
    pub free_positions: Vec<usize>,
    pub basis: Vec<PiGroup>,
    /// The same span, with each vector normalised to a primitive integer word.
    pub primitive_basis: Vec<PiGroup>,
    /// `k - rank`.
    pub undetectable_rescaling_count: usize,
    /// A basis of the **left** kernel: rescalings of the declared base units that no declared
    /// quantity can detect. Non-empty means the declared base is finer than the material can see.
    pub undetectable_base_rescalings: Vec<Vec<Rat>>,
    /// Smith invariant factors of the integral rescaling. A factor above one is a dimension the
    /// declared quantities reach only in a multiple.
    pub invariant_factors: Vec<BigInt>,
    /// The positive diagonal taken to reach `Z`. All one when every exponent was already integral.
    pub column_scales: Vec<BigInt>,
    /// Exact row eliminations performed. Work, never a clock.
    pub eliminations: u64,
}

impl PiGroups {
    /// The coordinates of `candidate` in [`PiGroups::basis`], or `None` when it is not in the span.
    ///
    /// This is the instrument that matters: a kernel basis is a **receiver coordinate** — two
    /// correct computations return different bases of the same kernel — so the invariant is
    /// membership in the span, not agreement of the words. Because the basis carries an identity
    /// block on [`PiGroups::free_positions`], the expansion is read off directly and then
    /// *verified* by reconstruction, so a candidate outside the span returns `None` rather than a
    /// wrong answer.
    pub fn coordinates_of(&self, candidate: &[Rat]) -> Option<Vec<Rat>> {
        let extent = self.quantities.len();
        if candidate.len() != extent {
            return None;
        }
        let coordinates: Vec<Rat> = self
            .free_positions
            .iter()
            .map(|position| candidate[*position].clone())
            .collect();
        let mut reconstructed = vec![Rat::zero(); extent];
        for (coordinate, group) in coordinates.iter().zip(&self.basis) {
            for (slot, exponent) in group.exponents.iter().enumerate() {
                reconstructed[slot] = &reconstructed[slot] + &(coordinate * exponent);
            }
        }
        (reconstructed == candidate).then_some(coordinates)
    }

    /// Whether a proposed group lies in the returned span.
    pub fn contains(&self, candidate: &[Rat]) -> bool {
        self.coordinates_of(candidate).is_some()
    }

    pub fn render_basis(&self) -> String {
        if self.basis.is_empty() {
            return "  (none — the dimension matrix has full column rank)".to_owned();
        }
        self.basis
            .iter()
            .zip(&self.primitive_basis)
            .enumerate()
            .map(|(ordinal, (group, primitive))| {
                format!(
                    "  pi_{ordinal}   {:<40}   primitive  {}",
                    group.render(&self.quantities),
                    primitive.render(&self.quantities)
                )
            })
            .collect::<Vec<String>>()
            .join("\n")
    }
}

// ===============================================================================================
// the elimination, over the tree's own reduced-row-echelon carrier

struct Elimination {
    rank: usize,
    free: Vec<usize>,
    kernel: Vec<Vec<Rat>>,
    eliminations: u64,
}

/// Rank and a kernel basis, by admitting each row into `ExactAffineVersionFiber` with a zero
/// response.
///
/// The carrier's `validate` enforces full RREF, so the standard read-off is exact: for each free
/// column `f`, the vector with `1` at `f` and `-row.coefficients[f]` at each pivot. A dependent row
/// admits with `rank_increased: false` rather than obstructing, because the response is zero.
fn eliminate(rows: &[Vec<Rat>], variables: usize) -> Result<Elimination, QuantityError> {
    let mut fiber = ExactAffineVersionFiber::new(variables)
        .map_err(|error| QuantityError::Elimination(error.to_string()))?;
    let mut eliminations = 0_u64;
    for row in rows {
        if row.len() != variables {
            return Err(QuantityError::ExponentWordLength {
                expected: variables,
                supplied: row.len(),
            });
        }
        let work = fiber
            .admit(row.clone(), Rat::zero())
            .map_err(|error| QuantityError::Elimination(error.to_string()))?;
        eliminations = eliminations.saturating_add(work.exact_row_eliminations);
    }
    let pivots: Vec<usize> = fiber.rows().iter().map(|row| row.pivot).collect();
    let free: Vec<usize> = (0..variables)
        .filter(|column| !pivots.contains(column))
        .collect();
    let kernel: Vec<Vec<Rat>> = free
        .iter()
        .map(|column| {
            let mut vector = vec![Rat::zero(); variables];
            vector[*column] = Rat::one();
            for row in fiber.rows() {
                vector[row.pivot] = -row.coefficients[*column].clone();
            }
            vector
        })
        .collect();
    Ok(Elimination {
        rank: fiber.rank(),
        free,
        kernel,
        eliminations,
    })
}

// ===============================================================================================
// exact integer arithmetic used above

fn integer_gcd(left: &BigInt, right: &BigInt) -> BigInt {
    let mut left = left.abs();
    let mut right = right.abs();
    while !right.is_zero() {
        let remainder = &left % &right;
        left = right;
        right = remainder;
    }
    left
}

fn integer_lcm(left: &BigInt, right: &BigInt) -> BigInt {
    if left.is_zero() || right.is_zero() {
        return BigInt::zero();
    }
    let divisor = integer_gcd(left, right);
    (left / &divisor * right).abs()
}

/// The exact integer `degree`-th root, or `None` when there is not one. Binary search on the
/// magnitude — no float, no `powf`, no tolerance.
fn exact_integer_root(value: &BigInt, degree: u32) -> Option<BigInt> {
    if degree == 0 {
        return None;
    }
    if degree == 1 {
        return Some(value.clone());
    }
    if value.is_zero() {
        return Some(BigInt::zero());
    }
    let negative = value.is_negative();
    if negative && degree.is_multiple_of(2) {
        return None;
    }
    let magnitude = value.abs();
    let mut low = BigInt::one();
    let mut high = magnitude.clone();
    let two = BigInt::from(2);
    while low <= high {
        let middle = (&low + &high) / &two;
        match middle.pow(degree).cmp(&magnitude) {
            Ordering::Equal => return Some(if negative { -middle } else { middle }),
            Ordering::Less => low = middle + BigInt::one(),
            Ordering::Greater => high = middle - BigInt::one(),
        }
    }
    None
}

/// `value^exponent` over `Q`, or a typed refusal. Never an approximation.
pub fn exact_rational_power(value: &Rat, exponent: &Rat) -> Result<Rat, QuantityError> {
    if exponent.is_zero() {
        if value.is_zero() {
            return Err(QuantityError::IndeterminatePower);
        }
        return Ok(Rat::one());
    }
    if value.is_zero() {
        return if exponent.is_negative() {
            Err(QuantityError::DivisionByZero)
        } else {
            Ok(Rat::zero())
        };
    }
    let degree = exponent
        .denom()
        .to_u32()
        .ok_or(QuantityError::ExponentOutsideCarrier)?;
    let power = exponent
        .numer()
        .abs()
        .to_u32()
        .ok_or(QuantityError::ExponentOutsideCarrier)?;
    let raised_numerator = value.numer().pow(power);
    let raised_denominator = value.denom().pow(power);
    let numerator = exact_integer_root(&raised_numerator, degree).ok_or_else(|| {
        QuantityError::NoRationalRoot {
            value: format_rat(value),
            exponent: format_rat(exponent),
        }
    })?;
    let denominator = exact_integer_root(&raised_denominator, degree).ok_or_else(|| {
        QuantityError::NoRationalRoot {
            value: format_rat(value),
            exponent: format_rat(exponent),
        }
    })?;
    let raised = Rat::new(numerator, denominator);
    if exponent.numer().is_negative() {
        if raised.is_zero() {
            return Err(QuantityError::DivisionByZero);
        }
        return Ok(Rat::one() / raised);
    }
    Ok(raised)
}

// ===============================================================================================
// the refusals

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum QuantityError {
    #[error("a base must be declared before any dimension exists")]
    NoBaseUnits,
    #[error("a base unit symbol cannot be empty")]
    EmptyBaseUnitSymbol,
    #[error("the base unit `{symbol}` is declared twice")]
    DuplicateBaseUnit { symbol: String },
    #[error("`{symbol}` is not a declared base unit; the declaration is ({declared})")]
    UnknownBaseUnit { symbol: String, declared: String },
    #[error("an exponent word of {expected} was expected and {supplied} were supplied")]
    ExponentWordLength { expected: usize, supplied: usize },
    #[error("dimensions declared over different bases do not compose: ({left}) against ({right})")]
    IncomparableBaseUnits { left: String, right: String },
    #[error("{operation} refuses: the left carries [{left}] and the right carries [{right}]")]
    DimensionMismatch {
        operation: &'static str,
        left: String,
        right: String,
    },
    #[error("a bare rational is not readable off a quantity carrying [{dimension}]")]
    NotDimensionless { dimension: String },
    #[error("division by a quantity with no magnitude")]
    DivisionByZero,
    #[error("zero to the zeroth power is not a value")]
    IndeterminatePower,
    #[error("the exponent lies outside the carrier this power is computed in")]
    ExponentOutsideCarrier,
    #[error("{value} to the power {exponent} has no rational value")]
    NoRationalRoot { value: String, exponent: String },
    #[error("the cast `{symbol}` carries no dimension, so declaring it erases the cast it names")]
    CastErasesTheDimension { symbol: String },
    #[error("the cast `{symbol}` has no magnitude")]
    CastHasNoMagnitude { symbol: String },
    #[error("a cast symbol cannot be empty")]
    EmptyCastSymbol,
    #[error("a dimension matrix needs at least one declared quantity")]
    NoQuantities,
    #[error("a quantity name cannot be empty")]
    EmptyQuantityName,
    #[error("the quantity `{name}` is declared twice")]
    DuplicateQuantityName { name: String },
    #[error(
        "the rank readings disagree: elimination {by_elimination}, transpose {by_transpose}, \
         Smith normal form {by_smith_normal_form}"
    )]
    RankDisagreement {
        by_elimination: usize,
        by_transpose: usize,
        by_smith_normal_form: usize,
    },
    #[error("clearing denominators for `{quantity}` did not land in the integers")]
    IntegralRescalingFailed { quantity: String },
    #[error("the returned group `{group}` does not annihilate the dimension matrix")]
    KernelDoesNotAnnihilate { group: String },
    #[error("the exact elimination refused: {0}")]
    Elimination(String),
    #[error("the exact linear carrier refused: {0}")]
    ExactLinear(String),
}

// ===============================================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// `M`, `L`, `T` occur **only here and in the driver**, as a declared fixture. Nothing in the
    /// organ above names a unit.
    fn mechanics() -> BaseUnits {
        BaseUnits::declare(["M", "L", "T"]).expect("the declared base is well formed")
    }

    fn rational(numerator: i64, denominator: i64) -> Rat {
        Rat::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    fn whole(value: i64) -> Rat {
        Rat::from_integer(BigInt::from(value))
    }

    fn word(values: &[i64]) -> Vec<Rat> {
        values.iter().map(|value| whole(*value)).collect()
    }

    /// `(E, m, c, p)` over `(M, L, T)`. The fixture the whole design is graded on.
    fn energy_momentum() -> DimensionMatrix {
        let base = mechanics();
        DimensionMatrix::declare(
            base.clone(),
            vec![
                (
                    "E".to_owned(),
                    base.integer_dimension(&[1, 2, -2]).expect("E"),
                ),
                ("m".to_owned(), base.integer_dimension(&[1, 0, 0]).expect("m")),
                ("c".to_owned(), base.integer_dimension(&[0, 1, -1]).expect("c")),
                ("p".to_owned(), base.integer_dimension(&[1, 1, -1]).expect("p")),
            ],
        )
        .expect("the declared matrix is well formed")
    }

    #[test]
    fn the_energy_momentum_matrix_has_rank_two_and_two_pi_groups() {
        let groups = energy_momentum().buckingham().expect("the pi groups return");
        assert_eq!(groups.rank, 2, "row T is minus row L, so the rank is 2 not 3");
        assert_eq!(groups.rank_by_smith_normal_form, 2);
        assert_eq!(groups.rank_by_transpose, 2);
        assert_eq!(groups.independent_group_count, 2);
        assert_eq!(groups.basis.len(), 2);
        assert_eq!(groups.free_positions, vec![2, 3]);
    }

    #[test]
    fn the_returned_groups_annihilate_the_matrix_exactly() {
        let matrix = energy_momentum();
        let groups = matrix.buckingham().expect("the pi groups return");
        let exact = matrix.as_exact_matrix().expect("the matrix is rectangular");
        for group in groups.basis.iter().chain(&groups.primitive_basis) {
            let image = exact.apply(&group.exponents).expect("shapes compose");
            assert!(
                image.iter().all(Zero::is_zero),
                "the group {} left a residual",
                group.render(&groups.quantities)
            );
        }
    }

    #[test]
    fn the_two_physically_named_groups_lie_in_the_returned_span() {
        let groups = energy_momentum().buckingham().expect("the pi groups return");
        // E / m c^2
        let over_rest = word(&[1, -1, -2, 0]);
        // E / p c
        let over_momentum = word(&[1, 0, -1, -1]);
        assert_eq!(
            groups.coordinates_of(&over_rest),
            Some(word(&[-2, 0])),
            "E/mc^2 expands in the returned basis"
        );
        assert_eq!(
            groups.coordinates_of(&over_momentum),
            Some(word(&[-1, -1])),
            "E/pc expands in the returned basis"
        );
    }

    #[test]
    fn a_kernel_basis_is_a_receiver_coordinate_and_the_span_is_the_invariant() {
        let groups = energy_momentum().buckingham().expect("the pi groups return");
        // The elimination returns half-integer words; the primitive normalisation returns the
        // integer word the record exhibits by hand. Both are the same kernel.
        assert_eq!(
            groups.basis[0].exponents,
            vec![rational(-1, 2), rational(1, 2), whole(1), whole(0)]
        );
        assert_eq!(groups.primitive_basis[0].exponents, word(&[1, -1, -2, 0]));
        assert!(groups.contains(&groups.primitive_basis[0].exponents));
        assert!(groups.contains(&groups.basis[1].exponents));
    }

    #[test]
    fn a_word_that_is_not_dimensionless_is_not_in_the_span() {
        let groups = energy_momentum().buckingham().expect("the pi groups return");
        // E / m is not dimensionless.
        assert_eq!(groups.coordinates_of(&word(&[1, -1, 0, 0])), None);
        assert!(!groups.contains(&word(&[1, 0, 0, 0])));
        // And a word of the wrong length is refused rather than truncated.
        assert_eq!(groups.coordinates_of(&word(&[1, -1, -2])), None);
    }

    #[test]
    fn a_full_rank_dimension_matrix_returns_no_pi_groups() {
        let base = mechanics();
        let matrix = DimensionMatrix::declare(
            base.clone(),
            vec![
                ("m".to_owned(), base.integer_dimension(&[1, 0, 0]).unwrap()),
                ("l".to_owned(), base.integer_dimension(&[0, 1, 0]).unwrap()),
                ("t".to_owned(), base.integer_dimension(&[0, 0, 1]).unwrap()),
            ],
        )
        .expect("declared");
        let groups = matrix.buckingham().expect("the pi groups return");
        assert_eq!(groups.rank, 3);
        assert_eq!(groups.rank_by_smith_normal_form, 3);
        assert_eq!(groups.independent_group_count, 0);
        assert!(groups.basis.is_empty());
        assert_eq!(groups.undetectable_rescaling_count, 0);
        assert!(groups.undetectable_base_rescalings.is_empty());
    }

    #[test]
    fn the_group_count_moves_with_the_material() {
        let base = mechanics();
        let mass = ("m".to_owned(), base.integer_dimension(&[1, 0, 0]).unwrap());
        let length = ("l".to_owned(), base.integer_dimension(&[0, 1, 0]).unwrap());
        let time = ("t".to_owned(), base.integer_dimension(&[0, 0, 1]).unwrap());
        let speed = ("c".to_owned(), base.integer_dimension(&[0, 1, -1]).unwrap());
        let energy = ("E".to_owned(), base.integer_dimension(&[1, 2, -2]).unwrap());

        let mut columns = vec![mass, length, time];
        let counts: Vec<usize> = [None, Some(speed), Some(energy)]
            .into_iter()
            .map(|addition| {
                if let Some(column) = addition {
                    columns.push(column);
                }
                DimensionMatrix::declare(base.clone(), columns.clone())
                    .expect("declared")
                    .buckingham()
                    .expect("returns")
                    .independent_group_count
            })
            .collect();
        assert_eq!(counts, vec![0, 1, 2], "the count moves with the material");
    }

    #[test]
    fn the_left_kernel_names_the_rescaling_that_erases_the_cast() {
        let groups = energy_momentum().buckingham().expect("the pi groups return");
        assert_eq!(groups.undetectable_rescaling_count, 1);
        assert_eq!(groups.undetectable_base_rescalings.len(), 1);
        // Rescaling L and T together leaves every one of E, m, c, p dimensionally unmoved. That is
        // exactly what "set c = 1" is, and here it is computed rather than conventional.
        let rescaling = &groups.undetectable_base_rescalings[0];
        assert_eq!(rescaling, &vec![whole(0), whole(1), whole(1)]);
    }

    #[test]
    fn adding_a_length_to_a_time_is_refused_by_type_naming_both() {
        let base = mechanics();
        let length = Quantity::integer(3, base.unit("L").unwrap());
        let time = Quantity::integer(3, base.unit("T").unwrap());
        let refusal = length.sum(&time).expect_err("addition refuses");
        assert_eq!(
            refusal,
            QuantityError::DimensionMismatch {
                operation: "addition",
                left: "L".to_owned(),
                right: "T".to_owned(),
            }
        );
        assert!(
            refusal.to_string().contains("[L]") && refusal.to_string().contains("[T]"),
            "the refusal names both dimensions: {refusal}"
        );
        assert!(length.difference(&time).is_err());
    }

    #[test]
    fn a_length_and_a_time_are_open_rather_than_unequal() {
        let base = mechanics();
        let length = Quantity::integer(3, base.unit("L").unwrap());
        let time = Quantity::integer(3, base.unit("T").unwrap());
        assert_eq!(length.compare(&time), ExactOrdering::Open);
        assert_eq!(time.compare(&length), ExactOrdering::Open);
        // Same dimension, so the question has an answer.
        let longer = Quantity::integer(4, base.unit("L").unwrap());
        assert_eq!(length.compare(&longer), ExactOrdering::Less);
        assert_eq!(longer.compare(&length), ExactOrdering::Greater);
        assert_eq!(length.compare(&length), ExactOrdering::Equal);
    }

    #[test]
    fn a_quantity_multiplied_by_a_quantity_adds_the_exponent_words() {
        let base = mechanics();
        let speed = Quantity::integer(2, base.integer_dimension(&[0, 1, -1]).unwrap());
        let mass = Quantity::integer(3, base.unit("M").unwrap());
        let momentum = mass.product(&speed).expect("always lawful");
        assert_eq!(momentum.dimension().exponents(), word(&[1, 1, -1]));
        assert_eq!(momentum.parts().0, &whole(6));
        let back = momentum.ratio(&speed).expect("lawful");
        assert_eq!(back.dimension(), mass.dimension());
    }

    #[test]
    fn the_exponent_group_is_rational_because_the_square_root_is_not_optional() {
        let base = mechanics();
        // The geometric mean of a length and a time. Its dimension is not in Z^k at all.
        let length_time = base.integer_dimension(&[0, 1, 1]).unwrap();
        let half = length_time.powed(&rational(1, 2));
        assert_eq!(
            half.exponents(),
            vec![whole(0), rational(1, 2), rational(1, 2)]
        );
        assert!(half.integral().is_none(), "L^(1/2) T^(1/2) is not integral");
        assert_eq!(half.powed(&whole(2)).exponents(), word(&[0, 1, 1]));
        assert!(length_time.integral().is_some());
    }

    #[test]
    fn a_rational_power_of_a_magnitude_returns_or_refuses_and_never_approximates() {
        let base = mechanics();
        let area = base.integer_dimension(&[0, 2, 0]).unwrap();
        let square = Quantity::integer(4, area.clone());
        let side = square.powed(&rational(1, 2)).expect("4 has a rational root");
        assert_eq!(side.parts().0, &whole(2));
        assert_eq!(side.dimension().exponents(), word(&[0, 1, 0]));

        let irrational = Quantity::integer(2, area);
        let refusal = irrational
            .powed(&rational(1, 2))
            .expect_err("2 has no rational square root");
        assert!(matches!(refusal, QuantityError::NoRationalRoot { .. }));

        // A negative magnitude has an exact cube root and no square root.
        let volume = base.integer_dimension(&[0, 3, 0]).unwrap();
        let negative = Quantity::integer(-8, volume);
        assert_eq!(
            negative.powed(&rational(1, 3)).unwrap().parts().0,
            &whole(-2)
        );
        assert!(negative.powed(&rational(1, 2)).is_err());
    }

    #[test]
    fn a_bare_rational_is_only_readable_off_a_dimensionless_quantity() {
        let base = mechanics();
        let length = Quantity::integer(7, base.unit("L").unwrap());
        assert!(matches!(
            length.rational(),
            Err(QuantityError::NotDimensionless { .. })
        ));
        let metre = Quantity::integer(1, base.unit("L").unwrap());
        assert_eq!(length.measured_in(&metre).unwrap(), whole(7));
        let time = Quantity::integer(1, base.unit("T").unwrap());
        assert!(length.measured_in(&time).is_err());
        let ratio = length.ratio(&metre).unwrap();
        assert_eq!(ratio.rational().unwrap(), &whole(7));
    }

    #[test]
    fn a_cast_whose_dimension_is_trivial_is_refused_by_name() {
        let base = mechanics();
        let erased = Quantity::integer(1, base.dimensionless());
        let refusal = Cast::declare("c", erased).expect_err("a dimensionless cast is refused");
        assert_eq!(
            refusal,
            QuantityError::CastErasesTheDimension {
                symbol: "c".to_owned()
            }
        );
        // A cast whose MAGNITUDE is one is lawful: that is a choice of units, not an erasure.
        let unit_speed = Quantity::integer(1, base.integer_dimension(&[0, 1, -1]).unwrap());
        assert!(Cast::declare("c", unit_speed).is_ok());
    }

    #[test]
    fn applying_a_cast_carries_the_chart_change_in_the_return() {
        let base = mechanics();
        let cast = Cast::declare(
            "c",
            Quantity::integer(1, base.integer_dimension(&[0, 1, -1]).unwrap()),
        )
        .expect("declared");
        let mass = Quantity::integer(4, base.unit("M").unwrap());
        let application = cast.apply(&mass, &whole(2)).expect("the cast applies");
        assert_eq!(application.cast, "c");
        assert_eq!(application.power, whole(2));
        assert_eq!(application.from.exponents(), word(&[1, 0, 0]));
        assert_eq!(application.to.exponents(), word(&[1, 2, -2]));
        assert!(!application.is_inert());
        assert_eq!(application.returned.parts().0, &whole(4));
        // The zeroth power is the cast that is not one, and the return says so.
        let inert = cast.apply(&mass, &whole(0)).expect("lawful");
        assert!(inert.is_inert());
    }

    #[test]
    fn a_pi_group_evaluates_to_an_exact_dimensionless_rational() {
        let base = mechanics();
        let groups = energy_momentum().buckingham().expect("returns");
        // beta = 3/5, gamma = 5/4, m = 4, c = 1: (mc^2, pc, E) = (4, 3, 5).
        let values = vec![
            Quantity::integer(5, base.integer_dimension(&[1, 2, -2]).unwrap()),
            Quantity::integer(4, base.integer_dimension(&[1, 0, 0]).unwrap()),
            Quantity::integer(1, base.integer_dimension(&[0, 1, -1]).unwrap()),
            Quantity::integer(3, base.integer_dimension(&[1, 1, -1]).unwrap()),
        ];
        let over_rest = PiGroup::new(word(&[1, -1, -2, 0]));
        let over_momentum = PiGroup::new(word(&[1, 0, -1, -1]));
        assert!(groups.contains(&over_rest.exponents));
        assert!(groups.contains(&over_momentum.exponents));
        assert_eq!(
            over_rest.evaluate(&values).unwrap().rational().unwrap(),
            &rational(5, 4),
            "E/mc^2 is gamma"
        );
        assert_eq!(
            over_momentum.evaluate(&values).unwrap().rational().unwrap(),
            &rational(5, 3),
            "E/pc is 1/beta"
        );
        // And the two the identity is stated in.
        assert_eq!(
            over_rest
                .negated()
                .evaluate(&values)
                .unwrap()
                .rational()
                .unwrap(),
            &rational(4, 5)
        );
        assert_eq!(
            over_momentum
                .negated()
                .evaluate(&values)
                .unwrap()
                .rational()
                .unwrap(),
            &rational(3, 5)
        );
    }

    #[test]
    fn the_energy_momentum_relation_is_exact_at_a_rational_beta() {
        let base = mechanics();
        let energy_dimension = base.integer_dimension(&[1, 2, -2]).unwrap();
        let cast = Cast::declare(
            "c",
            Quantity::integer(1, base.integer_dimension(&[0, 1, -1]).unwrap()),
        )
        .unwrap();
        // (beta, gamma, m) triples chosen so every figure is an exact integer.
        for (mass, momentum, energy) in [(4_i64, 3_i64, 5_i64), (12, 5, 13), (7, 0, 7)] {
            let rest = cast
                .apply(
                    &Quantity::integer(mass, base.unit("M").unwrap()),
                    &whole(2),
                )
                .unwrap()
                .returned;
            let carried = cast
                .apply(
                    &Quantity::integer(momentum, base.integer_dimension(&[1, 1, -1]).unwrap()),
                    &whole(1),
                )
                .unwrap()
                .returned;
            let total = Quantity::integer(energy, energy_dimension.clone());
            assert_eq!(rest.dimension(), &energy_dimension);
            assert_eq!(carried.dimension(), &energy_dimension);
            let left = total.powed(&whole(2)).unwrap();
            let right = rest
                .powed(&whole(2))
                .unwrap()
                .sum(&carried.powed(&whole(2)).unwrap())
                .unwrap();
            assert_eq!(left, right, "E^2 = (mc^2)^2 + (pc)^2 exactly");
            // The non-dimensionalisation: a point on the unit circle over Q.
            let cosine = rest.ratio(&total).unwrap().rational().unwrap().clone();
            let sine = carried.ratio(&total).unwrap().rational().unwrap().clone();
            assert_eq!(&cosine * &cosine + &sine * &sine, Rat::one());
        }
    }

    #[test]
    fn the_shorthand_is_the_relation_at_a_half_turn_of_zero() {
        let base = mechanics();
        let energy_dimension = base.integer_dimension(&[1, 2, -2]).unwrap();
        let cast = Cast::declare(
            "c",
            Quantity::integer(1, base.integer_dimension(&[0, 1, -1]).unwrap()),
        )
        .unwrap();
        // t = tan(theta/2) = sin / (1 + cos). Exact, and zero exactly when p = 0.
        let half_turn = |mass: i64, momentum: i64, energy: i64| -> Rat {
            let rest = cast
                .apply(&Quantity::integer(mass, base.unit("M").unwrap()), &whole(2))
                .unwrap()
                .returned;
            let carried = cast
                .apply(
                    &Quantity::integer(momentum, base.integer_dimension(&[1, 1, -1]).unwrap()),
                    &whole(1),
                )
                .unwrap()
                .returned;
            let total = Quantity::integer(energy, energy_dimension.clone());
            let cosine = rest.ratio(&total).unwrap().rational().unwrap().clone();
            let sine = carried.ratio(&total).unwrap().rational().unwrap().clone();
            sine / (Rat::one() + cosine)
        };
        assert_eq!(half_turn(4, 3, 5), rational(1, 3));
        assert_eq!(half_turn(12, 5, 13), rational(1, 5));
        assert_eq!(half_turn(7, 0, 7), Rat::zero(), "E = mc^2 is theta = 0");
    }

    #[test]
    fn at_theta_zero_the_second_group_leaves_the_chart_rather_than_returning_a_lie() {
        let base = mechanics();
        let values = vec![
            Quantity::integer(7, base.integer_dimension(&[1, 2, -2]).unwrap()),
            Quantity::integer(7, base.integer_dimension(&[1, 0, 0]).unwrap()),
            Quantity::integer(1, base.integer_dimension(&[0, 1, -1]).unwrap()),
            Quantity::integer(0, base.integer_dimension(&[1, 1, -1]).unwrap()),
        ];
        let over_rest = PiGroup::new(word(&[1, -1, -2, 0]));
        let over_momentum = PiGroup::new(word(&[1, 0, -1, -1]));
        assert_eq!(
            over_rest.evaluate(&values).unwrap().rational().unwrap(),
            &Rat::one(),
            "gamma is one"
        );
        assert_eq!(
            over_momentum.evaluate(&values),
            Err(QuantityError::DivisionByZero),
            "E/pc has left the chart, which is why the shorthand looks complete"
        );
        assert_eq!(
            over_momentum
                .negated()
                .evaluate(&values)
                .unwrap()
                .rational()
                .unwrap(),
            &Rat::zero(),
            "and pc/E is beta = 0"
        );
    }

    #[test]
    fn the_invariant_factors_report_a_dimension_reached_only_in_a_multiple() {
        let base = BaseUnits::declare(["A"]).unwrap();
        // One quantity whose dimension is A^2: the declared material reaches A only in a multiple.
        let matrix = DimensionMatrix::declare(
            base.clone(),
            vec![("a2".to_owned(), base.integer_dimension(&[2]).unwrap())],
        )
        .unwrap();
        let groups = matrix.buckingham().unwrap();
        assert_eq!(groups.rank, 1);
        assert_eq!(groups.independent_group_count, 0);
        assert_eq!(groups.invariant_factors, vec![BigInt::from(2)]);
        // And a base the material reaches outright returns a factor of one.
        let plain = DimensionMatrix::declare(
            base.clone(),
            vec![("a".to_owned(), base.integer_dimension(&[1]).unwrap())],
        )
        .unwrap();
        assert_eq!(plain.buckingham().unwrap().invariant_factors, vec![
            BigInt::one()
        ]);
    }

    #[test]
    fn a_rational_exponent_column_is_rescaled_to_the_integers_before_smith() {
        let base = mechanics();
        // sqrt(L T): the column carries denominator 2.
        let matrix = DimensionMatrix::declare(
            base.clone(),
            vec![
                (
                    "g".to_owned(),
                    base.integer_dimension(&[0, 1, 1])
                        .unwrap()
                        .powed(&rational(1, 2)),
                ),
                ("l".to_owned(), base.integer_dimension(&[0, 1, 0]).unwrap()),
                ("t".to_owned(), base.integer_dimension(&[0, 0, 1]).unwrap()),
            ],
        )
        .unwrap();
        let groups = matrix.buckingham().unwrap();
        assert_eq!(groups.column_scales, vec![
            BigInt::from(2),
            BigInt::one(),
            BigInt::one()
        ]);
        assert_eq!(groups.rank, 2);
        assert_eq!(groups.rank_by_smith_normal_form, 2);
        assert_eq!(groups.independent_group_count, 1);
        // g^2 / (l t) is the group, and it is dimensionless.
        assert!(groups.contains(&word(&[2, -1, -1])));
    }

    #[test]
    fn dimensions_from_two_declarations_refuse_to_compose() {
        let one = BaseUnits::declare(["M", "L", "T"]).unwrap();
        let other = BaseUnits::declare(["M", "L", "Q"]).unwrap();
        let left = one.unit("L").unwrap();
        let right = other.unit("L").unwrap();
        assert!(matches!(
            left.product(&right),
            Err(QuantityError::IncomparableBaseUnits { .. })
        ));
        assert_eq!(
            Quantity::integer(1, left).compare(&Quantity::integer(1, right)),
            ExactOrdering::Open
        );
    }

    #[test]
    fn the_declaration_refuses_what_it_should() {
        assert_eq!(
            BaseUnits::declare(Vec::<String>::new()).unwrap_err(),
            QuantityError::NoBaseUnits
        );
        assert_eq!(
            BaseUnits::declare(["M", "M"]).unwrap_err(),
            QuantityError::DuplicateBaseUnit {
                symbol: "M".to_owned()
            }
        );
        assert!(BaseUnits::declare(["M", " "]).is_err());
        let base = mechanics();
        assert!(base.unit("Q").is_err());
        assert!(base.dimension(vec![Rat::zero(); 2]).is_err());
        assert_eq!(
            DimensionMatrix::declare(base.clone(), Vec::new()).unwrap_err(),
            QuantityError::NoQuantities
        );
        let column = ("m".to_owned(), base.unit("M").unwrap());
        assert!(
            DimensionMatrix::declare(base, vec![column.clone(), column]).is_err(),
            "a repeated quantity name is refused"
        );
    }

    #[test]
    fn the_exact_integer_root_is_a_search_and_never_an_approximation() {
        assert_eq!(
            exact_integer_root(&BigInt::from(1024), 10),
            Some(BigInt::from(2))
        );
        assert_eq!(exact_integer_root(&BigInt::from(1023), 10), None);
        assert_eq!(exact_integer_root(&BigInt::from(-27), 3), Some(BigInt::from(-3)));
        assert_eq!(exact_integer_root(&BigInt::from(-27), 2), None);
        assert_eq!(exact_integer_root(&BigInt::zero(), 5), Some(BigInt::zero()));
        assert_eq!(exact_integer_root(&BigInt::one(), 7), Some(BigInt::one()));
        assert_eq!(exact_integer_root(&BigInt::from(9), 0), None);
    }

    #[test]
    fn a_dimensionless_group_renders_as_one_and_a_dimension_renders_its_word() {
        let base = mechanics();
        assert_eq!(base.dimensionless().render(), "1");
        assert_eq!(
            base.integer_dimension(&[1, 2, -2]).unwrap().render(),
            "M L^2 T^-2"
        );
        assert_eq!(
            base.integer_dimension(&[0, 1, 1])
                .unwrap()
                .powed(&rational(1, 2))
                .render(),
            "L^1/2 T^1/2"
        );
        let names = vec!["E".to_owned(), "m".to_owned(), "c".to_owned(), "p".to_owned()];
        assert_eq!(
            PiGroup::new(word(&[1, -1, -2, 0])).render(&names),
            "E m^-1 c^-2"
        );
        assert_eq!(PiGroup::new(word(&[0, 0, 0, 0])).render(&names), "1");
    }

    #[test]
    fn the_eliminations_are_counted_as_work_and_never_as_elapsed_time() {
        let groups = energy_momentum().buckingham().expect("returns");
        assert!(
            groups.eliminations > 0,
            "the reduction really did eliminate: {}",
            groups.eliminations
        );
    }
}
