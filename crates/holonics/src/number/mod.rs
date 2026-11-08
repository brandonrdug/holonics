//! **The number of the theory: a class on a graph of places** (Brandon, November 8; the record
//! `research/records/2026-11-08_A_NUMBER_IS_A_CLASS_ON_A_GRAPH_OF_PLACES_AND_EVERY_METHOD_IS_A_BRACKETING_A_CHART_OR_AN_END.md`,
//! §9 and §10, theory's design; this owner is its build step 1).
//!
//! [definition] A value occupies places `[lo, lo + w)` joined by carry edges weighted by the radix. Two digit
//! strings name one value just when they differ by a boundary, so the value is a class, and every way of
//! computing it (a bracketing of the carries, a decomposition of a product, an end of an inversion) gives the
//! same class. A value carries every choice that a native word leaves unnamed:
//! - **N1 places**: its grain `2^lo` ([`Grain`]) and its width `w` ([`Width`]);
//! - **N2 closing edge**: [`Closing`], the graph's modulus (the open ray widens; a path of `w` places returns
//!   its winding, never wraps silently; a ring, a twisted ring, a weighted or Solinas closing, coprime rings);
//! - **N3 width as a need**: every operation derives its result's width from its operands' (a sum the wider
//!   plus one, a sum of `n` plus `⌈log₂ n⌉`, a product the two widths added), so no width is picked to fit a
//!   carrier; a width is held as its own binary expansion ([`Width::planes`]);
//! - **N4 fibre form**: canonical digits ([`Value`]) or a redundant accumulation of place sums with its term
//!   count ([`Accumulation`]), normalized at a declared point, the same bits under any bracketing;
//! - **N5 release**: the only narrowing ([`release`]), naming its rounding and returning its remainder;
//! - **N6 inversion**: one map with its residual at a declared end ([`invert`]), returning `(X, E)` with its
//!   certificate;
//! - **N7 shears**: the reversible update `y ← y + f(x)` carries its inverse ([`Shear`]);
//! - **N8 presets**: a native type is a register with its choices fixed ([`Register`]), entering only by a
//!   declared map (a section, a sign extension, a cut or a join of carry edges), never as a foreign limb.
//!
//! The digits' realization (machine words inline at small widths, wider limbs beyond) is this owner's and
//! never leaves it: no value exposes a native integer, and nothing converts into one silently.
//!
//! **Guards** (N8, the record's §9.5). A native integer enters only by a preset's declared read:
//! ```compile_fail,E0277
//! let v: holonics::number::Value = 3i128.into();
//! ```
//! the digits' realization never leaves the owner:
//! ```compile_fail,E0616
//! let v = holonics::number::Register::i64().read_i64(3).unwrap();
//! let _ = v.digits;
//! ```
//! and a value has no wrapping operation:
//! ```compile_fail,E0599
//! let v = holonics::number::Register::u64().read_u64(3).unwrap();
//! let _ = v.wrapping_add(&v);
//! ```
//! A path's overflow is written out with its winding instead:
//! ```
//! use holonics::number::Register;
//! let v = Register::u64().read_u64(u64::MAX).unwrap();
//! let (bits, winding) = Register::u64().write_u64(&v.add(&v).unwrap()).unwrap();
//! assert_eq!(bits, u64::MAX - 1);
//! assert!(!winding.0.is_zero());
//! ```

mod accumulation;
mod closing;
mod inverse;
mod register;
mod release;
mod shear;
mod value;

#[cfg(test)]
mod tests;

pub use accumulation::Accumulation;
pub use closing::{Closing, Residue, Winding};
pub use inverse::{invert, End, Inverse};
pub use register::{Cuts, Register};
pub use release::{release, Released, Rounding, Tie};
pub use shear::{AddShear, Shear};
pub use value::{Section, Value};

/// **A width**: a count of places. It is held as its own binary expansion: a width of eleven is planes of
/// eight, two and one places ([`Width::planes`]), never a sixteen-place word (the 11-05 width law).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Width {
    places: u32,
}

impl Width {
    pub const fn new(places: u32) -> Self {
        Self { places }
    }

    pub const fn places(self) -> u32 {
        self.places
    }

    /// The planes the width registers at: each set bit of its count, widest first (`11 = 8 + 2 + 1`).
    pub fn planes(self) -> Vec<u32> {
        (0..u32::BITS).rev().filter(|&b| self.places & (1 << b) != 0).map(|b| 1u32 << b).collect()
    }

    /// The need of a sum of two values: the wider plus one place.
    pub fn of_sum(a: Width, b: Width) -> Width {
        Width::new(a.places.max(b.places) + 1)
    }

    /// The need of a sum of `terms` values: the widest plus `⌈log₂ terms⌉` places.
    pub fn of_terms(widest: Width, terms: Count) -> Width {
        Width::new(widest.places + terms.ceil_log2())
    }

    /// The need of a product: the two widths added.
    pub fn of_product(a: Width, b: Width) -> Width {
        Width::new(a.places + b.places)
    }
}

/// **A grain**: the lowest place `lo` of a value, its unit `2^lo`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Grain {
    lo: i32,
}

impl Grain {
    pub const fn new(lo: i32) -> Self {
        Self { lo }
    }

    pub const fn lo(self) -> i32 {
        self.lo
    }
}

/// **A count of terms** (how many values an accumulation holds): a count, not a value of the theory's
/// arithmetic; it sets an accumulation's width need.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Count {
    terms: u64,
}

impl Count {
    pub const fn new(terms: u64) -> Self {
        Self { terms }
    }

    pub const fn terms(self) -> u64 {
        self.terms
    }

    /// `⌈log₂ terms⌉`: the places a sum of this many terms may add (zero for one term or none).
    pub fn ceil_log2(self) -> u32 {
        if self.terms <= 1 {
            0
        } else {
            u64::BITS - (self.terms - 1).leading_zeros()
        }
    }
}

/// A refusal of the number owner: an operation outside its law (never a wrap, a saturation or a silent
/// drop).
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum NumberError {
    #[error("number refused: {0}")]
    Refused(&'static str),
}

pub type Result<T> = std::result::Result<T, NumberError>;

pub(crate) fn refuse<T>(why: &'static str) -> Result<T> {
    Err(NumberError::Refused(why))
}
