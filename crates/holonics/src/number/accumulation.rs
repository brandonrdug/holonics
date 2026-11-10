//! **An accumulation** (N4's redundant fibre form): place sums held with their term count before their
//! boundary. Terms enter in any order and any bracketing (integer addition is associative), and the carry
//! happens once, at a declared normalization, which returns the canonical value at the width its terms need.

use super::value::{Digits, Section, Value};
use super::{Count, Grain, Result, Width};

/// Place sums at one grain with their term count and the widest term's width.
#[derive(Clone, Debug)]
pub struct Accumulation {
    grain: Grain,
    terms: Count,
    /// The widest term's width, and its signed places (one more for a low term), read where any term is signed.
    widest: Width,
    widest_signed: Width,
    section: Section,
    sums: Digits,
}

impl Accumulation {
    /// An empty accumulation at a grain.
    pub fn at(grain: Grain) -> Self {
        Self { grain, terms: Count::new(0), widest: Width::new(1), widest_signed: Width::new(1), section: Section::Low, sums: Digits::zero() }
    }

    /// Add a term (read at the accumulation's grain, which must be no coarser than it).
    pub fn add(&mut self, term: &Value) -> Result<()> {
        if term.grain != self.grain {
            return self.add(&term.at_grain(self.grain)?);
        }
        let w = term.width.places();
        self.widest = self.widest.max(term.width);
        self.widest_signed = self.widest_signed.max(Width::new(if term.section == Section::Low { w + 1 } else { w }));
        if term.section != Section::Low {
            self.section = Section::TwosComplement;
        }
        self.sums = self.sums.add(&term.digits);
        self.terms = Count::new(self.terms.terms() + 1);
        Ok(())
    }

    /// Join another accumulation at the same grain (a co-present partial sum).
    pub fn join(&mut self, other: &Accumulation) -> Result<()> {
        if other.grain != self.grain {
            return super::refuse("accumulations at different grains");
        }
        self.widest = self.widest.max(other.widest);
        self.widest_signed = self.widest_signed.max(other.widest_signed);
        if other.section != Section::Low {
            self.section = Section::TwosComplement;
        }
        self.sums = self.sums.add(&other.sums);
        self.terms = Count::new(self.terms.terms() + other.terms.terms());
        Ok(())
    }

    pub fn terms(&self) -> Count {
        self.terms
    }

    /// **The normalization**: the canonical value, its width the widest term's plus `⌈log₂ terms⌉` (N3), the
    /// widest read in signed places where any term is signed.
    pub fn value(&self) -> Result<Value> {
        let widest = if self.section == Section::Low { self.widest } else { self.widest_signed };
        Value::of(self.grain, Width::of_terms(widest, self.terms.max(Count::new(1))), self.section, self.sums.clone())
    }
}
