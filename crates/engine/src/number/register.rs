//! **Presets** (N8): a native type is the place graph with its choices fixed and unnamed (its carry edges'
//! cuts, its closing edge, its section). It enters the owner only as a named preset, by a declared read, and
//! leaves only by a declared write that returns its winding: `u64` and `i64` are one path of 64 places with two
//! sections; packed lanes and bitfields are one register with carry edges cut at their boundaries.

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, ToPrimitive, Zero};

use super::closing::{Closing, Residue, Winding};
use super::value::{Digits, Section, Value};
use super::{refuse, Grain, Result, Width};

/// **Cut carry edges**: the field boundaries of a register, each field's width from its lowest place up.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Cuts {
    fields: Vec<u32>,
}

impl Cuts {
    /// No cut: one field of `w` places.
    pub fn none(w: u32) -> Self {
        Self { fields: vec![w] }
    }

    /// Fields of the given widths from the lowest place up (lanes: equal widths).
    pub fn fields(widths: &[u32]) -> Self {
        Self { fields: widths.to_vec() }
    }

    pub fn widths(&self) -> &[u32] {
        &self.fields
    }

    /// Each field's top place in a 64-place word (`H`), the mask the cut add restores by XOR.
    pub fn tops64(&self) -> Result<u64> {
        let mut at = 0u32;
        let mut h = 0u64;
        for &w in &self.fields {
            if w == 0 || at + w > 64 {
                return refuse("a 64-place register's fields outside its places");
            }
            h |= 1u64 << (at + w - 1);
            at += w;
        }
        Ok(h)
    }
}

/// **A register**: a native type's choices named (its width, cuts, closing edge and section).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Register {
    pub width: Width,
    pub cuts: Cuts,
    pub closing: Closing,
    pub section: Section,
}

impl Register {
    fn path(w: u32, section: Section) -> Self {
        Self { width: Width::new(w), cuts: Cuts::none(w), closing: Closing::Path(w), section }
    }

    /// `u64`: a path of 64 places, read in `[0, 2^64)`.
    pub fn u64() -> Self {
        Self::path(64, Section::Low)
    }

    /// `i64`: the same path, read in `[−2^63, 2^63)`.
    pub fn i64() -> Self {
        Self::path(64, Section::TwosComplement)
    }

    pub fn u32() -> Self {
        Self::path(32, Section::Low)
    }

    pub fn i32() -> Self {
        Self::path(32, Section::TwosComplement)
    }

    pub fn u128() -> Self {
        Self::path(128, Section::Low)
    }

    pub fn i128() -> Self {
        Self::path(128, Section::TwosComplement)
    }

    /// Packed lanes or bitfields in one 64-place word: carry edges cut at the fields' boundaries, each field
    /// read in the low section.
    pub fn lanes(widths: &[u32]) -> Result<Self> {
        let cuts = Cuts::fields(widths);
        cuts.tops64()?;
        Ok(Self { width: Width::new(widths.iter().sum()), cuts, closing: Closing::Path(64), section: Section::Low })
    }

    /// **The declared read** of a word's bits (the low `w` places of `bits`) into the owner: the class the
    /// register's section reads them as, at grain one, at the register's width.
    fn read_bits(&self, bits: u128) -> Result<Value> {
        let w = self.width.places();
        if w > 128 || !(w == 128 || bits >> w == 0) {
            return refuse("a read past the register's places");
        }
        if w <= 126 {
            // Inline: the class fits the realization's word, so no limb is built.
            let x = bits as i128;
            let top = 1i128 << (w - 1).min(125);
            let digits = match self.section {
                Section::Low => x,
                Section::TwosComplement | Section::Balanced if x >= top => x - (1i128 << w),
                Section::SignMagnitude if x >= top => -(x - top),
                _ => x,
            };
            return Value::of(Grain::new(0), self.width, self.section, Digits::Small(digits));
        }
        let unsigned = BigInt::from(bits);
        let digits = match self.section {
            Section::Low => unsigned,
            Section::TwosComplement | Section::Balanced => {
                let top = BigInt::one() << (w - 1) as usize;
                if unsigned >= top {
                    unsigned - (BigInt::one() << w as usize)
                } else {
                    unsigned
                }
            }
            Section::SignMagnitude => {
                let top = BigInt::one() << (w - 1) as usize;
                if unsigned >= top {
                    -(unsigned - top)
                } else {
                    unsigned
                }
            }
        };
        Value::of(Grain::new(0), self.width, self.section, Digits::from_big(digits))
    }

    /// **The declared write** of a value at grain one into the register's bits: its residue on the register's
    /// path, with the winding that left its top place (zero just when the value lies in the section).
    fn write_bits(&self, value: &Value) -> Result<(u128, Winding)> {
        if value.grain().lo() != 0 {
            return refuse("a register writes a value at grain one; release it there first");
        }
        let w = self.width.places();
        if let (Digits::Small(x), true) = (&value.digits, w <= 126) {
            // Inline: the residue is the low places of the word, the winding the rest of its class read in
            // the section (an arithmetic shift is the floor).
            let shift = if self.section == Section::Low { 0 } else { 1i128 << (w - 1) };
            if let Some(lifted) = x.checked_add(shift) {
                let bits = (*x as u128) & ((1u128 << w) - 1);
                let wind = Digits::Small(lifted >> w);
                let ww = wind.places_in(Section::TwosComplement).max(1);
                return Ok((bits, Winding(Value::of(Grain::new(0), Width::new(ww), Section::TwosComplement, wind)?)));
            }
        }
        let (residue, _) = Residue::of(value, &Closing::Path(w))?;
        let low = residue.lanes[0].digits.big();
        let x = value.digits.big();
        // The winding in the register's section: how far the class lies outside the section's range.
        let shift = match self.section {
            Section::Low => BigInt::zero(),
            _ => BigInt::one() << (w - 1) as usize,
        };
        let winding = (x + &shift).div_floor(&(BigInt::one() << w as usize));
        let bits = low.to_u128().ok_or(super::NumberError::Refused("a register's residue past 128 places"))?;
        let wind = Digits::from_big(winding);
        let ww = wind.places_in(Section::TwosComplement).max(1);
        Ok((bits, Winding(Value::of(Grain::new(0), Width::new(ww), Section::TwosComplement, wind)?)))
    }

    pub fn read_u64(&self, x: u64) -> Result<Value> {
        self.read_bits(u128::from(x))
    }

    pub fn read_i64(&self, x: i64) -> Result<Value> {
        self.read_bits(u128::from(x as u64))
    }

    pub fn read_u128(&self, x: u128) -> Result<Value> {
        self.read_bits(x)
    }

    pub fn read_i128(&self, x: i128) -> Result<Value> {
        self.read_bits(x as u128)
    }

    pub fn read_u32(&self, x: u32) -> Result<Value> {
        self.read_bits(u128::from(x))
    }

    pub fn read_i32(&self, x: i32) -> Result<Value> {
        self.read_bits(u128::from(x as u32))
    }

    /// The value's bits as a native `u64` word and its winding.
    pub fn write_u64(&self, value: &Value) -> Result<(u64, Winding)> {
        if self.width.places() > 64 {
            return refuse("a 64-place write from a wider register");
        }
        let (bits, winding) = self.write_bits(value)?;
        Ok((bits as u64, winding))
    }

    /// The value's bits as a native `i64` word (the same bits, read in the signed section) and its winding.
    pub fn write_i64(&self, value: &Value) -> Result<(i64, Winding)> {
        let (bits, winding) = self.write_u64(value)?;
        Ok((bits as i64, winding))
    }

    pub fn write_u128(&self, value: &Value) -> Result<(u128, Winding)> {
        self.write_bits(value)
    }

    pub fn write_i128(&self, value: &Value) -> Result<(i128, Winding)> {
        let (bits, winding) = self.write_bits(value)?;
        Ok((bits as i128, winding))
    }

    /// **Sign extension** (a declared map between presets): the value's class written out on a wider register
    /// of the same section, its tail of ones written where it is negative.
    pub fn extend(&self, value: &Value, wider: &Register) -> Result<Value> {
        if wider.width < self.width || wider.section != self.section {
            return refuse("a sign extension onto a narrower register or another section");
        }
        Value::of(value.grain(), wider.width, wider.section, value.digits.clone())
    }

    /// **The cut add** on packed fields in one 64-place word: each field's top place masked, one native add,
    /// the top places restored by XOR, `((x ∧ ¬H) + (y ∧ ¬H)) ⊕ ((x ⊕ y) ∧ H)` (the record's L3). With every
    /// edge cut it is XOR; with none, the 64-place add.
    pub fn add_packed(&self, x: u64, y: u64) -> Result<u64> {
        let h = self.cuts.tops64()?;
        Ok(((x & !h).wrapping_add(y & !h)) ^ ((x ^ y) & h))
    }

    /// **The join** of fields into one packed word (the inverse of [`Register::read_fields`]): each field a
    /// value at grain one in the low section, refused where it lies outside its field's places.
    pub fn write_fields(&self, fields: &[Value]) -> Result<u64> {
        if fields.len() != self.cuts.widths().len() {
            return refuse("a join of a different count of fields than the register's");
        }
        let mut at = 0u32;
        let mut word = 0u64;
        for (f, &w) in fields.iter().zip(self.cuts.widths()) {
            if f.grain().lo() != 0 || f.digits.places_in(Section::Low) > w {
                return refuse("a field outside its places");
            }
            let Digits::Small(x) = f.digits else { return refuse("a field outside its places") };
            word |= (x as u64) << at;
            at += w;
        }
        Ok(word)
    }

    /// The fields of a packed word, each read in the low section at its own width.
    pub fn read_fields(&self, word: u64) -> Result<Vec<Value>> {
        let mut at = 0u32;
        let mut out = Vec::with_capacity(self.cuts.widths().len());
        for &w in self.cuts.widths() {
            let field = (word >> at) & if w == 64 { u64::MAX } else { (1u64 << w) - 1 };
            out.push(Value::of(Grain::new(0), Width::new(w), Section::Low, Digits::Small(i128::from(field)))?);
            at += w;
        }
        Ok(out)
    }
}
