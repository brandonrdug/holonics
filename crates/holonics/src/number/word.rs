//! **The typed realization** (theory, November 8): under N3 every width is a law constant, so no width is held at run
//! time. A class whose width the law fixes is a type, [`Ray64`] or [`Ray128`], `W` places in the two's-complement section
//! at grain `2^LO`, carried in the native word the preset names. Each operation names its result's width in its type, and
//! a const assertion checks at compile time that the law's need fits it (a sum the wider plus one, a product the two widths
//! added) and that it fits the word; the run-time body is the native operation. An accumulation is checked once at its
//! loop head (the widest term's places plus `⌈log₂ n⌉` against the result's) and adds natively inside. A path's residue
//! ([`Path64`]) returns its winding with the native overflow flag.
//!
//! One section is used here: a low class of `w` places is a signed class of `w + 1` (the section rule of N3), so no
//! operation mixes sections. [`super::Value`] stays the general form, for widths a law does not fix; the two meet only by
//! the declared maps [`Ray64::value`] and [`Ray64::of_value`].

use super::value::{Digits, Section};
use super::{refuse, Grain, Result, Value, Width};

const fn max(a: u32, b: u32) -> u32 {
    if a > b {
        a
    } else {
        b
    }
}

/// `⌈log₂ n⌉`: the places a sum of `n` terms may add.
const fn ceil_log2(n: usize) -> u32 {
    if n <= 1 {
        0
    } else {
        usize::BITS - (n - 1).leading_zeros()
    }
}

macro_rules! ray {
    ($name:ident, $word:ty, $bits:expr, $read:ident, $write:ident) => {
        /// A class of `W` places in the two's-complement section at grain `2^LO`, carried in a native word. Its digits
        /// lie in `[−2^(W−1), 2^(W−1))`.
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        #[repr(transparent)]
        pub struct $name<const W: u32, const LO: i32>($word);

        impl<const W: u32, const LO: i32> $name<W, LO> {
            const FITS: () = assert!(W >= 1 && W <= $bits, "a width past its word");

            /// **The declared read** of a native word's digits as a class of `W` places, refused outside them.
            pub fn $read(x: $word) -> Result<Self> {
                let () = Self::FITS;
                if W < $bits && (x < -(1 << (W - 1)) || x >= (1 << (W - 1))) {
                    return refuse("a read outside its declared places");
                }
                Ok(Self(x))
            }

            /// **The declared write**: the class's digits as the native word (exact in it, by the type's width).
            pub fn $write(self) -> $word {
                self.0
            }

            /// The sum, its width `C` at least the wider plus one (checked at compile time).
            #[inline]
            pub fn add<const B: u32, const C: u32>(self, other: $name<B, LO>) -> $name<C, LO> {
                const { assert!(C >= max(W, B) + 1 && C <= $bits, "a sum's width below its need or past its word") };
                debug_assert!(Self::fits_in(self.0 as i128 + other.0 as i128, C));
                $name(self.0 + other.0)
            }

            /// The difference, its width `C` at least the wider plus one.
            #[inline]
            pub fn sub<const B: u32, const C: u32>(self, other: $name<B, LO>) -> $name<C, LO> {
                const { assert!(C >= max(W, B) + 1 && C <= $bits, "a difference's width below its need or past its word") };
                $name(self.0 - other.0)
            }

            /// The negation, one place wider.
            #[inline]
            pub fn neg<const C: u32>(self) -> $name<C, LO> {
                const { assert!(C >= W + 1 && C <= $bits, "a negation's width below its need or past its word") };
                $name(-self.0)
            }

            /// The product, at grain `LO + LB`, its width `C` at least the two widths added.
            #[inline]
            pub fn mul<const B: u32, const LB: i32, const C: u32, const LC: i32>(self, other: $name<B, LB>) -> $name<C, LC> {
                const { assert!(C >= W + B && C <= $bits && LC == LO + LB, "a product's width below its need, past its word, or at another grain") };
                $name(self.0 * other.0)
            }

            /// The same class in a wider word of the same kind (free: a width is a need, never a cut).
            #[inline]
            pub fn widen<const C: u32>(self) -> $name<C, LO> {
                const { assert!(C >= W && C <= $bits, "a widening to fewer places") };
                $name(self.0)
            }

            /// The same class read `K` places finer (`LC = LO − K`): the digits move up `K` places and the width with them.
            #[inline]
            pub fn finer<const K: u32, const C: u32, const LC: i32>(self) -> $name<C, LC> {
                const { assert!(C >= W + K && C <= $bits && LC == LO - K as i32, "a finer grain's width below its need") };
                $name(self.0 << K)
            }

            /// **The release** of `K` places to the nearest, ties up (the field's present release), returning the remainder
            /// at the released places: `value · 2^K + remainder = self`, the remainder in `[−2^(K−1), 2^(K−1))`.
            #[inline]
            pub fn release_nearest<const K: u32, const C: u32, const LC: i32>(self) -> ($name<C, LC>, $name<K, LO>) {
                // The quotient takes `W − K + 1` places (the rounding can reach the next one), the remainder `K`.
                const { assert!(K >= 1 && W < $bits && C + K >= W + 1 && C >= 1 && C <= $bits && LC == LO + K as i32, "a release's widths or grain not its law's") };
                let q = (self.0 + (1 << (K - 1))) >> K;
                let r = self.0 - (q << K);
                ($name(q), $name(r))
            }

            /// **An accumulation** of terms into a class of `C` places, checked once at its head (the terms' width plus
            /// `⌈log₂ n⌉` against `C`), the native adds inside.
            pub fn sum<const C: u32>(terms: &[Self]) -> Result<$name<C, LO>> {
                const { assert!(C <= $bits, "an accumulation past its word") };
                if W + ceil_log2(terms.len()) > C {
                    return refuse("an accumulation whose terms' need passes its declared width");
                }
                Ok($name(terms.iter().map(|t| t.0).sum()))
            }

            /// The class as a value of the general form (a declared map).
            pub fn value(self) -> Result<Value> {
                Value::of(Grain::new(LO), Width::new(W), Section::TwosComplement, Digits::Small(self.0 as i128))
            }

            /// A value of the general form at this grain read as this type, refused where its class needs more places.
            pub fn of_value(v: &Value) -> Result<Self> {
                let v = v.at_grain(Grain::new(LO))?;
                if v.digits.places_in(Section::TwosComplement) > W {
                    return refuse("a value outside the type's places");
                }
                match v.digits {
                    Digits::Small(x) => Ok(Self(x as $word)),
                    Digits::Big(_) => refuse("a value outside the type's places"),
                }
            }

            fn fits_in(x: i128, c: u32) -> bool {
                c >= 128 || (x >= -(1i128 << (c - 1)) && x < (1i128 << (c - 1)))
            }
        }
    };
}

ray!(Ray64, i64, 64, read_i64, write_i64);
ray!(Ray128, i128, 128, read_i128, write_i128);

/// A residue on a path of `W` places (`Z/2^W`, the low section), carried in a `u64`: each operation returns its winding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Path64<const W: u32>(u64);

impl<const W: u32> Path64<W> {
    const MASK: u64 = if W >= 64 { u64::MAX } else { (1u64 << W) - 1 };
    const FITS: () = assert!(W >= 1 && W <= 64, "a path past its word");

    /// The declared read of a native word's low `W` places, refused where it has more.
    pub fn read_u64(x: u64) -> Result<Self> {
        let () = Self::FITS;
        if x & !Self::MASK != 0 {
            return refuse("a path's read outside its places");
        }
        Ok(Self(x))
    }

    pub fn write_u64(self) -> u64 {
        self.0
    }

    /// The sum on the path and its winding (the carry that left the top place): one native add and its flag at `W = 64`.
    #[inline]
    pub fn add(self, other: Self) -> (Self, u64) {
        if W == 64 {
            let (s, c) = self.0.overflowing_add(other.0);
            (Self(s), u64::from(c))
        } else {
            let s = self.0 + other.0;
            (Self(s & Self::MASK), s >> W)
        }
    }

    /// The product on the path and its winding, `⌊ab / 2^W⌋` (the high word at `W = 64`).
    #[inline]
    pub fn mul(self, other: Self) -> (Self, u64) {
        let p = u128::from(self.0) * u128::from(other.0);
        (Self((p as u64) & Self::MASK), (p >> W) as u64)
    }
}

/// Probes whose machine code the realization's acceptance reads (theory, November 8: a ray add fitting its preset is one
/// add, a path add is the native add and its flag, an accumulation loop is the native loop).
#[doc(hidden)]
pub mod probe {
    use super::{Path64, Ray64};

    #[inline(never)]
    pub fn ray_add(a: Ray64<31, 0>, b: Ray64<31, 0>) -> Ray64<32, 0> {
        a.add(b)
    }

    #[inline(never)]
    pub fn native_add(a: i64, b: i64) -> i64 {
        a + b
    }

    #[inline(never)]
    pub fn path_add(a: Path64<64>, b: Path64<64>) -> (Path64<64>, u64) {
        a.add(b)
    }

    #[inline(never)]
    pub fn native_overflowing_add(a: u64, b: u64) -> (u64, bool) {
        a.overflowing_add(b)
    }

    #[inline(never)]
    pub fn ray_sum(xs: &[Ray64<40, 0>]) -> Option<Ray64<62, 0>> {
        Ray64::sum(xs).ok()
    }

    #[inline(never)]
    pub fn native_sum(xs: &[i64]) -> i64 {
        xs.iter().sum()
    }
}
