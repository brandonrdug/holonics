//! **The typed realization** (theory, November 8): under N3 every width is a law constant, so no width is held at run
//! time. A class whose width the law fixes is a type, [`Ray64`] or [`Ray128`]: `W` places at grain `2^LO` in its section
//! (`S` false: the low section `[0, 2^W)`; `S` true: two's complement `[−2^(W−1), 2^(W−1))`), carried in the native word the
//! preset names. Each operation names its result's width and section in its type, and an inline const assertion checks
//! at build time that they are the law's need, equal to it (a wider result is a declared crossing, [`Ray64::widen`]), and
//! that they fit the word; the run-time body is the native operation on the word's bits, which is one instruction for
//! either section. An accumulation checks its terms' width plus `⌈log₂ n⌉` once at its loop head and adds natively
//! inside. A path's residue ([`Path64`]) returns its winding with the native overflow flag.
//!
//! **N3's cross rules, typed** (theory, November 8 02:51): low + low is low at the wider plus one; low − low is signed at
//! the wider plus one; a sum or difference mixing a low and a signed operand is signed at `max(w_low + 1, w_signed) + 1`;
//! low × low is low at `w_a + w_b`; a product with a signed operand is signed at `w_a + w_b` (the sign comes from the signed
//! operand alone, so the low one enters at its own places); a negation is signed one place wider. So `u32 × u32` is one
//! native multiply into a `u64`, `Low<32> × Low<32> → Low<64>`.
//!
//! **A release's widths depend on its rule**: releasing `K` places of a signed class of `W`, floor gives `(W − K, low K)`,
//! nearest with ties up `(W − K + 1, signed K)`, and ceiling, nearest away and nearest even `(W − K + 1, signed K + 1)` (away
//! and even reach `+2^(K−1)`, ceiling spans `2^K − 1` below zero); a low class's quotient stays low.
//!
//! [`super::Value`] stays the general form, for widths a law does not fix; the two meet only by the declared maps
//! [`Ray64::value`] and [`Ray64::of_value`].

use super::value::{Digits, Section};
use super::{refuse, Grain, Result, Value, Width};

const fn max(a: u32, b: u32) -> u32 {
    if a > b {
        a
    } else {
        b
    }
}

/// The need of a sum: `(places, signed)`.
pub const fn sum_need(wa: u32, sa: bool, wb: u32, sb: bool) -> (u32, bool) {
    match (sa, sb) {
        (false, false) => (max(wa, wb) + 1, false),
        (true, true) => (max(wa, wb) + 1, true),
        (false, true) => (max(wa + 1, wb) + 1, true),
        (true, false) => (max(wa, wb + 1) + 1, true),
    }
}

/// The need of a difference: always signed.
pub const fn difference_need(wa: u32, sa: bool, wb: u32, sb: bool) -> (u32, bool) {
    match (sa, sb) {
        (false, false) | (true, true) => (max(wa, wb) + 1, true),
        (false, true) => (max(wa + 1, wb) + 1, true),
        (true, false) => (max(wa, wb + 1) + 1, true),
    }
}

/// The need of a product: the widths added, signed where either operand is.
pub const fn product_need(wa: u32, sa: bool, wb: u32, sb: bool) -> (u32, bool) {
    (wa + wb, sa || sb)
}

/// The rounding a typed release names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rule {
    Floor,
    Ceiling,
    NearestUp,
    NearestAway,
    NearestEven,
}

/// The need of a release of `k` places of a class of `w` in section `s` by `rule`: the quotient's `(places, signed)` and
/// the remainder's.
pub const fn release_need(rule: Rule, w: u32, s: bool, k: u32) -> ((u32, bool), (u32, bool)) {
    match rule {
        Rule::Floor => ((w - k, s), (k, false)),
        Rule::NearestUp => ((w - k + 1, s), (k, true)),
        Rule::Ceiling | Rule::NearestAway | Rule::NearestEven => ((w - k + 1, s), (k + 1, true)),
    }
}

macro_rules! ray {
    ($name:ident, $bits_ty:ty, $signed_ty:ty, $bits:expr, $read_low:ident, $read_signed:ident, $write_low:ident, $write_signed:ident) => {
        /// A class of `W` places at grain `2^LO` in the section `S` (false low, true two's complement), its digits carried
        /// in a native word's bits.
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        #[repr(transparent)]
        pub struct $name<const W: u32, const LO: i32, const S: bool>($bits_ty);

        impl<const W: u32, const LO: i32, const S: bool> $name<W, LO, S> {
            const FITS: () = assert!(W >= 1 && W <= $bits, "a width past its word");

            /// The digits read in the section (the low section's word read unsigned, as `i128` where it is wider than
            /// a signed word holds).
            fn digits(self) -> i128 {
                if S {
                    self.0 as $signed_ty as i128
                } else {
                    self.0 as i128
                }
            }

            fn inside(x: i128) -> bool {
                if S {
                    W >= 128 || (x >= -(1i128 << (W - 1)) && x < (1i128 << (W - 1)))
                } else {
                    // A low class of all of a 128-place word's places reads past `i128`: its word holds it whole.
                    W >= 127 || (x >= 0 && x < (1i128 << W))
                }
            }

            /// The class's digits as the native signed word (exact there by the type's width: a low class of all the
            /// word's places is refused).
            pub fn $write_signed(self) -> Result<$signed_ty> {
                if !S && W == $bits && (self.0 >> ($bits - 1)) != 0 {
                    return refuse("a low class past the signed word's places");
                }
                Ok(self.0 as $signed_ty)
            }

            /// The class's digits as the native unsigned word (refused for a negative class).
            pub fn $write_low(self) -> Result<$bits_ty> {
                if S && (self.0 as $signed_ty) < 0 {
                    return refuse("a negative class in the low section");
                }
                Ok(self.0)
            }

            /// The sum, its width and section the law's need (checked at compile time, equal to it).
            #[inline]
            pub fn add<const B: u32, const SB: bool, const C: u32, const SC: bool>(self, other: $name<B, LO, SB>) -> $name<C, LO, SC> {
                const {
                    let need = sum_need(W, S, B, SB);
                    assert!(C == need.0 && SC == need.1 && C <= $bits, "a sum's width or section not its need, or past its word")
                };
                let r = $name(self.0.wrapping_add(other.0));
                debug_assert!($name::<C, LO, SC>::inside(r.digits()));
                r
            }

            /// The difference, signed, its width the law's need.
            #[inline]
            pub fn sub<const B: u32, const SB: bool, const C: u32>(self, other: $name<B, LO, SB>) -> $name<C, LO, true> {
                const {
                    let need = difference_need(W, S, B, SB);
                    assert!(C == need.0 && C <= $bits, "a difference's width not its need, or past its word")
                };
                let r = $name(self.0.wrapping_sub(other.0));
                debug_assert!($name::<C, LO, true>::inside(r.digits()));
                r
            }

            /// The negation, signed, one place wider.
            #[inline]
            pub fn neg<const C: u32>(self) -> $name<C, LO, true> {
                const { assert!(C == W + 1 && C <= $bits, "a negation's width not its need, or past its word") };
                $name(self.0.wrapping_neg())
            }

            /// The product at grain `LO + LB`, its width the two widths added, signed where either operand is: the word's
            /// low product, one instruction for either section.
            #[inline]
            pub fn mul<const B: u32, const LB: i32, const SB: bool, const C: u32, const LC: i32, const SC: bool>(
                self,
                other: $name<B, LB, SB>,
            ) -> $name<C, LC, SC> {
                const {
                    let need = product_need(W, S, B, SB);
                    assert!(C == need.0 && SC == need.1 && C <= $bits && LC == LO + LB, "a product's width, section or grain not its need, or past its word")
                };
                let r = $name(self.0.wrapping_mul(other.0));
                debug_assert!($name::<C, LC, SC>::inside(r.digits()));
                r
            }

            /// The same class at more places (the declared crossing: a width is a need, so a wider one is named).
            #[inline]
            pub fn widen<const C: u32>(self) -> $name<C, LO, S> {
                const { assert!(C >= W && C <= $bits, "a widening to fewer places") };
                $name(self.0)
            }

            /// A low class read in the signed section, one place wider (the section change).
            #[inline]
            pub fn signed<const C: u32>(self) -> $name<C, LO, true> {
                const { assert!(!S && C == W + 1 && C <= $bits, "a section change's width not its need") };
                $name(self.0)
            }

            /// The same class read `K` places finer (`LC = LO − K`).
            #[inline]
            pub fn finer<const K: u32, const C: u32, const LC: i32>(self) -> $name<C, LC, S> {
                const { assert!(C == W + K && C <= $bits && LC == LO - K as i32, "a finer grain's width not its need") };
                $name(self.0 << K)
            }

            /// The floor's quotient and remainder, then one step up where `rule` rounds up: no addition leaves the word.
            #[inline]
            fn released(self, rule: Rule, k: u32) -> ($bits_ty, $bits_ty) {
                let mask: $bits_ty = ((1 as $bits_ty) << k) - 1;
                let q0 = if S { ((self.0 as $signed_ty) >> k) as $bits_ty } else { self.0 >> k };
                let r0 = self.0 & mask;
                let half: $bits_ty = (1 as $bits_ty) << (k - 1);
                let negative = S && (self.0 as $signed_ty) < 0;
                let up = match rule {
                    Rule::Floor => false,
                    Rule::Ceiling => r0 != 0,
                    Rule::NearestUp => r0 >= half,
                    Rule::NearestAway => r0 > half || (r0 == half && !negative),
                    Rule::NearestEven => r0 > half || (r0 == half && q0 & 1 == 1),
                };
                let q = q0.wrapping_add(<$bits_ty>::from(up));
                let r = if up { r0.wrapping_sub(mask).wrapping_sub(1) } else { r0 };
                (q, r)
            }

            /// **The release** of `K` places to the floor: `value · 2^K + remainder = self`, the quotient at `W − K`
            /// places in this section, the remainder low at `K`.
            #[inline]
            pub fn release_floor<const K: u32, const CQ: u32, const LQ: i32>(self) -> ($name<CQ, LQ, S>, $name<K, LO, false>) {
                const {
                    let need = release_need(Rule::Floor, W, S, K);
                    assert!(K >= 1 && K < W && LQ == LO + K as i32 && CQ == need.0 .0, "a release's grain or places not its rule's need")
                };
                let (q, r) = self.released(Rule::Floor, K);
                ($name(q), $name(r))
            }

            /// The release of `K` places to the nearest, ties up (the field's present release): the quotient at `W − K + 1`
            /// places, the remainder signed at `K`, in `[−2^(K−1), 2^(K−1))`.
            #[inline]
            pub fn release_nearest_up<const K: u32, const CQ: u32, const LQ: i32>(self) -> ($name<CQ, LQ, S>, $name<K, LO, true>) {
                const {
                    let need = release_need(Rule::NearestUp, W, S, K);
                    assert!(K >= 1 && K < W && LQ == LO + K as i32 && CQ == need.0 .0 && CQ <= $bits, "a release's grain or places not its rule's need")
                };
                let (q, r) = self.released(Rule::NearestUp, K);
                ($name(q), $name(r))
            }

            /// The release of `K` places by a rule whose remainder reaches `±2^(K−1)` or spans `2^K − 1` below zero (ceiling,
            /// nearest away, nearest even): the quotient at `W − K + 1` places, the remainder signed at `K + 1`.
            #[inline]
            pub fn release_by<const K: u32, const CQ: u32, const LQ: i32, const CR: u32>(self, rule: Rule) -> Result<($name<CQ, LQ, S>, $name<CR, LO, true>)> {
                const { assert!(K >= 1 && K < W && LQ == LO + K as i32 && CQ == W - K + 1 && CQ <= $bits && CR == K + 1 && CR <= $bits, "a release's grain or places not its rule's need") };
                if matches!(rule, Rule::Floor | Rule::NearestUp) {
                    return refuse("floor and nearest-up releases have their own widths (release_floor, release_nearest_up)");
                }
                let (q, r) = self.released(rule, K);
                Ok(($name(q), $name(r)))
            }

            /// **An accumulation** of terms into a class of `C` places in the terms' section, checked once at its head
            /// (`n ≤ 2^(C − W)`, which is `⌈log₂ n⌉ ≤ C − W`), the native adds inside.
            pub fn sum<const C: u32>(terms: &[Self]) -> Result<$name<C, LO, S>> {
                const { assert!(C >= W && C <= $bits, "an accumulation past its word or below its terms") };
                if C - W < usize::BITS && terms.len() > (1usize << (C - W)) {
                    return refuse("an accumulation whose terms' need passes its declared width");
                }
                Ok($name(terms.iter().fold(0 as $bits_ty, |acc, t| acc.wrapping_add(t.0))))
            }

            /// The class as a value of the general form (a declared map).
            pub fn value(self) -> Result<Value> {
                let (section, digits) =
                    if S { (Section::TwosComplement, num_bigint::BigInt::from(self.0 as $signed_ty)) } else { (Section::Low, num_bigint::BigInt::from(self.0)) };
                Value::of(Grain::new(LO), Width::new(W), section, Digits::from_big(digits))
            }

            /// A value of the general form at this grain read as this type, refused where its class lies outside it.
            pub fn of_value(v: &Value) -> Result<Self> {
                let v = v.at_grain(Grain::new(LO))?;
                let x = match v.digits {
                    Digits::Small(x) => x,
                    Digits::Big(_) => return refuse("a value outside the type's places"),
                };
                if !Self::inside(x) {
                    return refuse("a value outside the type's places");
                }
                Ok(Self(x as $bits_ty))
            }
        }

        impl<const W: u32, const LO: i32> $name<W, LO, false> {
            /// **The declared read** of a native unsigned word as a low class of `W` places, refused outside them.
            pub fn $read_low(x: $bits_ty) -> Result<Self> {
                let () = Self::FITS;
                if W < $bits && x >> W != 0 {
                    return refuse("a read outside its declared places");
                }
                Ok(Self(x))
            }
        }

        impl<const W: u32, const LO: i32> $name<W, LO, true> {
            /// **The declared read** of a native signed word as a signed class of `W` places, refused outside them.
            pub fn $read_signed(x: $signed_ty) -> Result<Self> {
                let () = Self::FITS;
                if W < $bits && (x < -(1 << (W - 1)) || x >= (1 << (W - 1))) {
                    return refuse("a read outside its declared places");
                }
                Ok(Self(x as $bits_ty))
            }
        }
    };
}

ray!(Ray64, u64, i64, 64, read_u64, read_i64, write_u64, write_i64);
ray!(Ray128, u128, i128, 128, read_u128, read_i128, write_u128, write_i128);

/// A low class (`[0, 2^W)`) carried in a `u64`.
pub type Low64<const W: u32, const LO: i32> = Ray64<W, LO, false>;
/// A signed class (`[−2^(W−1), 2^(W−1))`) carried in a `u64`'s bits, read as `i64`.
pub type Signed64<const W: u32, const LO: i32> = Ray64<W, LO, true>;
/// A low class carried in a `u128`.
pub type Low128<const W: u32, const LO: i32> = Ray128<W, LO, false>;
/// A signed class carried in a `u128`'s bits, read as `i128`.
pub type Signed128<const W: u32, const LO: i32> = Ray128<W, LO, true>;

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
/// add, a path add is the native add and its flag, an accumulation loop is the native loop, `u32 × u32` one multiply).
#[doc(hidden)]
pub mod probe {
    use super::{Low64, Path64, Signed64};

    #[inline(never)]
    pub fn ray_add(a: Signed64<31, 0>, b: Signed64<31, 0>) -> Signed64<32, 0> {
        a.add(b)
    }

    #[inline(never)]
    pub fn native_add(a: i64, b: i64) -> i64 {
        a + b
    }

    #[inline(never)]
    pub fn low_mul(a: Low64<32, 0>, b: Low64<32, 0>) -> Low64<64, 0> {
        a.mul(b)
    }

    #[inline(never)]
    pub fn native_u32_mul(a: u32, b: u32) -> u64 {
        u64::from(a) * u64::from(b)
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
    pub fn ray_sum(xs: &[Signed64<40, 0>]) -> Option<Signed64<62, 0>> {
        Signed64::sum(xs).ok()
    }

    #[inline(never)]
    pub fn native_sum(xs: &[i64]) -> i64 {
        xs.iter().sum()
    }
}
