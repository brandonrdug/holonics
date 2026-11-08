//! The number owner's laws, each against the native word it replaces inside native range and against
//! `BigInt` beyond it (theory's build step 1: bit for bit, preset by preset, cut pattern by cut pattern).

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};

use super::value::Digits;
use super::*;

/// A deterministic walk over words (splitmix64), so every property reads the same draws on every run.
struct Walk(u64);

impl Walk {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A word whose used places are themselves drawn, so narrow and wide classes both occur.
    fn word(&mut self) -> u64 {
        let x = self.next();
        let keep = (self.next() % 65) as u32;
        if keep == 64 {
            x
        } else {
            x & ((1u64 << keep) - 1)
        }
    }

    fn wide(&mut self) -> u128 {
        let hi = u128::from(self.word());
        let lo = u128::from(self.next());
        if self.next() % 2 == 0 {
            (hi << 64) | lo
        } else {
            lo
        }
    }
}

const DRAWS: usize = 4096;

/// A value's class at grain one (its grain no finer than one).
fn class(v: &Value) -> BigInt {
    assert!(v.grain().lo() >= 0);
    v.digits.big() << v.grain().lo() as usize
}

fn ray(x: BigInt) -> Value {
    let d = Digits::from_big(x);
    let w = d.places_in(Section::TwosComplement).max(1);
    Value::of(Grain::new(0), Width::new(w), Section::TwosComplement, d).unwrap()
}

fn unwound(w: &Winding) -> bool {
    w.0.is_zero()
}

#[test]
fn a_width_registers_at_its_binary_planes() {
    assert_eq!(Width::new(11).planes(), vec![8, 2, 1]);
    assert_eq!(Width::new(64).planes(), vec![64]);
    assert_eq!(Width::of_terms(Width::new(11), Count::new(5)), Width::new(14));
    assert_eq!(Width::of_terms(Width::new(11), Count::new(1)), Width::new(11));
}

#[test]
fn each_preset_reads_and_writes_its_native_word() {
    let mut walk = Walk(1);
    for _ in 0..DRAWS {
        let x = walk.next();
        let (b, w) = Register::u64().write_u64(&Register::u64().read_u64(x).unwrap()).unwrap();
        assert_eq!((b, unwound(&w)), (x, true));
        let (b, w) = Register::i64().write_i64(&Register::i64().read_i64(x as i64).unwrap()).unwrap();
        assert_eq!((b, unwound(&w)), (x as i64, true));
        let v = Register::i64().read_i64(x as i64).unwrap();
        assert_eq!(class(&v), BigInt::from(x as i64));
        let y = x as u32;
        let (b, w) = Register::u32().write_u64(&Register::u32().read_u32(y).unwrap()).unwrap();
        assert_eq!((b as u32, unwound(&w)), (y, true));
        let (b, w) = Register::i32().write_i64(&Register::i32().read_i32(y as i32).unwrap()).unwrap();
        assert_eq!((b as u32 as i32, unwound(&w)), (y as i32, true));
        let z = walk.wide();
        let (b, w) = Register::u128().write_u128(&Register::u128().read_u128(z).unwrap()).unwrap();
        assert_eq!((b, unwound(&w)), (z, true));
        let (b, w) = Register::i128().write_i128(&Register::i128().read_i128(z as i128).unwrap()).unwrap();
        assert_eq!((b, unwound(&w)), (z as i128, true));
    }
}

/// Inside native range each preset's sum, difference and product, written back, is the native wrapping
/// word, and its winding is nonzero just where the native operation overflows.
#[test]
fn each_preset_writes_the_native_wrap_with_its_winding() {
    let mut walk = Walk(2);
    for _ in 0..DRAWS {
        let (a, b) = (walk.word(), walk.word());
        let (u, i) = (Register::u64(), Register::i64());
        let (ua, ub) = (u.read_u64(a).unwrap(), u.read_u64(b).unwrap());
        let (ia, ib) = (i.read_i64(a as i64).unwrap(), i.read_i64(b as i64).unwrap());

        let (s, w) = u.write_u64(&ua.add(&ub).unwrap()).unwrap();
        assert_eq!((s, !unwound(&w)), a.overflowing_add(b));
        let (s, w) = u.write_u64(&ua.sub(&ub).unwrap()).unwrap();
        assert_eq!((s, !unwound(&w)), a.overflowing_sub(b));
        let (s, w) = u.write_u64(&ua.mul(&ub).unwrap()).unwrap();
        assert_eq!((s, !unwound(&w)), a.overflowing_mul(b));

        let (a, b) = (a as i64, b as i64);
        let (s, w) = i.write_i64(&ia.add(&ib).unwrap()).unwrap();
        assert_eq!((s, !unwound(&w)), a.overflowing_add(b));
        let (s, w) = i.write_i64(&ia.sub(&ib).unwrap()).unwrap();
        assert_eq!((s, !unwound(&w)), a.overflowing_sub(b));
        let (s, w) = i.write_i64(&ia.mul(&ib).unwrap()).unwrap();
        assert_eq!((s, !unwound(&w)), a.overflowing_mul(b));
        let (s, w) = i.write_i64(&ia.neg().unwrap()).unwrap();
        assert_eq!((s, !unwound(&w)), a.overflowing_neg());

        let (c, d) = (walk.wide(), walk.wide());
        let (u, i) = (Register::u128(), Register::i128());
        let (s, w) = u.write_u128(&u.read_u128(c).unwrap().mul(&u.read_u128(d).unwrap()).unwrap()).unwrap();
        assert_eq!((s, !unwound(&w)), c.overflowing_mul(d));
        let (s, w) = i.write_i128(&i.read_i128(c as i128).unwrap().add(&i.read_i128(d as i128).unwrap()).unwrap()).unwrap();
        assert_eq!((s, !unwound(&w)), (c as i128).overflowing_add(d as i128));
    }
}

/// Beyond native range the classes are `BigInt`'s, and each operation's width is its need: the class fits it.
#[test]
fn beyond_native_range_the_class_is_the_big_integers() {
    let mut walk = Walk(3);
    for _ in 0..DRAWS {
        let (a, b, c) = (walk.wide() as i128, walk.wide() as i128, walk.wide() as i128);
        let i = Register::i128();
        let (va, vb, vc) = (i.read_i128(a).unwrap(), i.read_i128(b).unwrap(), i.read_i128(c).unwrap());
        let p = va.mul(&vb).unwrap().mul(&vc).unwrap();
        assert_eq!(class(&p), BigInt::from(a) * BigInt::from(b) * BigInt::from(c));
        assert!(p.used() <= p.width());
        assert_eq!(p.width(), Width::new(3 * 128));
        let s = p.add(&va).unwrap().sub(&p).unwrap();
        assert!(s.same(&va));
        // The sum's width (the wider plus one) and the product's (the two added) are needs, never picked.
        assert_eq!(va.add(&vb).unwrap().width(), Width::new(129));
    }
}

/// Mixed sections need the low operand's signed places: `3 + 1` and `−2 − 3` at two places each, and many
/// low terms beside one signed term, all fit the widths the law derives.
#[test]
fn mixed_sections_take_the_low_operands_signed_places() {
    let low = |x: u64, w: u32| Value::of(Grain::new(0), Width::new(w), Section::Low, Digits::Small(i128::from(x))).unwrap();
    let signed = |x: i64, w: u32| Value::of(Grain::new(0), Width::new(w), Section::TwosComplement, Digits::Small(i128::from(x))).unwrap();
    let s = low(3, 2).add(&signed(1, 2)).unwrap();
    assert_eq!((class(&s), s.width(), s.section()), (BigInt::from(4), Width::new(4), Section::TwosComplement));
    let d = signed(-2, 2).sub(&low(3, 2)).unwrap();
    assert_eq!(class(&d), BigInt::from(-5));
    assert!(d.used() <= d.width());
    let d = low(0, 2).sub(&low(3, 2)).unwrap();
    assert_eq!((class(&d), d.width()), (BigInt::from(-3), Width::new(3)));
    let mut walk = Walk(13);
    for _ in 0..DRAWS {
        let (wa, wb) = ((walk.next() % 64) as u32 + 1, (walk.next() % 64) as u32 + 1);
        let a = low(walk.next() & if wa == 64 { u64::MAX } else { (1 << wa) - 1 }, wa);
        let b = signed((walk.next() as i64) >> (64 - wb), wb);
        for v in [a.add(&b).unwrap(), b.add(&a).unwrap(), a.sub(&b).unwrap(), b.sub(&a).unwrap(), a.mul(&b).unwrap()] {
            assert!(v.used() <= v.width());
        }
        let terms = vec![a.clone(), a.clone(), b.clone(), a];
        let total = Value::sum(&terms).unwrap();
        assert!(total.used() <= total.width());
        let mut acc = Accumulation::at(Grain::new(0));
        terms.iter().for_each(|t| acc.add(t).unwrap());
        assert_eq!(acc.value().unwrap(), total);
    }
}

/// The section change and the sign extension are declared maps that keep the class.
#[test]
fn the_section_change_and_sign_extension_keep_the_class() {
    let mut walk = Walk(4);
    for _ in 0..DRAWS {
        let x = walk.next() as u32 as i32;
        let v = Register::i32().read_i32(x).unwrap();
        let wide = Register::i32().extend(&v, &Register::i64()).unwrap();
        let (b, w) = Register::i64().write_i64(&wide).unwrap();
        assert_eq!((b, unwound(&w)), (i64::from(x), true));
        let u = Register::u64().read_u64(walk.next()).unwrap();
        let signed = u.in_section(Section::TwosComplement).unwrap();
        assert!(signed.same(&u));
        assert!(signed.width().places() <= 65);
        assert!(Register::i64().read_i64(-1).unwrap().in_section(Section::Low).is_err());
    }
    assert!(Register::i64().extend(&Register::i64().read_i64(1).unwrap(), &Register::i32()).is_err());
}

/// The cut add on packed fields is each field's own wrapping add: every edge cut is XOR, none the word's add.
#[test]
fn the_cut_add_is_the_lane_by_lane_add() {
    let mut walk = Walk(5);
    for _ in 0..DRAWS {
        let mut widths = Vec::new();
        let mut left = 64u32;
        while left > 0 {
            let w = ((walk.next() % 16) as u32 + 1).min(left);
            widths.push(w);
            left -= w;
        }
        let reg = Register::lanes(&widths).unwrap();
        let (x, y) = (walk.next(), walk.next());
        let mut want = 0u64;
        let mut at = 0u32;
        for &w in &widths {
            let mask = if w == 64 { u64::MAX } else { (1u64 << w) - 1 };
            let f = ((x >> at) & mask).wrapping_add((y >> at) & mask) & mask;
            want |= f << at;
            at += w;
        }
        let got = reg.add_packed(x, y).unwrap();
        assert_eq!(got, want);
        let fields = reg.read_fields(got).unwrap();
        let back = fields.iter().zip(&widths).scan(0u32, |at, (f, &w)| {
            let v = class(f) << *at as usize;
            *at += w;
            Some(v)
        });
        assert_eq!(back.sum::<BigInt>(), BigInt::from(got));
        assert_eq!(reg.write_fields(&fields).unwrap(), got);
    }
    let (x, y) = (0xDEAD_BEEF_0123_4567u64, 0x0F0F_F0F0_AAAA_5555u64);
    assert_eq!(Register::lanes(&[1; 64]).unwrap().add_packed(x, y).unwrap(), x ^ y);
    assert_eq!(Register::lanes(&[64]).unwrap().add_packed(x, y).unwrap(), x.wrapping_add(y));
    assert!(Register::lanes(&[60, 8]).is_err());
}

/// A release recomposes its class, `value · 2^k + remainder = x`, under every rule, and each rule's quotient
/// is its own descent: floor and ceiling bound the remainder on one side, nearest within half, its tie broken
/// as declared.
#[test]
fn a_release_recomposes_its_class_under_each_rule() {
    let mut walk = Walk(6);
    let rules = [Rounding::Floor, Rounding::Ceiling, Rounding::Nearest(Tie::Up), Rounding::Nearest(Tie::Even), Rounding::Nearest(Tie::Away)];
    for n in 0..DRAWS {
        let x = if n % 7 == 0 { (walk.next() as i128) << 3 } else { walk.wide() as i128 };
        let k = (walk.next() % 131) as u32 + 1;
        let v = Register::i128().read_i128(x).unwrap();
        let big = BigInt::from(x);
        let unit = BigInt::one() << k as usize;
        let (fq, fr) = big.div_mod_floor(&unit);
        for rule in rules {
            let r = release(&v, k, rule).unwrap();
            assert_eq!(r.value.grain().lo(), k as i32);
            assert_eq!(r.remainder.grain().lo(), 0);
            let q = r.value.digits.big();
            let rem = r.remainder.digits.big();
            assert_eq!(&q * &unit + &rem, big, "recomposition at k = {k}, {rule:?}");
            let twice = BigInt::from(2) * &fr;
            let want = match rule {
                Rounding::Floor => fq.clone(),
                Rounding::Ceiling => &fq + u32::from(!fr.is_zero()),
                Rounding::Nearest(tie) => {
                    let up = match twice.cmp(&unit) {
                        std::cmp::Ordering::Greater => true,
                        std::cmp::Ordering::Less => false,
                        std::cmp::Ordering::Equal => match tie {
                            Tie::Up => true,
                            Tie::Even => fq.is_odd(),
                            Tie::Away => !big.is_negative(),
                        },
                    };
                    &fq + u32::from(up)
                }
            };
            assert_eq!(q, want, "quotient at k = {k}, {rule:?}");
            if k < 127 && rule == Rounding::Floor {
                assert_eq!(q, BigInt::from(x >> k));
            }
            assert!(r.value.used() <= r.value.width());
        }
    }
    // A tie at k = 1: 5/2 and −5/2, each rule's own quotient.
    let five = Register::i64().read_i64(5).unwrap();
    let neg = Register::i64().read_i64(-5).unwrap();
    let q = |v: &Value, t| release(v, 1, Rounding::Nearest(t)).unwrap().value.digits.big();
    assert_eq!((q(&five, Tie::Up), q(&five, Tie::Even), q(&five, Tie::Away)), (3.into(), 2.into(), 3.into()));
    assert_eq!((q(&neg, Tie::Up), q(&neg, Tie::Even), q(&neg, Tie::Away)), ((-2).into(), (-2).into(), (-3).into()));
}

/// Every reduction onto a closing edge returns its winding: `x = winding · m + residue`, `0 ≤ residue < m`,
/// and residue sums and products are the reduced class.
#[test]
fn each_closing_returns_its_winding() {
    let mut walk = Walk(7);
    for _ in 0..DRAWS {
        let n = (walk.next() % 70) as u32 + 2;
        let c = walk.next() % (1u64 << n.min(40)).max(2);
        let m = (walk.next() % u64::from(n - 1)) as u32 + 1;
        let closings = [Closing::Path(n), Closing::Ring(n), Closing::Twist(n), Closing::Weighted(n, c.max(1)), Closing::Solinas(n, vec![m, 0])];
        let a = ray(BigInt::from(walk.wide() as i128));
        let b = ray(BigInt::from(walk.wide() as i128));
        for closing in closings {
            let modulus = closing.modulus().unwrap();
            if modulus <= BigInt::zero() {
                assert!(Residue::of(&a, &closing).is_err());
                continue;
            }
            let (ra, wa) = Residue::of(&a, &closing).unwrap();
            let r = ra.lanes[0].digits.big();
            assert_eq!(class(&wa[0].0) * &modulus + &r, class(&a));
            assert!(!r.is_negative() && r < modulus);
            let (rb, _) = Residue::of(&b, &closing).unwrap();
            let (s, _) = ra.add(&rb).unwrap();
            assert_eq!(s.lanes[0].digits.big(), (class(&a) + class(&b)).mod_floor(&modulus));
            let (p, _) = ra.mul(&rb).unwrap();
            assert_eq!(p.lanes[0].digits.big(), (class(&a) * class(&b)).mod_floor(&modulus));
        }
    }
}

/// Coprime rings carry no carry between their lanes, and the mixed-radix reconstruction returns the class
/// modulo their product.
#[test]
fn coprime_rings_reconstruct_their_class() {
    let mut walk = Walk(8);
    let rings = Closing::Rings(vec![5, 6, 7, 11]);
    let product: BigInt = [5u32, 6, 7, 11].iter().map(|&n| (BigInt::one() << n as usize) - 1).product();
    for _ in 0..DRAWS {
        let a = ray(BigInt::from(walk.wide() as i128));
        let b = ray(BigInt::from(walk.next() as i64));
        let (ra, _) = Residue::of(&a, &rings).unwrap();
        assert_eq!(ra.reconstruct().unwrap().digits.big(), class(&a).mod_floor(&product));
        let (rb, _) = Residue::of(&b, &rings).unwrap();
        let (p, _) = ra.mul(&rb).unwrap();
        assert_eq!(p.reconstruct().unwrap().digits.big(), (class(&a) * class(&b)).mod_floor(&product));
    }
    assert!(Residue::of(&ray(BigInt::from(3)), &Closing::Rings(vec![4, 6])).is_err());
}

/// Each end of the inversion returns its residual with its certificate: the bottom end's `aX ≡ 1 (mod 2^w)`
/// against the native Hensel word, the top end's lattice reciprocal `X = ⌊2^p / a⌋` with `0 ≤ E < a`, and
/// Euclid's `aX ≡ 1 (mod m)` or its refusal where `a` shares a factor with `m`.
#[test]
fn each_end_of_the_inversion_certifies_its_residual() {
    let mut walk = Walk(9);
    for _ in 0..DRAWS {
        let a = walk.next() | 1;
        let inv = invert(&Register::u64().read_u64(a).unwrap(), End::Bottom(64)).unwrap();
        let (x, _) = Register::u64().write_u64(&inv.x).unwrap();
        assert_eq!(a.wrapping_mul(x), 1);
        assert_eq!(inv.steps, 4);
        for w in [1u32, 3, 5, 6, 33, 100, 128] {
            let a = walk.wide() | 1;
            let inv = invert(&Register::u128().read_u128(a).unwrap(), End::Bottom(w)).unwrap();
            let m = BigInt::one() << w as usize;
            assert!((BigInt::from(a) * inv.x.digits.big()).mod_floor(&m).is_one(), "w = {w}");
        }

        let d = walk.wide().max(1);
        let p = (walk.next() % 300) as u32;
        let inv = invert(&Register::u128().read_u128(d).unwrap(), End::Top(p)).unwrap();
        let target = BigInt::one() << p as usize;
        let (q, e) = target.div_mod_floor(&BigInt::from(d));
        assert_eq!((inv.x.digits.big(), inv.residual.digits.big()), (q, e));
        assert_eq!(inv.x.grain().lo(), -(p as i32));

        let m = walk.word().max(2);
        let b = walk.next() % m;
        let modulus = Register::u64().read_u64(m).unwrap();
        let r = invert(&Register::u64().read_u64(b).unwrap(), End::Euclid(modulus));
        if BigInt::from(b).gcd(&BigInt::from(m)).is_one() {
            let x = r.unwrap().x.digits.big();
            assert_eq!((BigInt::from(b) * x).mod_floor(&BigInt::from(m)), BigInt::one());
        } else {
            assert!(r.is_err());
        }
    }
    assert!(invert(&Register::u64().read_u64(6).unwrap(), End::Bottom(64)).is_err());
    assert!(invert(&Register::u64().read_u64(3).unwrap(), End::Matrix).is_err());
}

/// An accumulation gives one class under every order and bracketing of its terms, and its width is the
/// widest term's plus `⌈log₂ terms⌉`: the redundant fibre form and the canonical sum agree.
#[test]
fn an_accumulation_is_the_same_under_every_bracketing() {
    let mut walk = Walk(10);
    for _ in 0..64 {
        let n = (walk.next() % 300) as usize + 1;
        let terms: Vec<Value> = (0..n)
            .map(|_| {
                let v = Register::i64().read_i64(walk.word() as i64).unwrap();
                v.scaled((walk.next() % 5) as i32).unwrap()
            })
            .collect();
        let mut forward = Accumulation::at(Grain::new(0));
        terms.iter().for_each(|t| forward.add(t).unwrap());
        let mut backward = Accumulation::at(Grain::new(0));
        terms.iter().rev().for_each(|t| backward.add(t).unwrap());
        let cut = (walk.next() as usize) % n;
        let (mut left, mut right) = (Accumulation::at(Grain::new(0)), Accumulation::at(Grain::new(0)));
        terms[..cut].iter().for_each(|t| left.add(t).unwrap());
        terms[cut..].iter().rev().for_each(|t| right.add(t).unwrap());
        right.join(&left).unwrap();
        let canonical = Value::sum(&terms).unwrap();
        assert_eq!(forward.value().unwrap(), backward.value().unwrap());
        assert_eq!(forward.value().unwrap(), right.value().unwrap());
        assert!(forward.value().unwrap().same(&canonical));
        let want: BigInt = terms.iter().map(class).sum();
        assert_eq!(class(&forward.value().unwrap()), want);
        assert_eq!(forward.terms(), Count::new(n as u64));
    }
}

/// A shear carries its inverse: applied and undone, the class returns.
#[test]
fn a_shear_undoes_itself() {
    let mut walk = Walk(11);
    for _ in 0..DRAWS {
        let y = Register::i64().read_i64(walk.next() as i64).unwrap();
        let d = Register::i64().read_i64(walk.next() as i64).unwrap().scaled(-((walk.next() % 9) as i32)).unwrap();
        let mut s = AddShear { y: y.clone(), d };
        s.apply().unwrap();
        s.undo().unwrap();
        assert!(s.y.same(&y));
    }
}

/// The owner's cost beside the native words it replaces, at the same widths (the build step's receipt;
/// run with `--ignored --nocapture`).
#[test]
#[ignore]
fn the_owners_cost_beside_native_words() {
    use std::hint::black_box;
    use std::time::Instant;
    let mut walk = Walk(12);
    const N: usize = 1 << 20;
    let words: Vec<u64> = (0..N).map(|_| walk.next() >> 2).collect();
    let values: Vec<Value> = words.iter().map(|&x| Register::i64().read_i64(x as i64).unwrap()).collect();

    let t = Instant::now();
    let mut native = 0i128;
    for &x in &words {
        native = black_box(native + i128::from(black_box(x)));
    }
    let native_ps = t.elapsed().as_nanos() * 1000 / N as u128;

    let t = Instant::now();
    let mut acc = Accumulation::at(Grain::new(0));
    for v in &values {
        acc.add(black_box(v)).unwrap();
    }
    let acc_ps = t.elapsed().as_nanos() * 1000 / N as u128;
    assert_eq!(acc.value().unwrap().digits.big(), BigInt::from(native));

    // The same adds on a resident set (4,096 values read 256 times, inside the cache), so the comparison reads the
    // operation's own cost apart from streaming a value's header beside its digits.
    const R: usize = 1 << 12;
    let t = Instant::now();
    let mut resident = 0i128;
    for _ in 0..256 {
        for &x in &words[..R] {
            resident = black_box(resident + i128::from(black_box(x)));
        }
    }
    let native_resident_ps = t.elapsed().as_nanos() * 1000 / (256 * R as u128);
    let t = Instant::now();
    let mut acc_resident = Accumulation::at(Grain::new(0));
    for _ in 0..256 {
        for v in &values[..R] {
            acc_resident.add(black_box(v)).unwrap();
        }
    }
    let acc_resident_ps = t.elapsed().as_nanos() * 1000 / (256 * R as u128);
    assert_eq!(acc_resident.value().unwrap().digits.big(), BigInt::from(resident));

    let t = Instant::now();
    let mut chain = Value::zero(Grain::new(0));
    for v in values.iter().take(1 << 12) {
        chain = black_box(chain.add(v).unwrap());
    }
    let chain_ps = t.elapsed().as_nanos() * 1000 / (1u128 << 12);

    let t = Instant::now();
    let mut prod = 0u64;
    for pair in words.chunks(2) {
        prod ^= black_box(pair[0].wrapping_mul(pair[1]));
    }
    let mul_native_ps = t.elapsed().as_nanos() * 1000 / (N as u128 / 2);
    let t = Instant::now();
    let mut bits = 0u64;
    for pair in values.chunks(2) {
        let (b, _) = Register::i64().write_i64(&pair[0].mul(&pair[1]).unwrap()).unwrap();
        bits ^= black_box(b as u64);
    }
    let mul_ps = t.elapsed().as_nanos() * 1000 / (N as u128 / 2);
    assert_eq!(bits, prod);
    eprintln!(
        "COST (ps per operation) add streamed: native i128 {native_ps}, accumulation {acc_ps}; add resident: native i128 \
         {native_resident_ps}, accumulation {acc_resident_ps}; chained Value::add {chain_ps}; mul+write: native u64 {mul_native_ps}, \
         owner {mul_ps}; a value {} bytes beside a word's 8", std::mem::size_of::<Value>()
    );
}

/// The typed realization's classes are the general form's: each operation, written back, is `Value`'s and the native
/// word's, at the section N3's cross rules give; each release recomposes `value · 2^K + remainder` with both inside the
/// widths its rule needs (`inside` is checked in debug on every result).
#[test]
fn the_typed_realization_is_the_general_forms_class() {
    let mut walk = Walk(14);
    for _ in 0..DRAWS {
        let (a, b) = ((walk.next() as i64) >> 33, (walk.next() as i64) >> 33);
        let (ta, tb) = (Signed64::<31, 0>::read_i64(a).unwrap(), Signed64::<31, 0>::read_i64(b).unwrap());
        let (va, vb) = (ta.value().unwrap(), tb.value().unwrap());
        let s: Signed64<32, 0> = ta.add(tb);
        assert_eq!(s.write_i64().unwrap(), a + b);
        assert!(s.value().unwrap().same(&va.add(&vb).unwrap()));
        let d: Signed64<32, 0> = ta.sub(tb);
        assert_eq!(d.write_i64().unwrap(), a - b);
        let p: Signed64<62, -3> = Signed64::<31, -1>::read_i64(a).unwrap().mul(Signed64::<31, -2>::read_i64(b).unwrap());
        assert_eq!(p.write_i64().unwrap(), a * b);
        // The cross rules: u32 × u32 into a u64; low + signed and low − low; a product with a signed operand.
        let (x, y) = (walk.next() as u32, walk.next() as u32);
        let (lx, ly) = (Low64::<32, 0>::read_u64(u64::from(x)).unwrap(), Low64::<32, 0>::read_u64(u64::from(y)).unwrap());
        let lp: Low64<64, 0> = lx.mul(ly);
        assert_eq!(lp.write_u64().unwrap(), u64::from(x) * u64::from(y));
        let ls: Low64<33, 0> = lx.add(ly);
        assert_eq!(ls.write_u64().unwrap(), u64::from(x) + u64::from(y));
        let ld: Signed64<33, 0> = lx.sub(ly);
        assert_eq!(ld.write_i64().unwrap(), i64::from(x) - i64::from(y));
        let sm = Signed64::<31, 0>::read_i64(a).unwrap();
        let mixed: Signed64<34, 0> = lx.add(sm);
        assert_eq!(mixed.write_i64().unwrap(), i64::from(x) + a);
        let mp: Signed64<63, 0> = lx.mul(sm);
        assert_eq!(mp.write_i64().unwrap(), i64::from(x) * a);
        assert!(mp.value().unwrap().same(&lx.value().unwrap().mul(&sm.value().unwrap()).unwrap()));
        let neg: Signed64<33, 0> = lx.neg();
        assert_eq!(neg.write_i64().unwrap(), -i64::from(x));
        let up: Signed64<33, 0> = lx.signed();
        assert_eq!(up.write_i64().unwrap(), i64::from(x));
        // Each release rule recomposes and agrees with the general form's.
        let (q, r): (Signed64<25, 7>, Signed64<7, 0>) = ta.release_nearest_up();
        assert_eq!(q.write_i64().unwrap() * 128 + r.write_i64().unwrap(), a);
        assert!(q.value().unwrap().same(&release(&va, 7, Rounding::Nearest(Tie::Up)).unwrap().value));
        let (q, r): (Signed64<24, 7>, Low64<7, 0>) = ta.release_floor();
        assert_eq!(q.write_i64().unwrap() * 128 + r.write_i64().unwrap(), a);
        assert!(q.value().unwrap().same(&release(&va, 7, Rounding::Floor).unwrap().value));
        for (rule, general) in [(Rule::Ceiling, Rounding::Ceiling), (Rule::NearestAway, Rounding::Nearest(Tie::Away)), (Rule::NearestEven, Rounding::Nearest(Tie::Even))] {
            let (q, r): (Signed64<25, 7>, Signed64<8, 0>) = ta.release_by::<7, 25, 7, 8>(rule).unwrap();
            assert_eq!(q.write_i64().unwrap() * 128 + r.write_i64().unwrap(), a, "{rule:?}");
            assert!(q.value().unwrap().same(&release(&va, 7, general).unwrap().value), "{rule:?}");
        }
        // At all of the word's places the nearest release does not leave the word.
        let full = walk.next() as i64;
        let (q, r): (Signed64<45, 20>, Signed64<20, 0>) = Signed64::<64, 0>::read_i64(full).unwrap().release_nearest_up();
        assert_eq!(i128::from(q.write_i64().unwrap()) * (1 << 20) + i128::from(r.write_i64().unwrap()), i128::from(full));
        assert!(Signed64::<31, 0>::of_value(&va).unwrap() == ta);
        let w = walk.wide() as i128 >> 2;
        let big = Signed128::<126, 0>::read_i128(w).unwrap();
        let s: Signed128<127, 0> = big.add(Signed128::<126, 0>::read_i128(-w).unwrap());
        assert_eq!(s.write_i128().unwrap(), 0);
        let (x, y) = (walk.next(), walk.next());
        let wide: Low128<128, 0> = Low128::<64, 0>::read_u128(u128::from(x)).unwrap().mul(Low128::<64, 0>::read_u128(u128::from(y)).unwrap());
        assert_eq!(wide.write_u128().unwrap(), u128::from(x) * u128::from(y));
        let (ps, pw) = Path64::<64>::read_u64(x).unwrap().add(Path64::<64>::read_u64(y).unwrap());
        assert_eq!((ps.write_u64(), pw == 1), x.overflowing_add(y));
        let (pm, hw) = Path64::<64>::read_u64(x).unwrap().mul(Path64::<64>::read_u64(y).unwrap());
        assert_eq!((pm.write_u64(), hw), (x.wrapping_mul(y), ((u128::from(x) * u128::from(y)) >> 64) as u64));
        let (x12, y12) = (x & 0xfff, y & 0xfff);
        let (s12, w12) = Path64::<12>::read_u64(x12).unwrap().add(Path64::<12>::read_u64(y12).unwrap());
        assert_eq!(s12.write_u64() + (w12 << 12), x12 + y12);
    }
    assert!(Signed64::<8, 0>::read_i64(128).is_err());
    assert!(Signed64::<8, 0>::read_i64(-128).is_ok());
    assert!(Low64::<8, 0>::read_u64(256).is_err());
    assert!(Path64::<12>::read_u64(1 << 12).is_err());
    assert!(Signed64::<31, 0>::read_i64(5).unwrap().release_by::<1, 31, 1, 2>(Rule::Floor).is_err());
    let terms: Vec<Signed64<40, 0>> = (0..(1 << 10)).map(|i| Signed64::read_i64(((i as i64) << 28) - (1 << 38)).unwrap()).collect();
    let total: Signed64<50, 0> = Signed64::sum(&terms).unwrap();
    assert_eq!(total.write_i64().unwrap(), terms.iter().map(|t| t.write_i64().unwrap()).sum::<i64>());
    assert!(Signed64::<40, 0>::sum::<49>(&terms).is_err());
    let wide_terms = vec![Signed128::<40, 0>::read_i128(-3).unwrap(); 5];
    let wide_total: Signed128<120, 0> = Signed128::sum(&wide_terms).unwrap();
    assert_eq!(wide_total.write_i128().unwrap(), -15);
}

/// The typed realization's cost beside the native words (run with `--ignored --nocapture`).
#[test]
#[ignore]
fn the_typed_realizations_cost_beside_native_words() {
    use std::hint::black_box;
    use std::time::Instant;
    let mut walk = Walk(15);
    const N: usize = 1 << 20;
    let words: Vec<i64> = (0..N).map(|_| (walk.next() as i64) >> 24).collect();
    let typed: Vec<Signed64<40, 0>> = words.iter().map(|&x| Signed64::read_i64(x).unwrap()).collect();
    let rounds = 64u128;
    let t = Instant::now();
    let mut native = 0i64;
    for _ in 0..rounds {
        native = native.wrapping_add(black_box(&words).iter().sum::<i64>());
    }
    let native_ps = t.elapsed().as_nanos() * 1000 / (rounds * N as u128);
    let t = Instant::now();
    let mut owner = 0i64;
    for _ in 0..rounds {
        let s: Signed64<60, 0> = Signed64::sum(black_box(&typed)).unwrap();
        owner = owner.wrapping_add(s.write_i64().unwrap());
    }
    let owner_ps = t.elapsed().as_nanos() * 1000 / (rounds * N as u128);
    assert_eq!(native, owner);
    let t = Instant::now();
    let mut pairs = 0i64;
    for w in words.chunks_exact(2) {
        pairs ^= black_box(black_box(w[0]) + black_box(w[1]));
    }
    let native_add_ps = t.elapsed().as_nanos() * 1000 / (N as u128 / 2);
    let t = Instant::now();
    let mut tpairs = 0i64;
    for w in typed.chunks_exact(2) {
        let s: Signed64<41, 0> = black_box(w[0]).add(black_box(w[1]));
        tpairs ^= black_box(s.write_i64().unwrap());
    }
    let owner_add_ps = t.elapsed().as_nanos() * 1000 / (N as u128 / 2);
    assert_eq!(pairs, tpairs);
    eprintln!("COST_TYPED (ps per term) accumulation: native {native_ps}, owner {owner_ps}; add: native {native_add_ps}, owner {owner_add_ps}; a typed value {} bytes", std::mem::size_of::<Signed64<40, 0>>());
}
