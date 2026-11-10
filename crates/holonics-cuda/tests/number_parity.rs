//! [measurement] **The number header on the card returns the host owner's classes** (step 2 of the number record's build
//! order; `kernels/number.cuh`, `holonics_cuda::number`, the host owner `holonics::number`): on random words at 1, 2, 4 and 8
//! limbs, each case's sum with its carry, difference with its borrow, the signed sum's winding, the unsigned and the signed
//! products, the release to the nearest (ties up) with its remainder, and the bottom inverse with its steps, against `BigInt`
//! and, inside 128 places, against `holonics::number`'s own release and inverse; the cut add against lane-by-lane adds; the
//! warp's add of 1,024-place words against `BigInt`. Run alone under the card's lock:
//! `flock -w 900 .local/gpu.lock cargo test --release -p holonics-cuda --test number_parity -- --include-ignored --test-threads=1`.

use holonics::number::{invert, release, End, Register, Rounding, Tie};
use holonics_cuda::hnn::Card;
use holonics_cuda::number::{cut_add, parity, warp_add};
use num_bigint::{BigInt, BigUint, Sign};
use num_traits::One;

fn mixer(seed: u64) -> impl FnMut() -> u64 {
    let mut s = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0xD1B5_4A32_D192_ED03;
    move || {
        s = s.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = s;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

fn unsigned(limbs: &[u32]) -> BigUint {
    BigUint::from_slice(limbs)
}

/// The signed reading of `L` limbs in the two's-complement section.
fn signed(limbs: &[u32]) -> BigInt {
    let u = BigInt::from(unsigned(limbs));
    if limbs.last().is_some_and(|&top| top >> 31 == 1) { u - (BigInt::one() << (32 * limbs.len())) } else { u }
}

/// A class's residue modulo `2^(32·n)` as `n` limbs.
fn limbs_of(x: &BigInt, n: usize) -> Vec<u32> {
    let m = BigInt::one() << (32 * n);
    let r = ((x % &m) + &m) % &m;
    let (_, mut digits) = r.to_u32_digits();
    digits.resize(n, 0);
    digits
}

fn draw(next: &mut impl FnMut() -> u64, limbs: usize) -> Vec<u32> {
    // A drawn top place, so narrow and wide classes, and both signs, occur.
    let mut v: Vec<u32> = (0..limbs).map(|_| next() as u32).collect();
    let keep = (next() % (32 * limbs as u64 + 1)) as usize;
    for (i, limb) in v.iter_mut().enumerate() {
        let lo = 32 * i;
        if keep <= lo {
            *limb = if next() % 2 == 0 { 0 } else { u32::MAX };
        } else if keep < lo + 32 {
            let mask = (1u32 << (keep - lo)) - 1;
            *limb = (*limb & mask) | if next() % 2 == 0 { 0 } else { !mask };
        }
    }
    v
}

#[test]
#[ignore = "needs the card"]
fn the_number_header_on_the_card_is_the_host_owners() {
    let card = Card::open(0).expect("a card");
    let mut next = mixer(0x6E75_6D62);
    for limbs in [1usize, 2, 4, 8] {
        let n = 32 * limbs;
        let cases: Vec<(Vec<u32>, Vec<u32>, i32)> =
            (0..4096).map(|_| (draw(&mut next, limbs), draw(&mut next, limbs), (next() % (n as u64 - 1)) as i32 + 1)).collect();
        let out = parity(&card, limbs, &cases).expect("the parity kernels");
        let m = BigInt::one() << n;
        for ((a, b, k), got) in cases.iter().zip(&out) {
            let (ua, ub) = (BigInt::from(unsigned(a)), BigInt::from(unsigned(b)));
            let (sa, sb) = (signed(a), signed(b));
            let sum = &ua + &ub;
            assert_eq!((limbs_of(&sum, limbs), got.carry), (got.sum.clone(), u32::from(sum >= m)), "sum at {limbs} limbs");
            assert_eq!((limbs_of(&(&ua - &ub), limbs), got.borrow), (got.difference.clone(), u32::from(ua < ub)), "difference");
            let s = &sa + &sb;
            let winding = (&s + (BigInt::one() << (n - 1))) >> n;
            assert_eq!(BigInt::from(got.winding), winding, "signed winding");
            assert_eq!(got.product, limbs_of(&(&ua * &ub), 2 * limbs), "unsigned product");
            assert_eq!(got.signed_product, limbs_of(&(&sa * &sb), 2 * limbs), "signed product");
            let unit = BigInt::one() << *k as usize;
            let q = (&sa + (BigInt::one() << (*k as usize - 1))) >> *k as usize;
            let r = &sa - &q * &unit;
            assert_eq!((got.quotient.clone(), got.remainder.clone()), (limbs_of(&q, limbs), limbs_of(&r, limbs)), "release of {k}");
            assert_eq!(signed(&got.remainder), r, "the remainder in its section");
            let odd = &ua | BigInt::one();
            let x = BigInt::from(unsigned(&got.inverse));
            assert!(((&odd * &x) % &m).is_one(), "bottom inverse at {limbs} limbs");
            if n <= 128 {
                // The host owner's own release and inverse at the same places.
                let ra = Register::i128().read_i128(i128::try_from(sa.clone()).unwrap()).unwrap();
                let released = release(&ra, *k as u32, Rounding::Nearest(Tie::Up)).unwrap();
                assert!(released.value.same(&Register::i128().read_i128(i128::try_from(q.clone()).unwrap()).unwrap().scaled(*k).unwrap()));
                let oa = Register::u128().read_u128(u128::try_from(odd.clone()).unwrap()).unwrap();
                let inv = invert(&oa, End::Bottom(n as u32)).unwrap();
                assert_eq!(inv.steps, got.steps, "the bottom end's steps at {n} places");
            }
        }
        eprintln!("NUMBER_PARITY limbs={limbs} cases={} identical", cases.len());
    }
    // The cut add: random field patterns in one 32-place word against each field's own wrapping add.
    let mut cut = Vec::new();
    let mut fields = Vec::new();
    for _ in 0..4096 {
        let mut widths = Vec::new();
        let mut left = 32u32;
        while left > 0 {
            let w = ((next() % 12) as u32 + 1).min(left);
            widths.push(w);
            left -= w;
        }
        let mut h = 0u32;
        let mut at = 0u32;
        for &w in &widths {
            h |= 1 << (at + w - 1);
            at += w;
        }
        cut.push((next() as u32, next() as u32, h));
        fields.push(widths);
    }
    let got = cut_add(&card, &cut).expect("the cut add");
    for (((x, y, _), widths), &g) in cut.iter().zip(&fields).zip(&got) {
        let mut want = 0u32;
        let mut at = 0u32;
        for &w in widths {
            let mask = if w == 32 { u32::MAX } else { (1u32 << w) - 1 };
            want |= (((x >> at) & mask).wrapping_add((y >> at) & mask) & mask) << at;
            at += w;
        }
        assert_eq!(g, want);
    }
    eprintln!("NUMBER_PARITY cut cases={} identical", cut.len());
    // The warp's add of 1,024-place words, with long carry chains drawn in.
    let wide: Vec<([u32; 32], [u32; 32])> = (0..1024)
        .map(|i| {
            let mut a = [0u32; 32];
            let mut b = [0u32; 32];
            for j in 0..32 {
                a[j] = next() as u32;
                b[j] = if i % 3 == 0 { !a[j] } else { next() as u32 };
            }
            if i % 3 == 0 {
                b[0] = b[0].wrapping_add(1);
            }
            (a, b)
        })
        .collect();
    let got = warp_add(&card, &wide).expect("the warp's add");
    let m = BigUint::one() << 1024;
    for ((a, b), (sum, winding)) in wide.iter().zip(&got) {
        let s = unsigned(a) + unsigned(b);
        let want = BigInt::from_biguint(Sign::Plus, &s % &m);
        assert_eq!(limbs_of(&want, 32), sum.to_vec());
        assert_eq!(*winding, u32::from(s >= m));
    }
    eprintln!("NUMBER_PARITY warp cases={} identical", wide.len());
}
