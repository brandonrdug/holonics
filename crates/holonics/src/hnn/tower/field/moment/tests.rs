use super::*;
use crate::hnn::tower::field::{ring_phasor, Field, FieldDeclaration};
use crate::hnn::tower::{half_turn, TowerError};
use num_bigint::BigInt;

type G = (i128, i128);
/// A Gaussian integer past `i128` (the span face multiplies two grains of `2^(−60)` and `2^(−106)`).
type B = (BigInt, BigInt);

fn bw(g: G) -> B {
    (BigInt::from(g.0), BigInt::from(g.1))
}

fn bmul(a: &B, b: &B) -> B {
    (&a.0 * &b.0 - &a.1 * &b.1, &a.0 * &b.1 + &a.1 * &b.0)
}

fn babs(x: &BigInt) -> BigInt {
    if x < &BigInt::from(0) { -x } else { x.clone() }
}

/// An exterior integer mixer's words from a seed (the fixtures' draws).
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

/// `sites` complex encodings with components uniform on `[−bound, bound)`.
fn strand(next: &mut impl FnMut() -> u64, sites: usize, bound: i64) -> Vec<(i64, i64)> {
    let mut draw = || (next() % (2 * bound as u64)) as i64 - bound;
    (0..sites).map(|_| (draw(), draw())).collect()
}

/// A turned ring slot as the founded field holds it, with the full ring `ζ^r`, `r < n`, from the
/// field's own `ring_phasor` (the reference never reads the truncated resident ring).
struct Slot {
    n: usize,
    ring: Vec<(i64, i64)>,
    decay: Vec<i64>,
    full: Vec<G>,
}

impl Slot {
    /// `ζ^r` for any integer `r`.
    fn phase(&self, r: i64) -> G {
        self.full[r.rem_euclid(self.n as i64) as usize]
    }
}

fn slots(reach: usize, modes: usize) -> Vec<Slot> {
    let declaration = FieldDeclaration { alphabet: 5, width: 8, heads: 2, modes, still: 1, contacts: 4, ticks: 2, frames: 2, reach, lanes: 1, depth: 0 };
    let mut next = mixer(7);
    let keys: Vec<u8> = (0..1usize << 14).flat_map(|_| next().to_be_bytes()).collect();
    let field = Field::found(declaration, &keys).unwrap();
    let pi = half_turn(MOVE_BITS + 16);
    field
        .rings()
        .iter()
        .zip(field.decays())
        .map(|((n, ring), decay)| {
            let full = (0..*n).map(|r| ring_phasor(r, *n, pi)).map(|(a, b)| (a as i128, b as i128)).collect();
            Slot { n: *n, ring: ring.clone(), decay: decay.clone(), full }
        })
        .collect()
}

fn gmul(a: G, b: G) -> G {
    (a.0 * b.0 - a.1 * b.1, a.0 * b.1 + a.1 * b.0)
}

fn gconj(a: G) -> G {
    (a.0, -a.1)
}

fn gadd(a: G, b: G) -> G {
    (a.0 + b.0, a.1 + b.1)
}

fn gwide((a, b): (i64, i64)) -> G {
    (a as i128, b as i128)
}

/// The coefficient `W_(t,k)` on `2^(−90)` from its definition, by the distance alone: near
/// `ζ^(k−t) D(|t−k|) 2^30`; far `D(2^ℓ) conj(ζ^t) ζ^k` with `ℓ = ⌊log₂ |t−k|⌋`.
fn coefficient(slot: &Slot, t: usize, k: usize) -> G {
    let d = t.abs_diff(k);
    if d < NEAR {
        let z = slot.phase(k as i64 - t as i64);
        let s = (slot.decay[d] as i128) << MOVE_BITS;
        (z.0 * s, z.1 * s)
    } else {
        let c = gmul(gconj(slot.phase(t as i64)), slot.phase(k as i64));
        let s = slot.decay[1usize << d.ilog2()] as i128;
        (c.0 * s, c.1 * s)
    }
}

/// `S_t = Σ_k W_(t,k) E±_k` over the pairs, unreleased on `2^(−106)`: `O(S²)`.
fn direct(slot: &Slot, before: &[(i64, i64)], after: &[(i64, i64)]) -> Vec<G> {
    let sites = before.len();
    (0..sites)
        .map(|t| {
            let mut s = (0i128, 0i128);
            for k in 0..sites {
                let w = coefficient(slot, t, k);
                if k <= t {
                    s = gadd(s, gmul(w, gwide(before[k])));
                }
                if k >= t {
                    s = gadd(s, gmul(w, gwide(after[k])));
                }
            }
            s
        })
        .collect()
}

/// The released return from its definition, unreleased on `2^(−84)`: `O(S²)`. The turned covector is
/// released once a term, `r_t = release(ζ^t δs_t, 30)`; a pair within `NEAR` meets as
/// `conj(ζ^(k−t)) D(|t−k|) δs_t`, a far pair as `conj(ζ^k) (D(2^ℓ) r_t)`, `ℓ = ⌊log₂ |t − k|⌋`. Plus sums
/// `t ≥ k`, minus `t ≤ k`; the octaves are by the distance alone.
fn direct_return(slot: &Slot, ds: &[(i64, i64)]) -> (Vec<G>, Vec<G>) {
    let sites = ds.len();
    let turned: Vec<G> = (0..sites)
        .map(|t| {
            let p = gmul(slot.phase(t as i64), gwide(ds[t]));
            (release(p.0, MOVE_BITS), release(p.1, MOVE_BITS))
        })
        .collect();
    let term = |k: usize, t: usize| -> G {
        let d = t.abs_diff(k);
        if d < NEAR {
            let c = gmul(gconj(slot.phase(k as i64 - t as i64)), gwide(ds[t]));
            let s = slot.decay[d] as i128;
            (c.0 * s, c.1 * s)
        } else {
            let s = slot.decay[1usize << d.ilog2()] as i128;
            gmul(gconj(slot.phase(k as i64)), (turned[t].0 * s, turned[t].1 * s))
        }
    };
    let sum = |k: usize, ts: &mut dyn Iterator<Item = usize>| ts.fold((0i128, 0i128), |a, t| gadd(a, term(k, t)));
    let plus = (0..sites).map(|k| sum(k, &mut (k..sites))).collect();
    let minus = (0..sites).map(|k| sum(k, &mut (0..=k))).collect();
    (plus, minus)
}

fn released(v: &[G], bits: u32) -> Vec<G> {
    v.iter().map(|&(a, b)| (release(a, bits), release(b, bits))).collect()
}

const LENGTHS: [usize; 14] = [1, 2, 5, 6, 7, 8, 9, 15, 16, 17, 31, 64, 100, 257];

fn all_slots() -> Vec<Slot> {
    let mut out = slots(16, 4);
    out.extend(slots(300, 6));
    out
}

/// The ring is closed under conjugation bit for bit, `ring[n − m] = conj(ring[m])`, which is what
/// lets a negative near difference read the resident ring where `n` passes the reach.
#[test]
fn the_ring_is_closed_under_conjugation() {
    let pi = half_turn(MOVE_BITS + 16);
    for n in [2usize, 3, 4, 5, 7, 16, 27, 32, 243, 512, 729] {
        for m in 1..n {
            let (a, b) = ring_phasor(m, n, pi);
            let (c, d) = ring_phasor(n - m, n, pi);
            assert_eq!((c, d), (a, -b), "n {n} m {m}");
        }
    }
}

/// The near phase reads `ring[(k − t) rem n]` where resident and the conjugate of `ring[t − k]`
/// where the ring holds fewer than `n` phasors, equal to the full ring either way.
#[test]
fn near_phases_equal_the_full_ring_wherever_the_ring_is_truncated() {
    for slot in all_slots() {
        let law = Law::new(12, &slot.ring, slot.n, &slot.decay, None).unwrap();
        for r in -(NEAR as i64 - 1)..=(NEAR as i64 - 1) {
            assert_eq!(law.zeta(r).unwrap(), slot.phase(r), "n {} r {r}", slot.n);
        }
    }
    // The slot of period 729 holds 300 phasors; its negative differences land past them.
    let slot = slots(300, 6).into_iter().find(|s| s.n == 729).unwrap();
    assert_eq!(slot.ring.len(), 300);
}

/// The crowds are dual: `k` is in the left octave `ℓ` of `t` exactly when `t` is in the right octave
/// `ℓ` of `k`, and every pair at least `NEAR` apart is in exactly one octave, at
/// `ℓ = ⌊log₂ |t − k|⌋`. This is what makes the adjoint's ranges the same `crowd_ranges`.
#[test]
fn the_octaves_are_dual_and_partition_the_far_pairs() {
    for sites in (1..=70).chain([100, 129, 257]) {
        let ranges: Vec<_> = (0..sites).map(|t| crowd_ranges(t, sites)).collect();
        for t in 0..sites {
            for k in 0..sites {
                let d = t.abs_diff(k);
                let left: Vec<u32> = ranges[t].iter().filter(|&&(lo, hi, _)| hi < t && (lo..=hi).contains(&k)).map(|r| r.2).collect();
                let right: Vec<u32> = ranges[k].iter().filter(|&&(lo, hi, _)| lo > k && (lo..=hi).contains(&t)).map(|r| r.2).collect();
                if d < NEAR {
                    assert!(left.is_empty() && right.is_empty() && ranges[t].iter().all(|&(lo, hi, _)| !(lo..=hi).contains(&k)), "S {sites} ({t},{k})");
                } else if k < t {
                    // `k` before `t`: the left octave of `t`, the right octave of `k`.
                    assert_eq!((left, right), (vec![d.ilog2()], vec![d.ilog2()]), "S {sites} ({t},{k})");
                } else {
                    assert!(left.is_empty() && right.is_empty());
                    let mirrored: Vec<u32> = ranges[t].iter().filter(|&&(lo, _, _)| lo > t).filter(|&&(lo, hi, _)| (lo..=hi).contains(&k)).map(|r| r.2).collect();
                    assert_eq!(mirrored, vec![d.ilog2()], "S {sites} ({t},{k})");
                }
            }
        }
    }
}

/// The moment equals the direct `O(S²)` sum of the coefficients, bit for bit, on every ring slot
/// of two founded fields, unreleased and released.
#[test]
fn the_moments_equal_the_direct_sum_bit_for_bit() {
    let mut next = mixer(11);
    let mut checked = 0usize;
    for slot in all_slots() {
        let reach = slot.decay.len();
        for &sites in LENGTHS.iter().filter(|&&s| s <= reach) {
            let (before, after) = (strand(&mut next, sites, 1 << 17), strand(&mut next, sites, 1 << 17));
            let exact = moment_exact(&before, &after, &slot.ring, slot.n, &slot.decay, None).unwrap();
            let want = direct(&slot, &before, &after);
            assert_eq!(exact, want, "n {} S {sites}", slot.n);
            let got = moments(&before, &after, &slot.ring, slot.n, &slot.decay, None).unwrap();
            let want_released: Vec<(i64, i64)> = released(&want, COEFFICIENT_BITS).into_iter().map(|(a, b)| (a as i64, b as i64)).collect();
            assert_eq!(got, want_released, "n {} S {sites}", slot.n);
            checked += sites;
        }
    }
    assert!(checked > 1000);
}

/// A slot of one constant phase and no decay (`n = 1`, `D = 1`) carries every source whole: the
/// moment is the plain sum of the forward strand up to `t` and the backward strand from `t`, so every
/// source is met exactly once, near or in its octave, and the sum is exact in the released grain.
#[test]
fn a_stationary_slot_sums_every_source_once() {
    let ring = [(1i64 << MOVE_BITS, 0i64)];
    let decay = vec![1i64 << MOVE_BITS; 300];
    let mut next = mixer(13);
    for sites in [1usize, 3, 6, 7, 20, 64, 129, 300] {
        let (before, after) = (strand(&mut next, sites, 1 << 17), strand(&mut next, sites, 1 << 17));
        let got = moments(&before, &after, &ring, 1, &decay, None).unwrap();
        for t in 0..sites {
            let mut want = (0i64, 0i64);
            for k in 0..sites {
                if k <= t {
                    want = (want.0 + before[k].0, want.1 + before[k].1);
                }
                if k >= t {
                    want = (want.0 + after[k].0, want.1 + after[k].1);
                }
            }
            assert_eq!(got[t], want, "S {sites} t {t}");
        }
    }
}

/// `Σ_t Re(conj(δs_t) S_t)` and `Σ_k Re(conj(Δ⁺_k) E⁺_k) + Re(conj(Δ⁻_k) E⁻_k)`, in integers.
fn pairings(before: &[(i64, i64)], after: &[(i64, i64)], ds: &[(i64, i64)], moment: &[G], plus: &[G], minus: &[G]) -> (BigInt, BigInt) {
    let b = |x: i128| BigInt::from(x);
    let re = |a: G, c: G| b(a.0) * b(c.0) + b(a.1) * b(c.1);
    let left = ds.iter().zip(moment).fold(BigInt::from(0), |acc, (&d, &s)| acc + re(gwide(d), s));
    let right = (0..before.len()).fold(BigInt::from(0), |acc, k| acc + re(plus[k], gwide(before[k])) + re(minus[k], gwide(after[k])));
    (left, right)
}

/// The released return equals the direct `O(S²)` sum of the same released law, bit for bit,
/// unreleased (`2^(−84)`) and released (60 bits to `2^(−24)`), on every slot, with covectors to the
/// size the return's certificate admits (components below `2^24` and `2^40`).
#[test]
fn the_return_equals_its_released_law_bit_for_bit() {
    let mut next = mixer(17);
    let mut checked = 0usize;
    for slot in all_slots() {
        let reach = slot.decay.len();
        for &sites in LENGTHS.iter().filter(|&&s| s <= reach) {
            for d_bound in [8i64, 1 << 24, 1 << 40] {
                let ds = strand(&mut next, sites, d_bound);
                let (plus, minus) = moment_return_exact(&ds, &slot.ring, slot.n, &slot.decay, None).unwrap();
                let (want_plus, want_minus) = direct_return(&slot, &ds);
                assert_eq!((&plus, &minus), (&want_plus, &want_minus), "n {} S {sites} bound {d_bound}", slot.n);
                let (rp, rm) = moments_return(&ds, &slot.ring, slot.n, &slot.decay, None).unwrap();
                assert_eq!((rp, rm), (released(&want_plus, RETURN_RELEASE_BITS), released(&want_minus, RETURN_RELEASE_BITS)), "n {} S {sites}", slot.n);
                checked += sites;
            }
        }
    }
    assert!(checked > 3000);
}

/// The bound on the pairing's rounding discrepancy (module doc), from the definitions:
/// `2^30 Σ_k [ l1(ζ^k) (Σ_(far t>k) D(2^ℓ)) ‖E⁺_k‖∞ + l1(ζ^k) (Σ_(far t<k) D(2^ℓ)) ‖E⁻_k‖∞ ]`.
fn pairing_bound(slot: &Slot, before: &[(i64, i64)], after: &[(i64, i64)]) -> BigInt {
    let sites = before.len();
    let sup = |p: (i64, i64)| p.0.unsigned_abs().max(p.1.unsigned_abs()) as i128;
    let mut total = BigInt::from(0);
    for k in 0..sites {
        let z = slot.phase(k as i64);
        let l1 = z.0.abs() + z.1.abs();
        let (mut above, mut below) = (0i128, 0i128);
        for t in 0..sites {
            let d = t.abs_diff(k);
            if d >= NEAR {
                let decay = slot.decay[1usize << d.ilog2()] as i128;
                if t > k {
                    above += decay;
                } else {
                    below += decay;
                }
            }
        }
        total += BigInt::from(l1) * (BigInt::from(above) * sup(before[k]) + BigInt::from(below) * sup(after[k]));
    }
    total << MOVE_BITS as usize
}

/// The released return pairs with the moments to the rounding of its releases, and the discrepancy is
/// real: `| ⟨δs, S(E)⟩ − 2^30 ⟨Δ(δs), E⟩ |` (grain `2^(−130)`, integers) is within `pairing_bound`, zero
/// where no far pair rounds (`S ≤ NEAR`) and nonzero somewhere else.
#[test]
fn the_return_pairs_with_the_moments_within_the_release_rounding() {
    let mut next = mixer(18);
    let mut seen = 0usize;
    for slot in all_slots() {
        let reach = slot.decay.len();
        for &sites in LENGTHS.iter().filter(|&&s| s <= reach) {
            for (e_bound, d_bound) in [(8i64, 8i64), (1 << 17, 1 << 24), (1 << 17, 1 << 40)] {
                let (before, after) = (strand(&mut next, sites, e_bound), strand(&mut next, sites, e_bound));
                let ds = strand(&mut next, sites, d_bound);
                let moment = moment_exact(&before, &after, &slot.ring, slot.n, &slot.decay, None).unwrap();
                let (plus, minus) = moment_return_exact(&ds, &slot.ring, slot.n, &slot.decay, None).unwrap();
                let (left, right) = pairings(&before, &after, &ds, &moment, &plus, &minus);
                let diff = &left - (right << MOVE_BITS as usize);
                let bound = pairing_bound(&slot, &before, &after);
                assert!(babs(&diff) <= bound, "n {} S {sites} bounds {e_bound} {d_bound}: {diff} against {bound}", slot.n);
                if sites <= NEAR {
                    assert_eq!(diff, BigInt::from(0), "no far pair, no rounding: n {} S {sites}", slot.n);
                    assert_eq!(bound, BigInt::from(0));
                } else if diff != BigInt::from(0) {
                    seen += 1;
                }
                assert!(sites < 2 || left != BigInt::from(0), "a vanishing pairing proves nothing");
            }
        }
    }
    assert!(seen > 20, "the release's rounding was seen {seen} times");
}

/// A stationary slot turns the covector by `2^30` exactly, so its release rounds nothing and the
/// return is the exact transpose scaled: the pairing is an equality of integers at any strand length.
#[test]
fn a_stationary_slot_pairs_exactly() {
    let ring = [(1i64 << MOVE_BITS, 0i64)];
    let decay = vec![1i64 << MOVE_BITS; 300];
    let mut next = mixer(21);
    for sites in [7usize, 64, 129, 300] {
        let (before, after) = (strand(&mut next, sites, 1 << 17), strand(&mut next, sites, 1 << 17));
        let ds = strand(&mut next, sites, 1 << 40);
        let moment = moment_exact(&before, &after, &ring, 1, &decay, None).unwrap();
        let (plus, minus) = moment_return_exact(&ds, &ring, 1, &decay, None).unwrap();
        let (left, right) = pairings(&before, &after, &ds, &moment, &plus, &minus);
        assert_eq!(left, right << MOVE_BITS as usize, "S {sites}");
        assert!(left != BigInt::from(0));
    }
}

/// The crib region's covector: 406 sites, l1 up to `2^28` (16 units on `2^(−24)`), which the exact
/// transpose's certificate refused on the founded ring and the released return admits, bit for bit
/// the direct sum of its law.
#[test]
fn a_crib_regions_covector_is_admitted() {
    let slot = slots(512, 6).into_iter().find(|s| s.n == 729).unwrap();
    let mut next = mixer(25);
    let sites = 406;
    let ds = strand(&mut next, sites, 1 << 27);
    let l1_of = |p: &(i64, i64)| p.0.unsigned_abs() as u128 + p.1.unsigned_abs() as u128;
    let g = ds.iter().map(l1_of).max().unwrap();
    let r = slot.ring.iter().map(l1_of).max().unwrap();
    let d = slot.decay[..sites].iter().map(|d| d.unsigned_abs() as u128).max().unwrap();
    assert!(g > 1 << 27, "a covector of l1 beyond 2^27");
    assert!(!certificate(sites as u128, r, d, g), "the exact transpose's carrier refuses it");
    assert!(return_certificate(sites as u128, r, d, g));
    let (plus, minus) = moments_return(&ds, &slot.ring, slot.n, &slot.decay, None).unwrap();
    let (want_plus, want_minus) = direct_return(&slot, &ds);
    assert_eq!((plus, minus), (released(&want_plus, RETURN_RELEASE_BITS), released(&want_minus, RETURN_RELEASE_BITS)));
}

/// Moments are linear in the encodings (the integer map has no rounding before its one release).
#[test]
fn the_unreleased_moment_is_linear() {
    let slot = slots(300, 6).into_iter().find(|s| s.n == 27).unwrap();
    let mut next = mixer(19);
    let sites = 90;
    let (a0, a1) = (strand(&mut next, sites, 1 << 16), strand(&mut next, sites, 1 << 16));
    let (b0, b1) = (strand(&mut next, sites, 1 << 16), strand(&mut next, sites, 1 << 16));
    let sum = |x: &[(i64, i64)], y: &[(i64, i64)]| x.iter().zip(y).map(|(p, q)| (p.0 + q.0, p.1 + q.1)).collect::<Vec<_>>();
    let (sa, sb) = (moment_exact(&a0, &a1, &slot.ring, slot.n, &slot.decay, None).unwrap(), moment_exact(&b0, &b1, &slot.ring, slot.n, &slot.decay, None).unwrap());
    let both = moment_exact(&sum(&a0, &b0), &sum(&a1, &b1), &slot.ring, slot.n, &slot.decay, None).unwrap();
    let want: Vec<G> = sa.iter().zip(&sb).map(|(&p, &q)| gadd(p, q)).collect();
    assert_eq!(both, want);
}

/// A site meets itself on both strands, each at its own encoding: `ζ⁰ D(0) = 1`.
#[test]
fn a_site_meets_itself_on_both_strands() {
    for slot in all_slots() {
        let mut before = vec![(0i64, 0i64); 4];
        let mut after = vec![(0i64, 0i64); 4];
        before[2] = (1000, -2000);
        after[2] = (30, 70);
        let got = moments(&before, &after, &slot.ring, slot.n, &slot.decay, None).unwrap();
        assert_eq!(got[2], (1030, -1930), "n {}", slot.n);
    }
}

/// Embeds a strand at place `tau` of `length` sites (zeros elsewhere).
fn embedded(x: &[(i64, i64)], tau: usize, length: usize) -> Vec<(i64, i64)> {
    let mut out = vec![(0i64, 0i64); length];
    out[tau..tau + x.len()].copy_from_slice(x);
    out
}

/// The near field reads `k − t` and not the places: a strand whose sources lie within `NEAR` of the
/// site is moved by no shift, bit for bit, on every slot (the span's face stands anywhere).
#[test]
fn the_near_field_does_not_depend_on_where_the_span_stands() {
    let mut next = mixer(23);
    for slot in slots(300, 6) {
        let (a_before, a_after) = (strand(&mut next, NEAR, 1 << 17), strand(&mut next, NEAR, 1 << 17));
        let at_origin = moments(&a_before, &a_after, &slot.ring, slot.n, &slot.decay, None).unwrap();
        for tau in [1usize, 5, 6, 7, 64, 100, 211, 294] {
            let (b_before, b_after) = (embedded(&a_before, tau, 300), embedded(&a_after, tau, 300));
            let shifted = moments(&b_before, &b_after, &slot.ring, slot.n, &slot.decay, None).unwrap();
            assert_eq!(&shifted[tau..tau + NEAR], &at_origin[..], "n {} tau {tau}", slot.n);
        }
    }
}

/// A longer strand moved by `τ` moves its moment only by the ring faces' attained rounding: the far
/// part is `D(2^ℓ) conj(ζ^t) ζ^k` through the absolute places, the same as `D(2^ℓ) ζ^(k−t)` up to
/// the faces' products. The bound is read from the ring: `gap` the largest
/// `‖conj(ζ^a) ζ^b − 2^30 ζ^(b−a)‖∞` over the places, `2 gap` between two placements of one pair.
#[test]
fn a_shifted_strand_moves_its_moment_only_by_the_attained_faces() {
    let mut next = mixer(29);
    let (mut worst, mut worst_exact) = (0i128, 0i128);
    for slot in slots(300, 6) {
        let gap = (0..300usize)
            .flat_map(|a| (0..300usize).map(move |b| (a, b)))
            .map(|(a, b)| {
                let c = gmul(gconj(slot.phase(a as i64)), slot.phase(b as i64));
                let z = slot.phase(b as i64 - a as i64);
                (c.0 - (z.0 << MOVE_BITS)).abs().max((c.1 - (z.1 << MOVE_BITS)).abs())
            })
            .max()
            .unwrap();
        let sites = 60;
        let (a_before, a_after) = (strand(&mut next, sites, 1 << 17), strand(&mut next, sites, 1 << 17));
        let at_origin = direct(&slot, &a_before, &a_after);
        // The bound on a site's change: Σ over its far sources of 2 gap D(2^ℓ) l1(E).
        let l1_of = |p: (i64, i64)| p.0.abs() as i128 + p.1.abs() as i128;
        for tau in [3usize, 64, 100, 240] {
            let (b_before, b_after) = (embedded(&a_before, tau, 300), embedded(&a_after, tau, 300));
            let shifted = moment_exact(&b_before, &b_after, &slot.ring, slot.n, &slot.decay, None).unwrap();
            for t in 0..sites {
                let mut bound = 0i128;
                for k in 0..sites {
                    let d = t.abs_diff(k);
                    if d >= NEAR {
                        let e = if k <= t { l1_of(a_before[k]) } else { 0 } + if k >= t { l1_of(a_after[k]) } else { 0 };
                        bound += 2 * gap * slot.decay[1usize << d.ilog2()] as i128 * e;
                    }
                }
                let moved = ((shifted[tau + t].0 - at_origin[t].0).abs()).max((shifted[tau + t].1 - at_origin[t].1).abs());
                assert!(moved <= bound, "n {} tau {tau} t {t}: moved {moved} bound {bound}", slot.n);
                worst_exact = worst_exact.max(moved);
                // In the released grain: at most the bound's grains, and one for the release.
                let (rs, ra) = (released(&shifted[tau + t..=tau + t], COEFFICIENT_BITS)[0], released(&at_origin[t..=t], COEFFICIENT_BITS)[0]);
                let grains = (rs.0 - ra.0).abs().max((rs.1 - ra.1).abs());
                assert!(grains <= (bound >> COEFFICIENT_BITS) + 1, "n {} tau {tau} t {t}: {grains} grains", slot.n);
                worst = worst.max(grains);
            }
        }
    }
    // The faces' rounding is real (the unreleased moment does move) and lies below the release's grain.
    assert!(worst_exact > 0, "the bound was never tested");
    eprintln!("largest shift of a moment: {worst_exact} on 2^-106, {worst} grains of 2^-16 released");
}

/// An exact slot: period 4 (the ring `1, i, −1, −i` is the turn's own constraint identities) and a
/// dyadic skin `D(d) = 2^(30−d)`, so `ζ^a ζ^b = 2^30 ζ^(a+b)` and `D(a) D(b) = 2^30 D(a+b)` as integers.
fn exact_slot() -> Slot {
    let one = 1i128 << MOVE_BITS;
    let full = vec![(one, 0), (0, one), (-one, 0), (0, -one)];
    let ring = full.iter().map(|&(a, b)| (a as i64, b as i64)).collect();
    let decay = (0..16).map(|d| 1i64 << (MOVE_BITS as usize - d)).collect();
    Slot { n: 4, ring, decay, full }
}

/// The span's face, exactly, where the faces compose exactly and the near field covers the span:
/// `s⁺_j − ζ^(i−j) D(j−i) s⁺_i` is the moment at `j` of the strand with the sources at or before `i`
/// removed, `2^60 s⁺_j − z s⁺_i = 2^60 s⁺_j[k > i]` with `z = ζ^(i−j) D(j−i)` on `2^(−60)`, and in the
/// released grain it is within the releases' rounding.
#[test]
fn the_span_face_reads_the_sources_between_its_boundaries_exactly() {
    let slot = exact_slot();
    let mut next = mixer(31);
    let zero = vec![(0i64, 0i64); NEAR];
    for _ in 0..8 {
        let before = strand(&mut next, NEAR, 1 << 17);
        let at = moment_exact(&before, &zero, &slot.ring, slot.n, &slot.decay, None).unwrap();
        let at_released = moments(&before, &zero, &slot.ring, slot.n, &slot.decay, None).unwrap();
        for i in 0..NEAR {
            for j in i + 1..NEAR {
                let mut masked = before.clone();
                masked[..=i].iter_mut().for_each(|p| *p = (0, 0));
                let between = moment_exact(&masked, &zero, &slot.ring, slot.n, &slot.decay, None).unwrap();
                let z = {
                    let p = slot.phase(i as i64 - j as i64);
                    let s = slot.decay[j - i] as i128;
                    (p.0 * s, p.1 * s)
                };
                // The exact face: 2^60 s_j − z s_i = 2^60 s_j[k > i], and z s_i divisible by 2^60.
                let zs = bmul(&bw(z), &bw(at[i]));
                let unit = BigInt::from(1) << 60usize;
                assert!(&zs.0 % &unit == BigInt::from(0) && &zs.1 % &unit == BigInt::from(0), "i {i} j {j}");
                let face = (bw(at[j]).0 - &zs.0 / &unit, bw(at[j]).1 - &zs.1 / &unit);
                assert_eq!(face, bw(between[j]), "i {i} j {j}");
                // The consumer's face, from the released moments, to the releases' rounding.
                let turned = gmul(z, gwide(at_released[i]));
                let f = (at_released[j].0 as i128 - release(turned.0, 60), at_released[j].1 as i128 - release(turned.1, 60));
                let want = released(&between[j..=j], COEFFICIENT_BITS)[0];
                assert!((f.0 - want.0).abs() <= 3 && (f.1 - want.1).abs() <= 3, "i {i} j {j}: {f:?} against {want:?}");
            }
        }
    }
}

/// The span's face on the founded rings, a longer strand: its deviation from the moment of the
/// between-sources strand is exactly the blur of the sources at or before `i`,
/// `Σ_(k ≤ i) (2^60 W_(j,k) − z W_(i,k)) E_k` (an identity of integers), and the released face is within
/// that gap and the releases' rounding.
#[test]
fn the_span_face_on_the_founded_rings_deviates_by_exactly_the_blur() {
    let mut next = mixer(37);
    let zero = vec![(0i64, 0i64); 48];
    let mut worst = 0i128;
    for slot in slots(300, 6) {
        let before = strand(&mut next, 48, 1 << 17);
        let at = moment_exact(&before, &zero, &slot.ring, slot.n, &slot.decay, None).unwrap();
        let at_released = moments(&before, &zero, &slot.ring, slot.n, &slot.decay, None).unwrap();
        for (i, j) in [(0usize, 1usize), (3, 8), (10, 11), (10, 30), (20, 47), (30, 40), (46, 47), (5, 47)] {
            let mut masked = before.clone();
            masked[..=i].iter_mut().for_each(|p| *p = (0, 0));
            let between = moment_exact(&masked, &zero, &slot.ring, slot.n, &slot.decay, None).unwrap();
            let z = {
                let p = slot.phase(i as i64 - j as i64);
                let s = slot.decay[j - i] as i128;
                (p.0 * s, p.1 * s)
            };
            // 2^60 (s_j − s_j[k > i]) − z s_i, in integers.
            let zs = bmul(&bw(z), &bw(at[i]));
            let residual = (((bw(at[j]).0 - bw(between[j]).0) << 60usize) - zs.0, ((bw(at[j]).1 - bw(between[j]).1) << 60usize) - zs.1);
            let (mut gap_re, mut gap_im, mut bound) = (BigInt::from(0), BigInt::from(0), BigInt::from(0));
            for k in 0..=i {
                let (wj, wi) = (bw(coefficient(&slot, j, k)), bw(coefficient(&slot, i, k)));
                let turned = bmul(&bw(z), &wi);
                let g = ((wj.0 << 60usize) - turned.0, (wj.1 << 60usize) - turned.1);
                let e = bw(gwide(before[k]));
                let product = bmul(&g, &e);
                gap_re += product.0;
                gap_im += product.1;
                let big = if babs(&g.0) > babs(&g.1) { babs(&g.0) } else { babs(&g.1) };
                bound += big * (babs(&e.0) + babs(&e.1));
            }
            assert_eq!(residual, (gap_re, gap_im), "n {} ({i},{j})", slot.n);
            // The released face against the released between-sources moment: the gap, plus roundings.
            let turned = gmul(z, gwide(at_released[i]));
            let f = (at_released[j].0 as i128 - release(turned.0, 60), at_released[j].1 as i128 - release(turned.1, 60));
            let want = released(&between[j..=j], COEFFICIENT_BITS)[0];
            let off = (f.0 - want.0).abs().max((f.1 - want.1).abs());
            let allowed = i128::try_from(bound >> 150usize).unwrap() + 3;
            assert!(off <= allowed, "n {} ({i},{j}): {off} grains against {allowed}", slot.n);
            worst = worst.max(off);
        }
    }
    // The blur is the declared approximation, and it is not small on a slow ring.
    assert!(worst > 0, "the blur was never seen");
    eprintln!("largest deviation of a released span face: {worst} grains of 2^-16");
}

/// A source past the skin is never read: on the ring whose decay is zero beyond seven sites, the span's
/// face is exact when the sources at or before `i` lie eight or more sites back, however long the strand.
#[test]
fn a_source_past_the_skin_is_not_misread() {
    let slot = slots(300, 6).into_iter().find(|s| s.n == 2).unwrap();
    assert!(slot.decay[7..].iter().all(|&d| d == 0) && slot.decay[6] != 0);
    let mut next = mixer(41);
    let sites = 80;
    let zero = vec![(0i64, 0i64); sites];
    for (i, j) in [(20usize, 21usize), (20, 27), (40, 79), (50, 52)] {
        let mut before = strand(&mut next, sites, 1 << 17);
        // Nothing within the near edge before `i`: the sources at or before `i` are all 8 or more back.
        before[i - 7..=i].iter_mut().for_each(|p| *p = (0, 0));
        let mut masked = before.clone();
        masked[..=i].iter_mut().for_each(|p| *p = (0, 0));
        let at = moment_exact(&before, &zero, &slot.ring, slot.n, &slot.decay, None).unwrap();
        let between = moment_exact(&masked, &zero, &slot.ring, slot.n, &slot.decay, None).unwrap();
        let p = slot.phase(i as i64 - j as i64);
        let s = slot.decay[j - i] as i128;
        assert_eq!(at[i], (0, 0), "i {i}");
        let zs = gmul((p.0 * s, p.1 * s), at[i]);
        assert_eq!(zs, (0, 0), "i {i}");
        assert_eq!(at[j], between[j], "({i},{j})");
    }
}

/// The certificate is the l1 bound `(S + 1) D̂ R max(R, 2^30) Ê < 2^127`.
#[test]
fn the_certificate_is_the_l1_bound() {
    let (r, d, e) = (1u128 << 31, 1u128 << 30, 1u128 << 18);
    // (S + 1) 2^110 < 2^127 exactly while S + 1 < 2^17.
    assert!(certificate((1 << 17) - 2, r, d, e));
    assert!(!certificate((1 << 17) - 1, r, d, e));
    // The founded unit ring (l1 below 2^31) and encodings below 2^17 admit the reach.
    assert!(certificate(2221, (1 << 30) + (1 << 29), 1 << 30, 1 << 18));
    // A zero decay or a zero input is certified (nothing to carry), saturation is a refusal.
    assert!(certificate(1 << 20, r, 0, 0));
    assert!(!certificate(u128::MAX - 1, r, d, e));
    assert!(!certificate(10, u128::MAX, d, e));
}

/// The return's certificate is `max(D̂, 1) R (NEAR G + S (⌊R G / 2^30⌋ + 1)) < 2^127`, linear in the
/// strand: for `R = 2^31`, `D̂ = 2^30` it is `2^61 (6 G + S (2 G + 1))`.
#[test]
fn the_return_certificate_is_the_released_bound() {
    let (r, d) = (1u128 << 31, 1u128 << 30);
    // At the crib region's 406 sites: 2^61 (818 G + 406) < 2^127 up to G = 2^56.
    assert!(return_certificate(406, r, d, 1 << 56));
    assert!(!return_certificate(406, r, d, 1 << 57));
    // At the reach of reading 8, 2221 sites: 2^61 (4448 G + 2221), up to G = 2^53.
    assert!(return_certificate(2221, r, d, 1 << 53));
    assert!(!return_certificate(2221, r, d, 1 << 54));
    // The crib region's l1 of 2^28.1, which the exact transpose's carrier refuses (about 2^27.3).
    let g = 285_000_000u128;
    assert!(return_certificate(406, (1 << 30) + (1 << 29), d, g));
    assert!(!certificate(406, (1 << 30) + (1 << 29), d, g));
    // Zero decay or covector is admitted, saturation is a refusal.
    assert!(return_certificate(1 << 20, r, 0, 0));
    // The released term's grain: even a zero covector releases to l1 at most 1 a source (the +1).
    assert!(!return_certificate(1 << 96, 1 << 31, 1, 0));
    assert!(return_certificate((1 << 96) - 1, 1 << 31, 1, 0));
    assert!(!return_certificate(u128::MAX, r, d, 1));
    assert!(!return_certificate(10, u128::MAX, d, 1 << 20));
    assert!(!return_certificate(10, r, d, u128::MAX));
}

/// A strand at the certificate's edge, all terms aligned, is carried exactly (the bound is
/// sufficient, never a wrap), and one past it is refused.
#[test]
fn the_certificate_admits_the_largest_aligned_strand_and_refuses_one_past_it() {
    let ring = [(1i64 << MOVE_BITS, 0i64)];
    let decay = vec![1i64 << MOVE_BITS; 300];
    let sites = 300;
    // Components below 2^17 (l1 below 2^18).
    let big = (1i64 << 17) - 1;
    let before = vec![(big, big); sites];
    let got = moments(&before, &before, &ring, 1, &decay, None).unwrap();
    for (t, &g) in got.iter().enumerate() {
        let count = (t + 1 + (sites - t)) as i64;
        assert_eq!(g, (count * big, count * big));
    }
    // Encodings of 2^60: l1 2^61 past the carrier at this ring and decay.
    let huge = vec![(1i64 << 60, 1i64 << 60); sites];
    assert_eq!(moments(&huge, &huge, &ring, 1, &decay, None), Err(TowerError::Refused("a strand past the l1 certificate of its 128-bit carrier")));
    assert!(moments_return(&huge, &ring, 1, &decay, None).is_err());
    // A covector of 2^30 on 2^(−24) (64.0) is admitted: the released return's carrier is linear in the
    // strand, and a stationary slot hears the plain sum, exactly.
    let loud = vec![(1i64 << 30, 1i64 << 30); sites];
    let (plus, minus) = moments_return(&loud, &ring, 1, &decay, None).unwrap();
    for k in 0..sites {
        let hear = |count: usize| ((count as i128) << 30, (count as i128) << 30);
        assert_eq!((plus[k], minus[k]), (hear(sites - k), hear(k + 1)));
    }
    // Components below 2^50 (about 10^8 units) are too; the 2^60 covector above is refused.
    let louder = vec![((1i64 << 50) - 1, (1i64 << 50) - 1); sites];
    let (plus, minus) = moments_return(&louder, &ring, 1, &decay, None).unwrap();
    let unit = (1i128 << 50) - 1;
    for k in 0..sites {
        assert_eq!((plus[k], minus[k]), (((sites - k) as i128 * unit, (sites - k) as i128 * unit), ((k + 1) as i128 * unit, (k + 1) as i128 * unit)));
    }
}

#[test]
fn malformed_strands_are_refused() {
    let slot = slots(16, 4).into_iter().find(|s| s.n == 27).unwrap();
    let e = vec![(1i64, 1i64); 8];
    assert!(moments(&e, &e[..7], &slot.ring, slot.n, &slot.decay, None).is_err(), "unequal strands");
    assert!(moments(&e, &e, &slot.ring, 0, &slot.decay, None).is_err(), "period zero");
    assert!(moments(&e, &e, &slot.ring[..4], slot.n, &slot.decay, None).is_err(), "ring shorter than the places");
    assert!(moments(&e, &e, &slot.ring, slot.n, &slot.decay[..7], None).is_err(), "skin shorter than the strand");
    assert!(moments_return(&e, &slot.ring[..4], slot.n, &slot.decay, None).is_err());
    assert!(moments_return(&e, &slot.ring, slot.n, &slot.decay[..7], None).is_err());
    // A short ring is enough where the period is shorter than the strand.
    let two = slots(16, 4).into_iter().find(|s| s.n == 2).unwrap();
    assert!(moments(&e, &e, &two.ring, 2, &two.decay, None).is_ok());
    // No strand, no moment.
    assert_eq!(moments(&[], &[], &[], 0, &[], None), Ok(Vec::new()));
    assert_eq!(moments_return(&[], &[], 0, &[], None), Ok((Vec::new(), Vec::new())));
}

/// A paced strand's faces from a founded field's slot: the turn and skin at any clock (§16, Law 1).
struct Paced {
    n: usize,
    ring: Vec<(i64, i64)>,
    decay: Vec<i64>,
    pi: i128,
    exponential: crate::hnn::keyed_modes::Exponential,
}

fn paced_slots(reach: usize, modes: usize) -> Vec<Paced> {
    let declaration = FieldDeclaration { alphabet: 5, width: 8, heads: 2, modes, still: 1, contacts: 4, ticks: 2, frames: 2, reach, lanes: 1, depth: 0 };
    let mut next = mixer(7);
    let keys: Vec<u8> = (0..1usize << 14).flat_map(|_| next().to_be_bytes()).collect();
    let field = Field::found(declaration, &keys).unwrap();
    let pi = half_turn(MOVE_BITS + 16);
    field.rings().iter().zip(field.decays()).map(|((n, ring), decay)| Paced { n: *n, ring: ring.clone(), decay: decay.clone(), pi, exponential: field.exponential().clone() }).collect()
}

/// A clock of `sites` places whose rates are drawn from `rates` (on `2^(−24)`): `(τ, σ)`, `τ_0 = σ_0 = 0`.
fn clock_of(next: &mut impl FnMut() -> u64, sites: usize, rates: &[i64]) -> (Vec<i64>, Vec<i64>) {
    let (mut tau, mut sigma) = (vec![0i64], vec![0i64]);
    for _ in 1..sites {
        let k = rates[(next() % rates.len() as u64) as usize];
        tau.push(tau.last().unwrap() + k);
        sigma.push(sigma.last().unwrap() + k.abs());
    }
    tau.truncate(sites);
    sigma.truncate(sites);
    (tau, sigma)
}

/// A strand paced at its own places (`τ_t = σ_t = t`) is the byte place's moment and return, bit for bit,
/// on every slot and length: the founding reads today's field.
#[test]
fn a_strand_paced_at_its_own_places_is_the_byte_moment() {
    let mut next = mixer(29);
    for slot in paced_slots(16, 4).into_iter().chain(paced_slots(300, 6)) {
        let reach = slot.decay.len();
        let turn = |r: i128| crate::hnn::tower::field::turn_phasor(r, slot.n, slot.pi);
        let skin = |s: i128| crate::hnn::tower::field::skin_of(s, slot.n, slot.pi, &slot.exponential);
        for &sites in LENGTHS.iter().filter(|&&s| s <= reach) {
            let places: Vec<i64> = (0..sites as i64).map(|t| t << crate::hnn::tower::field::PACE_BITS).collect();
            let pace = Pace { tau: &places, sigma: &places, turn: &turn, skin: &skin };
            let (before, after, ds) = (strand(&mut next, sites, 1 << 16), strand(&mut next, sites, 1 << 16), strand(&mut next, sites, 1 << 24));
            assert_eq!(moment_exact(&before, &after, &slot.ring, slot.n, &slot.decay, Some(&pace)).unwrap(), moment_exact(&before, &after, &slot.ring, slot.n, &slot.decay, None).unwrap(), "n {} S {sites}", slot.n);
            assert_eq!(moment_return_exact(&ds, &slot.ring, slot.n, &slot.decay, Some(&pace)).unwrap(), moment_return_exact(&ds, &slot.ring, slot.n, &slot.decay, None).unwrap(), "n {} S {sites}", slot.n);
        }
    }
}

/// A paced strand's moment and return equal their definitions summed directly over every pair, bit for bit:
/// near `ζ^(τ_k − τ_t) e^(−2π|σ_t − σ_k|/n) 2^30`, far `e^(−2π|σ_t − σ_(t±2^ℓ)|/n) conj(ζ^(τ_t)) ζ^(τ_k)` (the
/// octave's skin at the receiver's place `2^ℓ` away on the source's side), and the return their transpose with
/// the far turned covector `release(ζ^(τ_t) δs_t, 30)` once a term; with rates that stop, run backward and are
/// fractional, so the clock is no byte place.
#[test]
fn a_paced_strand_equals_its_definition_bit_for_bit() {
    let mut next = mixer(31);
    let one = 1i64 << crate::hnn::tower::field::PACE_BITS;
    let rates = [0, one, one, 2 * one, -one / 2, one / 3, 5 * one / 7];
    let mut checked = 0usize;
    for slot in paced_slots(300, 6) {
        let turn = |r: i128| crate::hnn::tower::field::turn_phasor(r, slot.n, slot.pi);
        let skin = |s: i128| crate::hnn::tower::field::skin_of(s, slot.n, slot.pi, &slot.exponential);
        for &sites in LENGTHS.iter().filter(|&&s| s <= 100) {
            let (tau, sigma) = clock_of(&mut next, sites, &rates);
            let pace = Pace { tau: &tau, sigma: &sigma, turn: &turn, skin: &skin };
            let face = |r: i128| -> G { let (a, b) = turn(r); (a as i128, b as i128) };
            let w = |t: usize, k: usize| -> G {
                let d = t.abs_diff(k);
                if d < NEAR {
                    let z = face(tau[k] as i128 - tau[t] as i128);
                    let s = (skin(sigma[t] as i128 - sigma[k] as i128) as i128) << MOVE_BITS;
                    (z.0 * s, z.1 * s)
                } else {
                    let level = d.ilog2();
                    let edge = if k > t { t + (1 << level) } else { t - (1 << level) };
                    let c = gmul(gconj(face(tau[t] as i128)), face(tau[k] as i128));
                    let s = skin(sigma[t] as i128 - sigma[edge] as i128) as i128;
                    (c.0 * s, c.1 * s)
                }
            };
            let (before, after, ds) = (strand(&mut next, sites, 1 << 16), strand(&mut next, sites, 1 << 16), strand(&mut next, sites, 1 << 24));
            let want: Vec<G> = (0..sites)
                .map(|t| (0..sites).fold((0i128, 0i128), |s, k| {
                    let s = if k <= t { gadd(s, gmul(w(t, k), gwide(before[k]))) } else { s };
                    if k >= t { gadd(s, gmul(w(t, k), gwide(after[k]))) } else { s }
                }))
                .collect();
            assert_eq!(moment_exact(&before, &after, &slot.ring, slot.n, &slot.decay, Some(&pace)).unwrap(), want, "n {} S {sites}", slot.n);
            let turned: Vec<G> = (0..sites).map(|t| { let p = gmul(face(tau[t] as i128), gwide(ds[t])); (release(p.0, MOVE_BITS), release(p.1, MOVE_BITS)) }).collect();
            let term = |k: usize, t: usize| -> G {
                let d = t.abs_diff(k);
                if d < NEAR {
                    let c = gmul(gconj(face(tau[k] as i128 - tau[t] as i128)), gwide(ds[t]));
                    let s = skin(sigma[t] as i128 - sigma[k] as i128) as i128;
                    (c.0 * s, c.1 * s)
                } else {
                    let level = d.ilog2();
                    let edge = if k > t { t + (1 << level) } else { t - (1 << level) };
                    let s = skin(sigma[t] as i128 - sigma[edge] as i128) as i128;
                    gmul(gconj(face(tau[k] as i128)), (turned[t].0 * s, turned[t].1 * s))
                }
            };
            let plus: Vec<G> = (0..sites).map(|k| (k..sites).fold((0i128, 0i128), |a, t| gadd(a, term(k, t)))).collect();
            let minus: Vec<G> = (0..sites).map(|k| (0..=k).fold((0i128, 0i128), |a, t| gadd(a, term(k, t)))).collect();
            assert_eq!(moment_return_exact(&ds, &slot.ring, slot.n, &slot.decay, Some(&pace)).unwrap(), (plus, minus), "n {} S {sites}", slot.n);
            checked += sites;
        }
    }
    assert!(checked > 1000);
}
