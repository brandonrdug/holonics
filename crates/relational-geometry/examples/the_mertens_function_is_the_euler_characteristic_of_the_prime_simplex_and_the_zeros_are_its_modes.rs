//! The Mertens function is the Euler characteristic of the prime simplex, and the zeros are its
//! modes.
//!
//! The squarefree numbers at most `N` are the faces of a simplicial complex on the primes:
//!
//! ```text
//!     K_N = { S ⊂ primes : Π_{p ∈ S} p ≤ N }
//! ```
//!
//! closed under subsets because a sub-product is smaller. A face with `ω(n) = k + 1` primes is a
//! `k`-simplex — `Δ⁰_{17}`, `Δ¹_{3·7}`, `Δ²_{2·3·5}`, `Δ³_{2·3·5·7}` — and the number `n` is the
//! shadow of the exponent-lattice point `(1, …, 1)` under the functional `⟨log p, k⟩`. The Möbius
//! polarity `μ(n) = (−1)^{ω(n)}` is the orientation by dimension parity, so
//!
//! ```text
//!     M(N) = Σ_{n ≤ N} μ(n) = Σ_{S ∈ K_N} (−1)^{|S|} = −χ̃(K_N)
//! ```
//!
//! **the Mertens function is minus the reduced Euler characteristic of the prime simplex**, and
//! `Σ_{d | n} μ(d) = 0` for `n > 1` is the reduced characteristic of one simplex vanishing — the
//! polarities of a full face recombine to the null cone. The weighted characteristic
//! `Σ_S (−1)^{|S|} (ΠS)^{−s} = 1/ζ(s)` has its poles at the zeros: **the zeros are the modes of
//! `χ`**, and the Riemann hypothesis is `χ̃(K_N) = O(N^{1/2+ε})`.
//!
//! `K_N` is a *shifted* complex (replace a prime by a smaller prime and the product drops), so by
//! Björner–Kalai it is homotopy equivalent to a wedge of spheres, one `i`-sphere for every face
//! `F` with `|F| = i + 1` that avoids the least vertex `2` and whose join with `2` leaves the
//! complex:
//!
//! ```text
//!     β̃_i(K_N) = #{ odd squarefree n ∈ (N/2, N] : ω(n) = i + 1 }.
//! ```
//!
//! So the homology of the prime simplex lives entirely on the odd squarefree numbers in the top
//! octave `(N/2, N]`, graded by the number of prime factors, and `M(N)` is their alternating count.
//! Each Betti number is of size `N (log log N)^i / (i! log N)`; their alternating sum is `O(√N)`
//! under the hypothesis — the cancellation *is* the content.
//!
//! Two returns, sectioned so each runs under the process aperture:
//!
//! - `combinatorics [N_max]`: the exact `f`-vector and Betti vector of `K_N` at `N = 10^k`, the
//!   identity `M(N) = −χ̃(K_N)` checked at **every** `N ≤ N_max`, the sphere generators of a small
//!   `K_N` written as simplex symbols, and `M(N)²` against `N` as exact integers.
//! - `modes [dir] [x_max] [workers] [x_min]`: the certified zeros reconstruct `M(x)` through the
//!   explicit formula `M(x) = −2 + Σ_ρ x^ρ/(ρ ζ′(ρ)) + Σ_k (−1)^{k−1} (2π/x)^{2k}/((2k)! k ζ(2k+1))`
//!   (Titchmarsh 14.27, conditional on simple zeros), with `ζ′(ρ)` enclosed by the second-order
//!   jet over the zero's own certified box and its Euler–Maclaurin remainder radius. The residual
//!   `|M(x) − M_T(x)|` per cutoff `T` and the reconstructed jumps `μ(n)` at squarefree `n` are the
//!   measurement. Every quantity is an exact rational or an exact rational interval; a bound
//!   printed as `k/64` is the least such dyadic above the exact bound.

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Instant;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use relational_geometry::{
    ComplexInterval, ComplexReceiverBox, EtaRatioAtlas, ExactSeriesConfig, RatInterval,
    cis_interval, derive_euler_maclaurin_start, exp_interval, log_rational_interval, pi_interval,
    zeta_evaluate_jet2_with_head,
};

const DEFAULT_ARTIFACTS: &str =
    "output/the_card_returns_the_eta_boundary_and_the_zero_is_a_winding";
const OUTPUT: &str = "output/the_mertens_function_is_the_euler_characteristic_of_the_prime_simplex";
const BITS: u32 = 64;
const TERMS: u32 = 20;
/// The grain the Euler–Maclaurin start is derived for at each zero.
const JET_GRAIN_BITS: u32 = 24;

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

/// The least `k/2^bits` at or above `value` — an exact upper bound, never a rendering.
fn dyadic_ceiling(value: &BigRational, bits: u32) -> String {
    let scale = BigInt::one() << bits as usize;
    let scaled = value * BigRational::from_integer(scale.clone());
    let k = scaled.ceil().to_integer();
    let reduced = BigRational::new(k, scale);
    format!("{reduced}")
}

/// `[lower, upper]` widened outward to the dyadic grain `2^-bits`.
fn dyadic_interval(interval: &RatInterval, bits: u32) -> String {
    let scale = BigInt::one() << bits as usize;
    let lo = (&interval.lower * BigRational::from_integer(scale.clone()))
        .floor()
        .to_integer();
    let hi = (&interval.upper * BigRational::from_integer(scale.clone()))
        .ceil()
        .to_integer();
    format!(
        "[{}, {}]",
        BigRational::new(lo, scale.clone()),
        BigRational::new(hi, scale)
    )
}

// --- the prime simplex ------------------------------------------------------------------------

struct Sieve {
    mu: Vec<i8>,
    omega: Vec<u8>,
}

fn sieve(n_max: usize) -> Sieve {
    let mut mu = vec![1i8; n_max + 1];
    let mut omega = vec![0u8; n_max + 1];
    let mut composite = vec![false; n_max + 1];
    mu[0] = 0;
    for p in 2..=n_max {
        if composite[p] {
            continue;
        }
        let mut m = p;
        while m <= n_max {
            composite[m] = true;
            mu[m] = -mu[m];
            omega[m] += 1;
            m += p;
        }
        if let Some(p2) = p.checked_mul(p) {
            let mut m = p2;
            while m <= n_max {
                mu[m] = 0;
                m += p2;
            }
        }
    }
    // primes were marked composite for the loop; that only affected the sieve order
    Sieve { mu, omega }
}

fn prime_factors(mut n: u64) -> Vec<u64> {
    let mut out = Vec::new();
    let mut p = 2;
    while p * p <= n {
        if n % p == 0 {
            out.push(p);
            while n % p == 0 {
                n /= p;
            }
        }
        p += 1;
    }
    if n > 1 {
        out.push(n);
    }
    out
}

/// `Δ^k_{p·q·…}`: the face of the prime simplex a squarefree number is the shadow of.
fn simplex_symbol(n: u64) -> String {
    let primes = prime_factors(n);
    let superscript: String = (primes.len() - 1)
        .to_string()
        .chars()
        .map(|c| match c {
            '0' => '⁰',
            '1' => '¹',
            '2' => '²',
            '3' => '³',
            '4' => '⁴',
            '5' => '⁵',
            '6' => '⁶',
            '7' => '⁷',
            '8' => '⁸',
            _ => '⁹',
        })
        .collect();
    format!(
        "Δ{superscript}_{{{}}}",
        primes
            .iter()
            .map(|p| p.to_string())
            .collect::<Vec<_>>()
            .join("·")
    )
}

fn combinatorics(n_max: usize) -> Result<String, String> {
    let started = Instant::now();
    let s = sieve(n_max);
    let mut report = String::new();
    // the identity M(N) = −χ̃(K_N) = Σ_{odd squarefree m ∈ (N/2, N]} μ(m), at every N
    let mut mertens = 0i64;
    let mut odd_prefix = vec![0i64; n_max + 1];
    let mut verified = 0usize;
    let mut first_failure: Option<usize> = None;
    for n in 1..=n_max {
        mertens += i64::from(s.mu[n]);
        odd_prefix[n] = odd_prefix[n - 1] + if n % 2 == 1 { i64::from(s.mu[n]) } else { 0 };
        let euler = odd_prefix[n] - odd_prefix[n / 2];
        if euler == mertens {
            verified += 1;
        } else if first_failure.is_none() {
            first_failure = Some(n);
        }
    }
    report.push_str(&format!(
        "identity M(N) = −χ̃(K_N) = Σ_{{odd squarefree m ∈ (N/2, N]}} μ(m): verified at {verified} of {n_max} values of N{}\n",
        match first_failure {
            None => String::new(),
            Some(n) => format!("; FIRST FAILURE at N = {n}"),
        }
    ));
    // f-vectors and Betti vectors at N = 10^k
    let mut n_values: Vec<usize> = Vec::new();
    let mut n = 10usize;
    while n <= n_max {
        n_values.push(n);
        n *= 10;
    }
    if n_values.last() != Some(&n_max) {
        n_values.push(n_max);
    }
    report.push_str("\nN\tf-vector (faces by dimension: squarefree n ≤ N with ω = i+1)\tβ̃-vector (odd squarefree n ∈ (N/2, N] with ω = i+1)\tspheres Σβ̃\tχ̃(K_N)\tM(N)\tM(N)²\tM(N)²/N\n");
    for &big_n in &n_values {
        let mut f: BTreeMap<usize, u64> = BTreeMap::new();
        let mut betti: BTreeMap<usize, u64> = BTreeMap::new();
        let mut m_n = 0i64;
        for n in 1..=big_n {
            if s.mu[n] == 0 {
                continue;
            }
            m_n += i64::from(s.mu[n]);
            let dim = usize::from(s.omega[n]);
            if dim == 0 {
                continue; // the empty face, n = 1
            }
            *f.entry(dim - 1).or_default() += 1;
            if n % 2 == 1 && 2 * n > big_n {
                *betti.entry(dim - 1).or_default() += 1;
            }
        }
        let spheres: u64 = betti.values().sum();
        let chi: i64 = betti
            .iter()
            .map(|(i, b)| if i % 2 == 0 { *b as i64 } else { -(*b as i64) })
            .sum();
        let square = m_n * m_n;
        report.push_str(&format!(
            "{big_n}\t{:?}\t{:?}\t{spheres}\t{chi}\t{m_n}\t{square}\t{}\n",
            f.values().collect::<Vec<_>>(),
            betti.values().collect::<Vec<_>>(),
            rat(square, big_n as i64)
        ));
    }
    // a small complex written out
    let small = 30usize;
    report.push_str(&format!(
        "\nK_{small}: faces {}\n",
        (2..=small)
            .filter(|&n| s.mu[n] != 0)
            .map(|n| simplex_symbol(n as u64))
            .collect::<Vec<_>>()
            .join(" ")
    ));
    report.push_str(&format!(
        "K_{small}: sphere generators (odd squarefree in ({}, {small}]) {}  →  χ̃ = {}, M({small}) = {}\n",
        small / 2,
        (small / 2 + 1..=small)
            .filter(|&n| n % 2 == 1 && s.mu[n] != 0)
            .map(|n| simplex_symbol(n as u64))
            .collect::<Vec<_>>()
            .join(" "),
        odd_prefix[small] - odd_prefix[small / 2],
        (1..=small).map(|n| i64::from(s.mu[n])).sum::<i64>()
    ));
    // the polarity recombination inside one face: Σ_{d | n} μ(d) = 0
    let n = 210u64;
    let divisor_sum: i64 = (1..=n)
        .filter(|d| n % d == 0)
        .map(|d| i64::from(s.mu[d as usize]))
        .sum();
    report.push_str(&format!(
        "one face {}: Σ_{{d | {n}}} μ(d) = {divisor_sum} — the reduced characteristic of a simplex, the null cone\n",
        simplex_symbol(n)
    ));
    report.push_str(&format!(
        "elapsed_s={:.1}\n",
        started.elapsed().as_secs_f64()
    ));
    Ok(report)
}

// --- the zeros as modes ------------------------------------------------------------------------

/// A certified zero on the line with `ζ′(ρ)` enclosed over its own box.
struct Mode {
    gamma: RatInterval,
    zeta_prime: ComplexInterval,
    start: u32,
}

fn read_zeros(directory: &PathBuf) -> Result<(Vec<RatInterval>, BigRational), String> {
    let mut paths: Vec<PathBuf> = fs::read_dir(directory)
        .map_err(|e| e.to_string())?
        .filter_map(|entry| entry.ok().map(|e| e.path()))
        .filter(|path| {
            path.file_name().and_then(|n| n.to_str()).is_some_and(|n| {
                n.starts_with("holonic-eta-ratio-atlas-resident-") && n.ends_with(".ron")
            })
        })
        .collect();
    paths.sort();
    let mut zeros: Vec<RatInterval> = Vec::new();
    let mut top = BigRational::zero();
    for path in &paths {
        let atlas: EtaRatioAtlas =
            ron::from_str(&fs::read_to_string(path).map_err(|e| e.to_string())?)
                .map_err(|e| format!("{}: {e}", path.display()))?;
        if atlas.scan.tau.upper > top {
            top = atlas.scan.tau.upper.clone();
        }
        for lineage in &atlas.zero_lineages {
            zeros.push(lineage.final_receiver.tau.clone());
        }
    }
    zeros.sort_by(|a, b| a.lower.cmp(&b.lower));
    Ok((zeros, top))
}

/// `ζ′(ρ)` over the box `σ = 1/2`, `τ = γ`: the jet's first component widened by its certified
/// Euler–Maclaurin remainder radius. The zero sits on the line by the reflection theorem, so
/// the box is exact in `σ`.
fn zeta_prime_enclosure(gamma: &RatInterval) -> Result<Mode, String> {
    let receiver = ComplexReceiverBox {
        sigma: RatInterval::point(rat(1, 2)),
        tau: gamma.clone(),
    };
    let base = ExactSeriesConfig {
        dyadic_bits: 96,
        ..ExactSeriesConfig::default()
    };
    let config = derive_euler_maclaurin_start(&receiver, &base, JET_GRAIN_BITS)
        .map_err(|e| e.to_string())?;
    let jet = zeta_evaluate_jet2_with_head(&receiver, &config, None).map_err(|e| e.to_string())?;
    let r1 = jet.remainders[1].clone();
    let widen = RatInterval::symmetric(r1);
    let zeta_prime =
        ComplexInterval::new(jet.jet.first.re.add(&widen), jet.jet.first.im.add(&widen));
    // the value must enclose zero: the box contains the zero
    let r0 = jet.remainders[0].clone();
    let value = ComplexInterval::new(
        jet.jet.value.re.add(&RatInterval::symmetric(r0.clone())),
        jet.jet.value.im.add(&RatInterval::symmetric(r0)),
    );
    if !value.contains_origin() {
        return Err(format!(
            "the jet over the certified box {} does not enclose ζ = 0",
            gamma
        ));
    }
    Ok(Mode {
        gamma: gamma.clone(),
        zeta_prime,
        start: config.euler_maclaurin_start,
    })
}

/// `Σ_{|γ| ≤ T} 2 Re[x^ρ / (ρ ζ′(ρ))]` at every cutoff at once.
fn mode_sums(
    modes: &[Mode],
    x: &BigRational,
    cutoffs: &[BigRational],
) -> Result<Vec<RatInterval>, String> {
    let log_x = log_rational_interval(x, TERMS + 8, BITS).map_err(|e| e.to_string())?;
    let root_x = exp_interval(&log_x.scale(&rat(1, 2)), TERMS, BITS);
    let half = rat(1, 2);
    let mut sum = RatInterval::point(BigRational::zero());
    let mut out = Vec::with_capacity(cutoffs.len());
    let mut next_cutoff = 0usize;
    for mode in modes {
        while next_cutoff < cutoffs.len() && mode.gamma.lower > cutoffs[next_cutoff] {
            out.push(sum.clone());
            next_cutoff += 1;
        }
        if next_cutoff >= cutoffs.len() {
            break;
        }
        let gamma = &mode.gamma;
        let a = &mode.zeta_prime.re;
        let b = &mode.zeta_prime.im;
        // w = ρ ζ′(ρ) = (½ + iγ)(a + ib)
        let w_re = a.scale(&half).subtract(&gamma.multiply(b));
        let w_im = gamma.multiply(a).add(&b.scale(&half));
        let w_norm = w_re.square().add(&w_im.square());
        if w_norm.contains_zero() {
            return Err(format!("ρ ζ′(ρ) is not separated from zero at γ ∈ {gamma}"));
        }
        let turn = cis_interval(&gamma.multiply(&log_x), TERMS, BITS);
        // 2 Re[x^ρ w̄ / |w|²] = 2 √x (cos·Re w + sin·Im w) / |w|²
        let numerator = turn.re.multiply(&w_re).add(&turn.im.multiply(&w_im));
        let term = root_x
            .multiply(&numerator)
            .divide(&w_norm)
            .map_err(|e| e.to_string())?
            .scale(&rat(2, 1));
        sum = sum.add(&term).round_out(BITS);
    }
    while out.len() < cutoffs.len() {
        out.push(sum.clone());
    }
    Ok(out)
}

/// `Σ_{k ≥ 1} (−1)^{k−1} (2π/x)^{2k} / ((2k)! k ζ(2k+1))` with `ζ(2k+1) ∈ [1, 5/4]` and a tail
/// bound of twice the first omitted magnitude.
fn trivial_zero_series(x: &BigRational) -> RatInterval {
    let two_pi_over_x = pi_interval(BITS).scale(&(rat(2, 1) / x));
    let q = two_pi_over_x.square();
    let zeta_band = RatInterval::new(rat(4, 5), rat(1, 1)); // 1/ζ(2k+1) ∈ [4/5, 1]
    let mut sum = RatInterval::point(BigRational::zero());
    let mut power = RatInterval::point(BigRational::one());
    let mut factorial = BigRational::one();
    let terms = 10u32;
    let mut last_magnitude = RatInterval::point(BigRational::zero());
    for k in 1..=terms + 1 {
        power = power.multiply(&q);
        factorial *= rat(i64::from(2 * k - 1), 1) * rat(i64::from(2 * k), 1);
        let magnitude = power.scale(&(BigRational::one() / (&factorial * rat(i64::from(k), 1))));
        if k == terms + 1 {
            last_magnitude = magnitude;
            break;
        }
        let signed = if k % 2 == 1 {
            magnitude.multiply(&zeta_band)
        } else {
            magnitude.multiply(&zeta_band).neg()
        };
        sum = sum.add(&signed);
    }
    let tail = last_magnitude.abs_upper() * rat(2, 1);
    sum.add(&RatInterval::symmetric(tail)).round_out(BITS)
}

fn modes(arguments: &[String]) -> Result<String, String> {
    let directory = PathBuf::from(
        arguments
            .first()
            .cloned()
            .unwrap_or_else(|| DEFAULT_ARTIFACTS.to_owned()),
    );
    let x_max: u64 = arguments
        .get(1)
        .and_then(|v| v.parse().ok())
        .unwrap_or(1000);
    let workers: usize = arguments
        .get(2)
        .and_then(|v| v.parse().ok())
        .unwrap_or_else(|| {
            thread::available_parallelism()
                .map(|c| c.get())
                .unwrap_or(1)
        });
    let x_min: u64 = arguments.get(3).and_then(|v| v.parse().ok()).unwrap_or(2);
    let started = Instant::now();
    let (zeros, top) = read_zeros(&directory)?;
    let count = zeros.len();
    let widest = zeros
        .iter()
        .map(|z| z.width())
        .max()
        .unwrap_or_else(BigRational::zero);

    // ζ′(ρ) at every zero: read back from the table a previous chunk wrote for the same zeros,
    // else enclosed in parallel and written
    let table_path = format!("{OUTPUT}/zeta-prime-at-the-zeros.tsv");
    let cached: Option<Vec<Mode>> = fs::read_to_string(&table_path).ok().and_then(|text| {
        let mut modes = Vec::new();
        for line in text.lines().skip(1) {
            let fields: Vec<&str> = line.split('\t').collect();
            if fields.len() != 5 {
                return None;
            }
            let parse = |t: &str| t.parse::<BigRational>().ok();
            let gamma = RatInterval::new(parse(fields[0])?, parse(fields[1])?);
            let (re_l, re_u) = fields[2]
                .trim_matches(|c| c == '[' || c == ']')
                .split_once(',')?;
            let (im_l, im_u) = fields[3]
                .trim_matches(|c| c == '[' || c == ']')
                .split_once(',')?;
            modes.push(Mode {
                gamma,
                zeta_prime: ComplexInterval::new(
                    RatInterval::new(parse(re_l)?, parse(re_u)?),
                    RatInterval::new(parse(im_l)?, parse(im_u)?),
                ),
                start: fields[4].parse().ok()?,
            });
        }
        if modes.len() == zeros.len() && modes.iter().zip(zeros.iter()).all(|(m, z)| m.gamma == *z)
        {
            Some(modes)
        } else {
            None
        }
    });
    let zeros = Arc::new(zeros);
    let next = Arc::new(AtomicUsize::new(0));
    let results: Arc<Mutex<Vec<(usize, Result<Mode, String>)>>> = Arc::new(Mutex::new(Vec::new()));
    let mut refused = 0usize;
    let cache_hit = cached.is_some();
    let modes: Vec<Mode> = match cached {
        Some(modes) => modes,
        None => {
            thread::scope(|scope| {
                for _ in 0..workers.max(1) {
                    let zeros = Arc::clone(&zeros);
                    let next = Arc::clone(&next);
                    let results = Arc::clone(&results);
                    scope.spawn(move || {
                        loop {
                            let index = next.fetch_add(1, Ordering::Relaxed);
                            let Some(gamma) = zeros.get(index) else { break };
                            let mode = zeta_prime_enclosure(gamma);
                            results.lock().expect("results").push((index, mode));
                        }
                    });
                }
            });
            let mut results = Arc::try_unwrap(results)
                .map_err(|_| "results")?
                .into_inner()
                .map_err(|_| "results")?;
            results.sort_by_key(|r| r.0);
            let mut modes: Vec<Mode> = Vec::with_capacity(count);
            for (_, r) in results {
                match r {
                    Ok(m) => modes.push(m),
                    Err(e) => {
                        refused += 1;
                        eprintln!("refused: {e}");
                    }
                }
            }
            modes
        }
    };
    let enclosed_at = started.elapsed().as_secs_f64();
    eprintln!(
        "ζ′(ρ) at {} zeros ready at {enclosed_at:.1} s (cache hit: {cache_hit})",
        modes.len()
    );
    let widest_zeta_prime = modes
        .iter()
        .map(|m| {
            let w = m.zeta_prime.re.width();
            let h = m.zeta_prime.im.width();
            if w > h { w } else { h }
        })
        .max()
        .unwrap_or_else(BigRational::zero);
    let max_start = modes.iter().map(|m| m.start).max().unwrap_or(0);
    let mut report = String::new();
    report.push_str(&format!(
        "zeros={count} certified below {top}, widest zero interval {widest}; ζ′(ρ) enclosed at {} zeros ({refused} refused{}), widest component ≤ {} (exact in zeta-prime-at-the-zeros.tsv), largest derived Euler–Maclaurin start {max_start}, enclosure elapsed_s={enclosed_at:.1}\n",
        modes.len(),
        if cache_hit { ", read back from the table" } else { "" },
        dyadic_ceiling(&widest_zeta_prime, 20)
    ));
    // the exact Mertens function up to x_max
    let s = sieve(x_max as usize + 1);
    let mut mertens = vec![0i64; x_max as usize + 2];
    for n in 1..=x_max as usize + 1 {
        mertens[n] = mertens[n - 1] + i64::from(s.mu[n]);
    }

    let cutoffs: Vec<BigRational> = [100i64, 200, 500, 1000]
        .iter()
        .map(|c| rat(*c, 1))
        .filter(|c| *c <= top)
        .collect();
    let modes = Arc::new(modes);
    let points: Vec<u64> = (x_min.max(2)..=x_max).collect();
    let next = Arc::new(AtomicUsize::new(0));
    let rows: Arc<Mutex<Vec<(u64, i64, Vec<RatInterval>)>>> = Arc::new(Mutex::new(Vec::new()));
    thread::scope(|scope| {
        for _ in 0..workers.max(1) {
            let modes = Arc::clone(&modes);
            let next = Arc::clone(&next);
            let rows = Arc::clone(&rows);
            let cutoffs = cutoffs.clone();
            let points = &points;
            let mertens = &mertens;
            scope.spawn(move || {
                loop {
                    let index = next.fetch_add(1, Ordering::Relaxed);
                    let Some(&n) = points.get(index) else { break };
                    // read at x = n + 1/2, where M has no jump
                    let x = rat(2 * n as i64 + 1, 2);
                    let Ok(sums) = mode_sums(&modes, &x, &cutoffs) else {
                        continue;
                    };
                    let trivial = trivial_zero_series(&x);
                    let reconstructions: Vec<RatInterval> = sums
                        .iter()
                        .map(|sum| sum.translate(&rat(-2, 1)).add(&trivial).round_out(BITS))
                        .collect();
                    rows.lock()
                        .expect("rows")
                        .push((n, mertens[n as usize], reconstructions));
                }
            });
        }
    });
    let elapsed = started.elapsed().as_secs_f64();
    let mut rows = Arc::try_unwrap(rows)
        .map_err(|_| "rows")?
        .into_inner()
        .map_err(|_| "rows")?;
    rows.sort_by_key(|r| r.0);
    report.push_str(&format!(
        "x in [{}, {x_max}] workers={workers} elapsed_s={elapsed:.1}\n",
        x_min.max(2)
    ));
    for (ci, cutoff) in cutoffs.iter().enumerate() {
        for (lo, hi) in [(2u64, 100u64), (100, 300), (300, 600), (600, 1000)] {
            if lo > x_max {
                continue;
            }
            let mut worst = BigRational::zero();
            let mut n_rows = 0usize;
            let mut enclosed = 0usize;
            for (n, m, recs) in rows.iter() {
                if *n < lo || *n >= hi.min(x_max + 1) {
                    continue;
                }
                let Some(rec) = recs.get(ci) else { continue };
                let residual = rec.translate(&rat(-*m, 1));
                if residual.contains_zero() {
                    enclosed += 1;
                }
                let bound = residual.abs_upper();
                if bound > worst {
                    worst = bound;
                }
                n_rows += 1;
            }
            if n_rows == 0 {
                continue;
            }
            report.push_str(&format!(
                "cutoff T={cutoff}  x in [{lo},{hi})  rows={n_rows}  max |M − M_T| ≤ {} (= {} exactly)  rows whose interval encloses M: {enclosed}\n",
                dyadic_ceiling(&worst, 6),
                worst
            ));
        }
    }
    // jumps at squarefree n against μ(n), at the top cutoff
    report.push_str("jumps at the top cutoff: M_T(n + ½) − M_T(n − ½) against μ(n), first thirty squarefree n\n");
    let top_index = cutoffs.len().saturating_sub(1);
    let mut shown = 0;
    let mut sign_agreements = 0usize;
    let mut sign_open = 0usize;
    for (n, _, recs) in rows.iter() {
        if s.mu[*n as usize] == 0 {
            continue;
        }
        let Some(after) = recs.get(top_index) else {
            continue;
        };
        let Some((_, _, before_recs)) = rows.iter().find(|r| r.0 + 1 == *n) else {
            continue;
        };
        let Some(before) = before_recs.get(top_index) else {
            continue;
        };
        let jump = after.subtract(before);
        let mu = i64::from(s.mu[*n as usize]);
        let agrees = if jump.contains_zero() {
            sign_open += 1;
            "open"
        } else if (jump.lower.is_positive() && mu > 0) || (jump.upper.is_negative() && mu < 0) {
            sign_agreements += 1;
            "polarity agrees"
        } else {
            "polarity DISAGREES"
        };
        if shown < 30 {
            report.push_str(&format!(
                "  n={n:>4} {:<14} μ={mu:>2}  jump ∈ {}  {agrees}\n",
                simplex_symbol(*n),
                dyadic_interval(&jump, 8)
            ));
            shown += 1;
        }
    }
    report.push_str(&format!(
        "polarity at squarefree n in range: agrees {sign_agreements}, open {sign_open}\n"
    ));
    fs::create_dir_all(OUTPUT).map_err(|e| e.to_string())?;
    let range = format!("{:05}-{:05}", x_min.max(2), x_max);
    let mut table = String::from("n\tM(n)\t");
    for c in &cutoffs {
        table.push_str(&format!("M_T_at_n_plus_half_T={c}\t"));
    }
    table.push('\n');
    for (n, m, recs) in rows.iter() {
        table.push_str(&format!("{n}\t{m}\t"));
        for r in recs {
            table.push_str(&format!("{r}\t"));
        }
        table.push('\n');
    }
    fs::write(format!("{OUTPUT}/modes-{range}.tsv"), table).map_err(|e| e.to_string())?;
    let mut modes_table = String::from(
        "gamma_lower\tgamma_upper\tzeta_prime_re\tzeta_prime_im\teuler_maclaurin_start\n",
    );
    for m in modes.iter() {
        modes_table.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\n",
            m.gamma.lower, m.gamma.upper, m.zeta_prime.re, m.zeta_prime.im, m.start
        ));
    }
    if !cache_hit {
        fs::write(&table_path, modes_table).map_err(|e| e.to_string())?;
    }
    fs::write(format!("{OUTPUT}/receipt-modes-{range}.txt"), &report).map_err(|e| e.to_string())?;
    Ok(report)
}

fn main() -> Result<(), String> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    fs::create_dir_all(OUTPUT).map_err(|e| e.to_string())?;
    match arguments.first().map(String::as_str) {
        Some("combinatorics") => {
            let n_max: usize = arguments
                .get(1)
                .and_then(|v| v.parse().ok())
                .unwrap_or(10_000_000);
            let report = combinatorics(n_max)?;
            print!("{report}");
            fs::write(format!("{OUTPUT}/receipt-combinatorics.txt"), &report)
                .map_err(|e| e.to_string())?;
            println!("artifact={OUTPUT}/receipt-combinatorics.txt");
        }
        Some("modes") => {
            let report = modes(&arguments[1..])?;
            print!("{report}");
            println!("artifact={OUTPUT}/receipt-modes-*.txt");
        }
        _ => {
            return Err(
                "usage: combinatorics [N_max] | modes [artifact directory] [x_max] [workers] [x_min]"
                    .to_owned(),
            );
        }
    }
    Ok(())
}
