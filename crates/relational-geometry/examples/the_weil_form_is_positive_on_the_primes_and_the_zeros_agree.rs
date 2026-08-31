//! The Weil form is computed from the primes and its positivity is the Riemann hypothesis.
//!
//! Weil's criterion: with `ρ = ½ + iγ` over the nontrivial zeros, `g` a real even test function
//! and `ĝ(t) = ∫ g(x) e^{itx} dx`,
//!
//! ```text
//!     W(g₁, g₂) = Σ_ρ ĝ₁(γ) ĝ₂(γ)
//! ```
//!
//! is a symmetric pairing whose diagonal `W(g, g) = Σ_ρ |ĝ(γ)|²` is manifestly non-negative when
//! every `γ` is real — and RH is equivalent to `W(g, g) ≥ 0` for every `g`. **The explicit formula
//! computes `W` from the primes without knowing a single zero.** With `h = g₁ ⋆ g₂` (so `ĥ = ĝ₁ĝ₂`)
//! and `Φ(s) = ∫ h(x) e^{(s−½)x} dx`,
//!
//! ```text
//!     Σ_ρ Φ(ρ) = Φ(0) + Φ(1) − 2 Σ_n Λ(n) n^{−1/2} h(log n) − h(0)(log π + γ_E)
//!                + 2 ∫₀^∞ [e^{−2x} h(0) − e^{−x/2} h(x)] / (1 − e^{−2x}) dx,
//! ```
//!
//! derived from `ξ′/ξ(s) = 1/s + 1/(s−1) − ½ log π + ½ ψ(s/2) + ζ′/ζ(s)` and the integral
//! representation `ψ(z) = −γ_E + ∫₀^∞ (e^{−u} − e^{−zu})/(1 − e^{−u}) du`. For the family
//! `g_a = 1_{[−a, a]}` with rational `a`, `h` is the trapezoid `min(2a₁, 2a₂, a₁ + a₂ − |x|)⁺`,
//! `Φ(0) + Φ(1) = 32 sinh(a₁/2) sinh(a₂/2)`, the prime sum is finite (`n ≤ e^{a₁+a₂}`), the
//! archimedean integral is enclosed on a dyadic grid with the removable singularity at `0` bounded
//! by hand, and `γ_E` is an Euler–Maclaurin series with its remainder. **Every term is an exact
//! rational interval.**
//!
//! The return is the Gram matrix of `W` on the family, its exact elimination — every pivot an
//! interval whose sign is decided or returned `open` — and, as the check that the constants are
//! right, the spectral side `2 Σ_{0<γ<T} 4 sin(a₁γ) sin(a₂γ)/γ²` from the certified zeros with a
//! tail bounded through `N(t) ≤ (t/2π) log(t/2π) + 3 log t` (Trudgian 2014, `t ≥ 100`): the two
//! sides must intersect entry by entry. The smallest pivot is the form's gap on the family.
//!
//! Usage: `[artifact directory] [arithmetic] [half-widths as rationals, e.g. 1/2 1 3/2 2 5/2 3 7/2 4]`;
//! `arithmetic` skips the spectral cross-check (already established entry by entry on the
//! families that fit beside it under the process aperture).

use std::env;
use std::fs;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Instant;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use relational_geometry::{
    EtaRatioAtlas, RatInterval, cis_interval, exp_rational_interval, log_integer_interval,
    log_rational_interval, pi_interval,
};

const DEFAULT_ARTIFACTS: &str =
    "output/the_card_returns_the_eta_boundary_and_the_zero_is_a_winding";
const OUTPUT: &str = "output/the_weil_form_is_positive_on_the_primes_and_the_zeros_agree";
const BITS: u32 = 64;
const TERMS: u32 = 20;
/// The grid: `2^-FINE_BITS` cells on `[2^-FINE_BITS, 1/8]`; beyond `1/8` the integral is a series.
const FINE_BITS: u32 = 16;

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

fn dyadic_ceiling(value: &BigRational, bits: u32) -> String {
    let scale = BigInt::one() << bits as usize;
    let k = (value * BigRational::from_integer(scale.clone()))
        .ceil()
        .to_integer();
    format!("{}", BigRational::new(k, scale))
}

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

/// `⌊√v⌋` by Newton's iteration on integers.
fn integer_sqrt(v: &BigInt) -> BigInt {
    if v.is_zero() {
        return BigInt::zero();
    }
    let mut x = BigInt::one() << ((v.bits() + 1) / 2) as usize;
    loop {
        let y = (&x + v / &x) >> 1usize;
        if y >= x {
            return x;
        }
        x = y;
    }
}

/// `n^{-1/2}` from the integer square root at `2^64` scale.
fn inverse_root(n: u64) -> RatInterval {
    let scale = BigInt::one() << 64usize;
    let scaled = BigInt::from(n) * &scale * &scale;
    let s = integer_sqrt(&scaled);
    // s ≤ √n·2^64 < s + 1
    RatInterval::new(
        BigRational::new(scale.clone(), &s + BigInt::one()),
        BigRational::new(scale, s),
    )
}

/// Euler's constant by Euler–Maclaurin at `N = 32` with ten Bernoulli terms and the first omitted
/// term as the remainder radius.
fn euler_constant() -> RatInterval {
    let n = 32i64;
    let mut harmonic = BigRational::zero();
    for k in 1..=n {
        harmonic += rat(1, k);
    }
    let log_n = log_integer_interval(n as u32, TERMS + 8, BITS).unwrap();
    // Bernoulli numbers B_0..B_24 by the recurrence Σ_{k≤m} C(m+1,k) B_k = 0
    let mut bernoulli: Vec<BigRational> = vec![BigRational::one()];
    for m in 1..=24usize {
        let mut sum = BigRational::zero();
        let mut binom = BigRational::one();
        for (k, b) in bernoulli.iter().enumerate() {
            // C(m+1, k)
            if k > 0 {
                binom = binom * rat((m + 2 - k) as i64, 1) / rat(k as i64, 1);
            }
            sum += &binom * b;
        }
        // B_m = −(Σ_{k<m} C(m+1, k) B_k) / C(m+1, m), C(m+1, m) = m + 1
        bernoulli.push(-sum / rat((m + 1) as i64, 1));
    }
    let mut value = harmonic - rat(1, 2 * n);
    let mut n_power = BigRational::one();
    for k in 1..=10usize {
        n_power *= rat(n * n, 1);
        value += &bernoulli[2 * k] / (rat(2 * k as i64, 1) * &n_power);
    }
    n_power *= rat(n * n, 1);
    let remainder = (&bernoulli[22] / (rat(22, 1) * n_power)).abs();
    let gamma = RatInterval::new(value.clone(), value)
        .subtract(&log_n)
        .add(&RatInterval::symmetric(remainder))
        .round_out(BITS);
    // exterior control: the published digits 0.57721566490153286060 must lie inside
    let published = BigRational::new(
        "57721566490153286060".parse::<BigInt>().unwrap(),
        "100000000000000000000".parse::<BigInt>().unwrap(),
    );
    assert!(
        gamma.lower <= published && published <= gamma.upper,
        "Euler's constant enclosure {gamma} excludes the published value"
    );
    gamma
}

/// Prime powers `n ≤ n_max` with their prime, by a smallest-prime-factor sieve.
fn prime_powers_to(n_max: u64) -> Vec<(u64, u64)> {
    let n = n_max as usize;
    let mut spf = vec![0u32; n + 1];
    for i in 2..=n {
        if spf[i] == 0 {
            let mut m = i;
            while m <= n {
                if spf[m] == 0 {
                    spf[m] = i as u32;
                }
                m += i;
            }
        }
    }
    let mut out = Vec::new();
    for m in 2..=n {
        let p = spf[m] as usize;
        let mut q = m;
        while q % p == 0 {
            q /= p;
        }
        if q == 1 {
            out.push((m as u64, p as u64));
        }
    }
    out
}

/// The trapezoid `h = 1_{[−a₁,a₁]} ⋆ 1_{[−a₂,a₂]}` at `x ≥ 0`: even and non-increasing.
fn trapezoid(a1: &BigRational, a2: &BigRational, x: &BigRational) -> BigRational {
    let width = a1 + a2;
    let plateau = if a1 < a2 {
        a1 * rat(2, 1)
    } else {
        a2 * rat(2, 1)
    };
    if *x >= width {
        BigRational::zero()
    } else {
        let slope = &width - x;
        if slope < plateau { slope } else { plateau }
    }
}

/// `h` over `[x_lo, x_hi]`, `0 ≤ x_lo`: `[h(x_hi), h(x_lo)]` by monotonicity.
fn trapezoid_over(
    a1: &BigRational,
    a2: &BigRational,
    x_lo: &BigRational,
    x_hi: &BigRational,
) -> RatInterval {
    RatInterval::new(trapezoid(a1, a2, x_hi), trapezoid(a1, a2, x_lo))
}

struct Grid {
    /// grid points `x_k` on `[0, 1/8]` with `u(x_k)` and `v(x_k)`, where
    /// `u(x) = (e^{−x/2} − e^{−2x})/(1 − e^{−2x})` (decreasing, `u(0) = 3/4`) and
    /// `v(x) = x e^{−x/2}/(1 − e^{−2x})` (increasing on `[0, 1/8]`, `v(0) = 1/2`)
    points: Vec<(BigRational, RatInterval, RatInterval)>,
}

/// `u` is decreasing on `(0, ∞)`: `u = (e^{3x/2} − 1)/(e^{2x} − 1)` and
/// `d/dx log u = 3/(2(1 − e^{−3x/2})) − 2/(1 − e^{−2x}) < 0` because `c/(1 − e^{−cx})` increases in
/// `c`. `v` is increasing on `[0, 1/8]`: `sign v′ = sign ψ`, `ψ = e^{x/2}(1 − x/2) − e^{−3x/2}(1 + 3x/2)`,
/// `ψ(0) = 0`, `ψ′ = (x/4)(9e^{−3x/2} − e^{x/2}) > 0` for `x < (log 9)/2`.
fn grid() -> Grid {
    let fine = rat(1, 1 << FINE_BITS);
    let eighth = rat(1, 8);
    let mut points: Vec<(BigRational, RatInterval, RatInterval)> = vec![(
        BigRational::zero(),
        RatInterval::point(rat(3, 4)),
        RatInterval::point(rat(1, 2)),
    )];
    let mut x = fine.clone();
    while x <= eighth {
        let half = exp_rational_interval(&(-&x / rat(2, 1)), TERMS, BITS);
        let two = half.square().square().round_out(BITS);
        let one_minus_two = RatInterval::new(
            BigRational::one() - &two.upper,
            BigRational::one() - &two.lower,
        );
        let u = half
            .subtract(&two)
            .divide(&one_minus_two)
            .expect("x > 0")
            .round_out(BITS);
        let v = half
            .scale(&x)
            .divide(&one_minus_two)
            .expect("x > 0")
            .round_out(BITS);
        points.push((x.clone(), u, v));
        x += &fine;
    }
    Grid { points }
}

/// `∫_p^q (c + m x) e^{−λx} dx = G(p) − G(q)`, `G(x) = ((c + m x)/λ + m/λ²) e^{−λx}`, with the
/// exponentials supplied as intervals.
fn linear_exponential_piece(
    c: &BigRational,
    m: &BigRational,
    lambda: &BigRational,
    p: &BigRational,
    e_p: &RatInterval,
    q: &BigRational,
    e_q: &RatInterval,
) -> RatInterval {
    let g = |x: &BigRational, e: &RatInterval| -> RatInterval {
        let coefficient = (c + m * x) / lambda + m / (lambda * lambda);
        e.scale(&coefficient)
    };
    g(p, e_p).subtract(&g(q, e_q))
}

/// `2 ∫₀^∞ [e^{−2x} h(0) − e^{−x/2} h(x)] / (1 − e^{−2x}) dx` for the pair `(a₁, a₂)`:
/// a `2^-FINE_BITS` monotone-endpoint enclosure on `[0, 1/8]`, the geometric expansion `1/(1 − e^{−2x}) = Σ_{k<K} e^{−2kx} + e^{−2Kx}/(1 − e^{−2x})`
/// on `[1/8, X]` with every term a closed-form exponential integral and the remainder bounded
/// by `10 h(0) e^{−K/4}/K`, and the closed-form tail beyond `X = ⌈2 max a⌉`.
fn archimedean_integral(
    grid: &Grid,
    x_max_int: i64,
    a1: &BigRational,
    a2: &BigRational,
) -> RatInterval {
    let h0 = trapezoid(a1, a2, &BigRational::zero());
    let width = a1 + a2;
    let plateau_end = (a1 - a2).abs();
    // --- [0, 1/8] on the fine grid: F = −2h0·u + 2·[a₁ = a₂]·v is increasing, so each cell is
    // enclosed by its endpoint values and the enclosure widths telescope to w·(F(1/8) − F(0))
    let same = a1 == a2;
    // F/2 = −h0·u + [a₁ = a₂]·v; the factor 2 is applied once, at the end, with the series part
    let f_at = |u: &RatInterval, v: &RatInterval| -> RatInterval {
        let base = u.scale(&(-&h0));
        if same { base.add(v) } else { base }
    };
    let mut total = RatInterval::point(BigRational::zero());
    let mut previous = &grid.points[0];
    for point in grid.points.iter().skip(1) {
        let (x_lo, u_lo, v_lo) = previous;
        let (x_hi, u_hi, v_hi) = point;
        let cell = f_at(u_lo, v_lo)
            .hull(&f_at(u_hi, v_hi))
            .scale(&(x_hi - x_lo));
        total = total.add(&cell).round_out(BITS);
        previous = point;
    }
    // --- [1/8, X] by the geometric expansion
    let eighth = rat(1, 8);
    let x_max = rat(x_max_int, 1);
    // pieces of h on [1/8, X]: plateau (c = h0, m = 0) on [1/8, plateau_end], slope
    // (c = width, m = −1) on [max(1/8, plateau_end), width]
    let mut pieces: Vec<(BigRational, BigRational, BigRational, BigRational)> = Vec::new();
    if plateau_end > eighth {
        pieces.push((
            h0.clone(),
            BigRational::zero(),
            eighth.clone(),
            plateau_end.clone(),
        ));
    }
    let slope_start = if plateau_end > eighth {
        plateau_end.clone()
    } else {
        eighth.clone()
    };
    if width > slope_start {
        pieces.push((
            width.clone(),
            -BigRational::one(),
            slope_start,
            width.clone(),
        ));
    }
    let k_terms: usize = 64;
    // exponentials at the breakpoints: e^{−2b} and e^{−b/2}, raised to powers as k runs
    let breakpoints: Vec<BigRational> = {
        let mut b = vec![eighth.clone(), x_max.clone()];
        for (_, _, p, q) in &pieces {
            b.push(p.clone());
            b.push(q.clone());
        }
        b.sort();
        b.dedup();
        b
    };
    let base: Vec<(RatInterval, RatInterval)> = breakpoints
        .iter()
        .map(|b| {
            let half = exp_rational_interval(&(-b / rat(2, 1)), TERMS, BITS);
            let two = half.square().square().round_out(BITS);
            (two, half)
        })
        .collect();
    let index_of = |b: &BigRational| breakpoints.iter().position(|x| x == b).unwrap();
    let mut two_power: Vec<RatInterval> = base.iter().map(|(two, _)| two.clone()).collect(); // e^{−(2k+2)b} at k = 0
    let mut half_power: Vec<RatInterval> = base.iter().map(|(_, half)| half.clone()).collect(); // e^{−(2k+1/2)b} at k = 0
    let mut series = RatInterval::point(BigRational::zero());
    for k in 0..k_terms {
        let lambda_two = rat(2 * k as i64 + 2, 1);
        let lambda_half = rat(4 * k as i64 + 1, 2);
        // h0 ∫_{1/8}^{X} e^{−(2k+2)x} dx
        let i0 = index_of(&eighth);
        let ix = index_of(&x_max);
        let plateau_term = linear_exponential_piece(
            &h0,
            &BigRational::zero(),
            &lambda_two,
            &eighth,
            &two_power[i0],
            &x_max,
            &two_power[ix],
        );
        let mut term = plateau_term;
        for (c, m, p, q) in &pieces {
            let ip = index_of(p);
            let iq = index_of(q);
            let piece = linear_exponential_piece(
                c,
                m,
                &lambda_half,
                p,
                &half_power[ip],
                q,
                &half_power[iq],
            );
            term = term.subtract(&piece);
        }
        series = series.add(&term).round_out(BITS);
        for (i, (two, _)) in base.iter().enumerate() {
            two_power[i] = two_power[i].multiply(two).round_out(BITS);
            half_power[i] = half_power[i].multiply(two).round_out(BITS);
        }
    }
    // remainder: |2 ∫ bracket · e^{−2Kx}/(1−e^{−2x})| ≤ 10 h0 e^{−K/4} / K on [1/8, ∞)
    let e_k = exp_rational_interval(&rat(-(k_terms as i64), 4), TERMS, BITS);
    let remainder = rat(10, k_terms as i64) * &h0 * e_k.upper;
    total = total
        .add(&series)
        .add(&RatInterval::symmetric(remainder))
        .round_out(BITS);
    // beyond X: h = 0 and ∫_X^∞ 2e^{−2x}/(1−e^{−2x}) dx = −log(1 − e^{−2X})
    let e_2x = exp_rational_interval(&rat(-2 * x_max_int, 1), TERMS, BITS);
    let one_minus = RatInterval::new(
        BigRational::one() - &e_2x.upper,
        BigRational::one() - &e_2x.lower,
    );
    let log_tail = RatInterval::new(
        log_rational_interval(&one_minus.lower, TERMS + 8, BITS)
            .unwrap()
            .lower,
        log_rational_interval(&one_minus.upper, TERMS + 8, BITS)
            .unwrap()
            .upper,
    );
    total
        .scale(&rat(2, 1))
        .subtract(&log_tail.scale(&h0))
        .round_out(BITS)
}

/// Whether the leading `size × size` block of `a − εI` is positive definite, by exact rational
/// symmetric elimination: every pivot strictly positive.
fn exact_positive_definite(a: &[Vec<BigRational>], size: usize, epsilon: &BigRational) -> bool {
    let mut w: Vec<Vec<BigRational>> = (0..size)
        .map(|i| {
            (0..size)
                .map(|j| {
                    if i == j {
                        &a[i][j] - epsilon
                    } else {
                        a[i][j].clone()
                    }
                })
                .collect()
        })
        .collect();
    for k in 0..size {
        let pivot = w[k][k].clone();
        if !pivot.is_positive() {
            return false;
        }
        for i in (k + 1)..size {
            let factor = &w[i][k] / &pivot;
            if factor.is_zero() {
                continue;
            }
            for j in (k + 1)..size {
                let update = &factor * &w[k][j];
                w[i][j] -= update;
            }
        }
    }
    true
}

fn sinh_point(u: &BigRational) -> RatInterval {
    let plus = exp_rational_interval(u, TERMS, BITS);
    let minus = exp_rational_interval(&(-u), TERMS, BITS);
    plus.subtract(&minus).scale(&rat(1, 2))
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

/// `2 Σ_{γ>T} 4/γ²` bounded through `N(t) ≤ (t/2π) log(t/2π) + 3 log t`:
/// `≤ 2·[(4/π)(log(T/2π) + 1)/T + 6(2 log T + 1)/T²]`.
fn spectral_tail(top: &BigRational) -> BigRational {
    let pi = pi_interval(BITS);
    let t_over_2pi = RatInterval::point(top.clone())
        .divide(&pi.scale(&rat(2, 1)))
        .unwrap();
    let log_t_2pi = log_rational_interval(&t_over_2pi.upper, TERMS + 8, BITS).unwrap();
    let log_t = log_rational_interval(top, TERMS + 8, BITS).unwrap();
    let first = (log_t_2pi.upper + BigRational::one()) * rat(4, 1) / &pi.lower / top;
    let second = (log_t.upper * rat(2, 1) + BigRational::one()) * rat(6, 1) / (top * top);
    (first + second) * rat(2, 1)
}

fn main() -> Result<(), String> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    let directory = PathBuf::from(
        arguments
            .first()
            .cloned()
            .unwrap_or_else(|| DEFAULT_ARTIFACTS.to_owned()),
    );
    let spectral_requested = arguments.get(1).map(String::as_str) != Some("arithmetic");
    let rest_start = if spectral_requested { 1 } else { 2 };
    let half_widths: Vec<BigRational> = if arguments.len() > rest_start {
        arguments[rest_start..]
            .iter()
            .map(|a| a.parse::<BigRational>().map_err(|e| format!("{a}: {e}")))
            .collect::<Result<_, _>>()?
    } else {
        (1..=8).map(|k| rat(k, 2)).collect()
    };
    let m = half_widths.len();
    // the series region ends at X = ⌈2·max a⌉, beyond which h vanishes
    let x_max: i64 = (half_widths.iter().max().unwrap() * rat(2, 1))
        .ceil()
        .to_integer()
        .to_string()
        .parse()
        .unwrap();
    let started = Instant::now();
    fs::create_dir_all(OUTPUT).map_err(|e| e.to_string())?;

    // shared exact constants
    let gamma_e = euler_constant();
    let log_pi = {
        let pi = pi_interval(BITS);
        RatInterval::new(
            log_rational_interval(&pi.lower, TERMS + 8, BITS)
                .unwrap()
                .lower,
            log_rational_interval(&pi.upper, TERMS + 8, BITS)
                .unwrap()
                .upper,
        )
    };
    let constant = log_pi.add(&gamma_e);
    let grid = grid();
    let grid_at = started.elapsed().as_secs_f64();

    // prime powers up to e^{2·max a}: Λ(n), n^{−1/2}, log n
    let largest = half_widths.iter().max().unwrap() * rat(2, 1);
    let bound = exp_rational_interval(&largest, TERMS, BITS)
        .upper
        .ceil()
        .to_integer();
    let n_max: u64 = bound.to_string().parse().unwrap();
    let mut prime_powers: Vec<(u64, RatInterval, RatInterval, RatInterval)> = Vec::new();
    for (n, p) in prime_powers_to(n_max) {
        let lambda = log_integer_interval(p as u32, TERMS + 8, BITS).map_err(|e| e.to_string())?;
        let log_n = log_integer_interval(n as u32, TERMS + 8, BITS).map_err(|e| e.to_string())?;
        prime_powers.push((n, lambda, inverse_root(n), log_n));
    }
    let primes_at = started.elapsed().as_secs_f64();

    // the arithmetic Gram, pairs in parallel
    let pairs: Vec<(usize, usize)> = (0..m).flat_map(|i| (i..m).map(move |j| (i, j))).collect();
    let entries: Arc<
        Mutex<
            Vec<(
                (usize, usize),
                RatInterval,
                RatInterval,
                RatInterval,
                RatInterval,
            )>,
        >,
    > = Arc::new(Mutex::new(Vec::new()));
    let next = Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let workers = thread::available_parallelism()
        .map(|c| c.get())
        .unwrap_or(1)
        .min(pairs.len().max(1));
    thread::scope(|scope| {
        for _ in 0..workers {
            let entries = Arc::clone(&entries);
            let next = Arc::clone(&next);
            let pairs = &pairs;
            let half_widths = &half_widths;
            let grid = &grid;
            let x_max = x_max;
            let prime_powers = &prime_powers;
            let constant = &constant;
            scope.spawn(move || {
                loop {
                    let index = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    let Some(&(i, j)) = pairs.get(index) else {
                        break;
                    };
                    let (a1, a2) = (&half_widths[i], &half_widths[j]);
                    // Φ(0) + Φ(1) = 32 sinh(a₁/2) sinh(a₂/2)
                    let boundary = sinh_point(&(a1 / rat(2, 1)))
                        .multiply(&sinh_point(&(a2 / rat(2, 1))))
                        .scale(&rat(32, 1));
                    // 2 Σ Λ(n) n^{−1/2} h(log n)
                    let mut primes = RatInterval::point(BigRational::zero());
                    let support = a1 + a2;
                    for (_, lambda, root, log_n) in prime_powers.iter() {
                        if log_n.lower >= support {
                            break;
                        }
                        let h = trapezoid_over(a1, a2, &log_n.lower, &log_n.upper);
                        if h.upper.is_zero() {
                            continue;
                        }
                        primes = primes
                            .add(&lambda.multiply(root).multiply(&h))
                            .round_out(BITS);
                    }
                    let primes = primes.scale(&rat(2, 1));
                    let h0 = trapezoid(a1, a2, &BigRational::zero());
                    let gamma_term = constant.scale(&h0);
                    let integral = archimedean_integral(grid, x_max, a1, a2);
                    let w = boundary
                        .subtract(&primes)
                        .subtract(&gamma_term)
                        .add(&integral)
                        .round_out(BITS);
                    entries
                        .lock()
                        .unwrap()
                        .push(((i, j), w, boundary, primes, integral));
                }
            });
        }
    });
    let entries = Arc::try_unwrap(entries)
        .map_err(|_| "entries")?
        .into_inner()
        .unwrap();
    let mut gram: Vec<Vec<RatInterval>> = vec![vec![RatInterval::point(BigRational::zero()); m]; m];
    let mut parts: Vec<((usize, usize), RatInterval, RatInterval, RatInterval)> = Vec::new();
    for ((i, j), w, boundary, primes, integral) in entries {
        gram[i][j] = w.clone();
        gram[j][i] = w;
        parts.push(((i, j), boundary, primes, integral));
    }
    parts.sort_by_key(|p| p.0);
    let arithmetic_at = started.elapsed().as_secs_f64();

    // the spectral side from the certified zeros
    let (zeros, top) = if spectral_requested {
        read_zeros(&directory)?
    } else {
        (Vec::new(), BigRational::zero())
    };
    let tail = if spectral_requested {
        spectral_tail(&top)
    } else {
        BigRational::zero()
    };
    let mut spectral: Vec<Vec<RatInterval>> =
        vec![vec![RatInterval::point(BigRational::zero()); m]; m];
    // sin(a γ) for every a and γ
    let sines: Vec<Vec<RatInterval>> = half_widths
        .iter()
        .map(|a| {
            zeros
                .iter()
                .map(|g| cis_interval(&g.scale(a), TERMS, BITS).im)
                .collect()
        })
        .collect();
    for i in 0..m {
        for j in i..m {
            let mut sum = RatInterval::point(BigRational::zero());
            for (k, g) in zeros.iter().enumerate() {
                let term = sines[i][k]
                    .multiply(&sines[j][k])
                    .divide(&g.square())
                    .unwrap()
                    .scale(&rat(8, 1)); // 2 (±γ) × 4 sin sin / γ²
                sum = sum.add(&term).round_out(BITS);
            }
            let tail_interval = if i == j {
                RatInterval::new(BigRational::zero(), tail.clone())
            } else {
                RatInterval::symmetric(tail.clone())
            };
            let s = sum.add(&tail_interval).round_out(BITS);
            spectral[i][j] = s.clone();
            spectral[j][i] = s;
        }
    }
    let spectral_at = started.elapsed().as_secs_f64();

    // the least eigenvalue of the arithmetic Gram on every nested prefix family, exactly:
    // λ_min(W_mid) by rational bisection on the exact LDLᵀ pivots of W_mid − εI, and
    // λ_min(W) ∈ [λ_min(W_mid) − δ, λ_min(W_mid) + δ] with δ the largest row sum of half-widths (Weyl)
    let midpoint: Vec<Vec<BigRational>> = gram
        .iter()
        .map(|row| row.iter().map(|w| w.midpoint()).collect())
        .collect();
    let half_widths_matrix: Vec<Vec<BigRational>> = gram
        .iter()
        .map(|row| row.iter().map(|w| w.width() / rat(2, 1)).collect())
        .collect();
    let mut gaps: Vec<(usize, RatInterval)> = Vec::new();
    for size in 1..=m {
        let delta = (0..size)
            .map(|i| {
                (0..size)
                    .map(|j| half_widths_matrix[i][j].clone())
                    .sum::<BigRational>()
            })
            .max()
            .unwrap();
        let mut lo = BigRational::zero();
        let mut hi = (0..size).map(|i| midpoint[i][i].clone()).max().unwrap();
        if !exact_positive_definite(&midpoint, size, &lo) {
            // not PD at ε = 0: bisect downward to the least eigenvalue
            lo = -hi.clone();
            hi = BigRational::zero();
        }
        for _ in 0..24 {
            let mid = (&lo + &hi) / rat(2, 1);
            if exact_positive_definite(&midpoint, size, &mid) {
                lo = mid;
            } else {
                hi = mid;
            }
        }
        gaps.push((
            size,
            RatInterval::new(&lo - &delta, &hi + &delta).round_out(BITS),
        ));
    }
    let eigen_at = started.elapsed().as_secs_f64();

    let mut report = String::new();
    report.push_str(&format!(
        "family: g_a = 1_[−a,a] with a ∈ {{{}}}; prime powers to {n_max}; grid {} points; γ_E ∈ {}; zeros {} certified below {top}, spectral tail ≤ {}\n",
        half_widths.iter().map(|a| a.to_string()).collect::<Vec<_>>().join(", "),
        grid.points.len(),
        dyadic_interval(&gamma_e, 40),
        zeros.len(),
        dyadic_ceiling(&tail, 16)
    ));
    report.push_str("\npair\tW from the primes (arithmetic side)\tW from the zeros (spectral side, tail included)\tintersect\tΦ(0)+Φ(1)\t2ΣΛ(n)n^{-1/2}h(log n)\tarchimedean\n");
    let mut disjoint = 0usize;
    for ((i, j), boundary, primes, integral) in &parts {
        let w = &gram[*i][*j];
        let s = &spectral[*i][*j];
        let meets = w.lower <= s.upper && s.lower <= w.upper;
        if !meets {
            disjoint += 1;
        }
        report.push_str(&format!(
            "({}, {})\t{}\t{}\t{}\t{}\t{}\t{}\n",
            half_widths[*i],
            half_widths[*j],
            dyadic_interval(w, 12),
            dyadic_interval(s, 12),
            if meets { "yes" } else { "NO" },
            dyadic_interval(boundary, 12),
            dyadic_interval(primes, 12),
            dyadic_interval(integral, 12)
        ));
    }
    if spectral_requested {
        report.push_str(&format!(
            "\nexplicit-formula check: {} of {} entries intersect ({} disjoint)\n",
            parts.len() - disjoint,
            parts.len(),
            disjoint
        ));
    } else {
        report.push_str("\nspectral side not computed on this run (arithmetic only)\n");
    }
    report.push_str("least eigenvalue of the arithmetic Gram on each nested prefix family (support 2a_max), exact bisection ± Weyl half-width bound:\n");
    let mut widest_entry = BigRational::zero();
    for row in &gram {
        for w in row {
            if w.width() > widest_entry {
                widest_entry = w.width();
            }
        }
    }
    for (size, gap) in &gaps {
        report.push_str(&format!(
            "  members {size:>2} (a ≤ {}): λ_min ∈ {}  {}\n",
            half_widths[size - 1],
            dyadic_interval(gap, 16),
            if gap.lower.is_positive() {
                "positive definite"
            } else if gap.upper.is_negative() {
                if spectral_requested && disjoint == 0 {
                    "NEGATIVE with the zeros agreeing entry by entry — a counterexample to positivity"
                } else if spectral_requested {
                    "negative, but the arithmetic side disagrees with the zeros: the implementation is refuted, not positivity"
                } else {
                    "negative on the arithmetic side (no spectral check on this run — not a counterexample until the zeros agree)"
                }
            } else {
                "open"
            }
        ));
    }
    report.push_str(&format!(
        "widest Gram entry: {}\n",
        dyadic_ceiling(&widest_entry, 20)
    ));
    report.push_str(&format!(
        "elapsed_s: grid {grid_at:.1}, primes {primes_at:.1}, arithmetic Gram {arithmetic_at:.1}, spectral Gram {spectral_at:.1}, eigenvalues {eigen_at:.1}\n"
    ));
    print!("{report}");
    let family_name = format!(
        "{}-members-to-{}",
        m,
        half_widths
            .iter()
            .max()
            .unwrap()
            .to_string()
            .replace('/', "over")
    );
    fs::write(format!("{OUTPUT}/receipt-{family_name}.txt"), &report).map_err(|e| e.to_string())?;
    let mut table = String::from(
        "i\tj\ta_i\ta_j\tW_arithmetic_lower\tW_arithmetic_upper\tW_spectral_lower\tW_spectral_upper\n",
    );
    for i in 0..m {
        for j in 0..m {
            table.push_str(&format!(
                "{i}\t{j}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                half_widths[i],
                half_widths[j],
                gram[i][j].lower,
                gram[i][j].upper,
                spectral[i][j].lower,
                spectral[i][j].upper
            ));
        }
    }
    fs::write(format!("{OUTPUT}/gram-{family_name}.tsv"), table).map_err(|e| e.to_string())?;
    println!("artifact={OUTPUT}/receipt-{family_name}.txt");
    Ok(())
}
