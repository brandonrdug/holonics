//! The primes, heard through the zeros: the explicit formula run backwards on certified vortices.
//!
//! The zeros are the receptors and the primes are the impulses they read; the explicit formula is
//! the transduction. Run it the other way and the receptors *reconstruct the impulses*:
//!
//! ```text
//!     ψ(x) = x − Σ_ρ x^ρ/ρ − log 2π − ½ log(1 − x^{−2}),        ψ(x) = Σ_{p^k ≤ x} log p
//! ```
//!
//! Each certified zero `ρ = 1/2 + iγ` contributes one spiral mode `x^{1/2} e^{iγ log x}/ρ`, and
//! the pair `ρ, ρ̄` contributes `2 x^{1/2} [½ cos(γ log x) + γ sin(γ log x)] / (¼ + γ²)`. With
//! the zeros below a height `T` the reconstruction carries the tail of every zero above `T`; that
//! tail is what the residual `ψ(x) − ψ_T(x)` measures, and it must fall as `T` rises if the array
//! is passive. Every ordinate enters as its certified interval, every logarithm and turn as an
//! exact enclosure, so the reconstruction is an interval that contains the truncated sum.
//!
//! The reading is taken at half-integers, where `ψ` has no jump, and the jumps themselves are
//! read as `ψ_T(p + ½) − ψ_T(p − ½)` against `log p`.
//!
//! Usage: `... -- [artifact directory] [x_max] [workers] [x_min]`; each run writes
//! `receipt-<x_min>-<x_max>.txt` and `reconstruction-<x_min>-<x_max>.tsv`, so a range wider than
//! the process aperture is sectioned into runs that compose.

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
    EtaRatioAtlas, RatInterval, cis_interval, exp_interval, log_integer_interval,
    log_rational_interval, pi_interval,
};

const DEFAULT_ARTIFACTS: &str =
    ".local/artifacts/the_card_returns_the_eta_boundary_and_the_zero_is_a_winding";
const OUTPUT: &str = ".local/artifacts/the_primes_are_heard_through_the_zeros";
const BITS: u32 = 64;
const TERMS: u32 = 20;

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

/// The least `k/2^bits` at or above `value` — an exact upper bound, never a rendering.
fn dyadic_ceiling(value: &BigRational, bits: u32) -> String {
    let scale = BigInt::one() << bits as usize;
    let k = (value * BigRational::from_integer(scale.clone()))
        .ceil()
        .to_integer();
    format!("{}", BigRational::new(k, scale))
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

fn is_prime(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    let mut d = 2;
    while d * d <= n {
        if n % d == 0 {
            return false;
        }
        d += 1;
    }
    true
}

/// `ψ(x)` for integer `x`: the exact sum of `log p` over prime powers at most `x`, as an interval.
fn chebyshev_psi(x: u64) -> Result<RatInterval, String> {
    let mut total = RatInterval::point(BigRational::zero());
    for p in 2..=x {
        if !is_prime(p) {
            continue;
        }
        let log_p = log_integer_interval(p as u32, TERMS + 8, BITS).map_err(|e| e.to_string())?;
        let mut power = p;
        while power <= x {
            total = total.add(&log_p);
            power = match power.checked_mul(p) {
                Some(v) => v,
                None => break,
            };
        }
    }
    Ok(total)
}

/// `Σ_{|γ| ≤ T} x^ρ/ρ` over certified zero intervals for every cutoff at once: each zero's term
/// is formed once and added to the running sum, and the sum is read off at each cutoff.
fn spiral_sums(
    zeros: &[RatInterval],
    x: &BigRational,
    cutoffs: &[BigRational],
) -> Result<Vec<RatInterval>, String> {
    let log_x = log_rational_interval(x, TERMS + 8, BITS).map_err(|e| e.to_string())?;
    let root_x = exp_interval(&log_x.scale(&rat(1, 2)), TERMS, BITS);
    let half = rat(1, 2);
    let quarter = rat(1, 4);
    let mut sum = RatInterval::point(BigRational::zero());
    let mut out = Vec::with_capacity(cutoffs.len());
    let mut next_cutoff = 0usize;
    for gamma in zeros {
        while next_cutoff < cutoffs.len() && gamma.lower > cutoffs[next_cutoff] {
            out.push(sum.clone());
            next_cutoff += 1;
        }
        if next_cutoff >= cutoffs.len() {
            break;
        }
        let angle = gamma.multiply(&log_x);
        let turn = cis_interval(&angle, TERMS, BITS);
        // 2 Re(x^ρ/ρ) = 2 x^{1/2} [½ cos + γ sin] / (¼ + γ²)
        let numerator = turn.re.scale(&half).add(&gamma.multiply(&turn.im));
        let denominator = gamma.multiply(gamma).translate(&quarter);
        let term = root_x
            .multiply(&numerator)
            .divide(&denominator)
            .map_err(|e| e.to_string())?
            .scale(&rat(2, 1));
        sum = sum.add(&term).round_out(BITS);
    }
    while out.len() < cutoffs.len() {
        out.push(sum.clone());
    }
    Ok(out)
}

fn main() -> Result<(), String> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
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
    let x_min: u64 = arguments.get(3).and_then(|v| v.parse().ok()).unwrap_or(2);
    let workers: usize = arguments
        .get(2)
        .and_then(|v| v.parse().ok())
        .unwrap_or_else(|| {
            thread::available_parallelism()
                .map(|c| c.get())
                .unwrap_or(1)
        });

    let mut paths: Vec<PathBuf> = fs::read_dir(&directory)
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
    let widest = zeros
        .iter()
        .map(|z| z.width())
        .max()
        .unwrap_or_else(BigRational::zero);
    let count = zeros.len();
    println!(
        "zeros: {count} certified below {top}, widest interval {widest} (≤ {})",
        dyadic_ceiling(&widest, 12)
    );

    let cutoffs: Vec<BigRational> = [100i64, 200, 500, 1000]
        .iter()
        .map(|c| rat(*c, 1))
        .filter(|c| *c <= top)
        .collect();
    let zeros = Arc::new(zeros);
    let points: Vec<u64> = (x_min.max(2)..=x_max).collect();
    let next = Arc::new(AtomicUsize::new(0));
    let rows: Arc<Mutex<Vec<(u64, RatInterval, Vec<RatInterval>)>>> =
        Arc::new(Mutex::new(Vec::new()));
    let started = Instant::now();
    let two_pi = pi_interval(BITS).scale(&rat(2, 1));
    let log_two_pi = RatInterval::new(
        log_rational_interval(&two_pi.lower, TERMS + 8, BITS)
            .map_err(|e| e.to_string())?
            .lower,
        log_rational_interval(&two_pi.upper, TERMS + 8, BITS)
            .map_err(|e| e.to_string())?
            .upper,
    );
    thread::scope(|scope| {
        for _ in 0..workers.max(1) {
            let zeros = Arc::clone(&zeros);
            let next = Arc::clone(&next);
            let rows = Arc::clone(&rows);
            let cutoffs = cutoffs.clone();
            let log_two_pi = log_two_pi.clone();
            let points = &points;
            scope.spawn(move || {
                loop {
                    let index = next.fetch_add(1, Ordering::Relaxed);
                    let Some(&n) = points.get(index) else { break };
                    // read at the half-integer x = n + 1/2, where ψ has no jump
                    let x = rat(2 * n as i64 + 1, 2);
                    let psi = match chebyshev_psi(n) {
                        Ok(v) => v,
                        Err(_) => continue,
                    };
                    let x_squared_inverse = rat(4, (2 * n as i64 + 1) * (2 * n as i64 + 1));
                    let one_minus = RatInterval::point(rat(1, 1) - x_squared_inverse);
                    let half_log = RatInterval::new(
                        log_rational_interval(&one_minus.lower, TERMS + 8, BITS)
                            .map(|l| l.lower)
                            .unwrap_or_else(|_| BigRational::zero()),
                        log_rational_interval(&one_minus.upper, TERMS + 8, BITS)
                            .map(|l| l.upper)
                            .unwrap_or_else(|_| BigRational::zero()),
                    )
                    .scale(&rat(1, 2));
                    let Ok(spirals) = spiral_sums(&zeros, &x, &cutoffs) else {
                        continue;
                    };
                    // ψ_T(x) = x − Σ − log 2π − ½ log(1 − x^{-2})
                    let reconstructions: Vec<RatInterval> = spirals
                        .iter()
                        .map(|spiral| {
                            RatInterval::point(x.clone())
                                .subtract(spiral)
                                .subtract(&log_two_pi)
                                .subtract(&half_log)
                                .round_out(BITS)
                        })
                        .collect();
                    rows.lock().expect("rows").push((n, psi, reconstructions));
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

    // residual statistics per cutoff and per height band of x
    let mut report = String::new();
    report.push_str(&format!("zeros={count} widest_interval={widest} x_max={x_max} workers={workers} elapsed_s={elapsed:.1}\n"));
    for (ci, cutoff) in cutoffs.iter().enumerate() {
        for (lo, hi) in [(2u64, 100u64), (100, 300), (300, 600), (600, 1000)] {
            if lo >= x_max {
                continue;
            }
            let mut worst = BigRational::zero();
            let mut n_rows = 0usize;
            for (n, psi, recs) in rows.iter() {
                if *n < lo || *n >= hi.min(x_max + 1) {
                    continue;
                }
                let Some(rec) = recs.get(ci) else { continue };
                let residual = psi.subtract(rec);
                let bound = if residual.lower.abs() > residual.upper.abs() {
                    residual.lower.abs()
                } else {
                    residual.upper.abs()
                };
                if bound > worst {
                    worst = bound;
                }
                n_rows += 1;
            }
            // the reference x log²x/(2πT) at x = hi, as an exact interval
            let log_hi =
                log_integer_interval(hi as u32, TERMS + 8, BITS).map_err(|e| e.to_string())?;
            let reference = log_hi
                .square()
                .scale(&rat(hi as i64, 1))
                .divide(&pi_interval(BITS).scale(&(rat(2, 1) * cutoff)))
                .map_err(|e| e.to_string())?;
            report.push_str(&format!(
                "cutoff T={cutoff}  x in [{lo},{hi})  rows={n_rows}  max |ψ − ψ_T| ≤ {} (= {} exactly)  reference x log²x/(2πT) at x={hi} ≤ {}\n",
                dyadic_ceiling(&worst, 6),
                worst,
                dyadic_ceiling(&reference.upper, 6)
            ));
        }
    }
    // the jumps: ψ_T(p + ½) − ψ_T(p − ½) against log p, for the first primes, at the top cutoff
    report.push_str("jumps at the top cutoff (reconstructed jump ÷ log p):\n");
    let top_index = cutoffs.len().saturating_sub(1);
    let mut shown = 0;
    for (n, _, recs) in rows.iter() {
        if !is_prime(*n) || shown >= 25 {
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
        let log_p = log_integer_interval(*n as u32, TERMS + 8, BITS).map_err(|e| e.to_string())?;
        let ratio = jump.divide(&log_p).map_err(|e| e.to_string())?;
        report.push_str(&format!(
            "  p={n:>4}  jump ∈ {}  log p ∈ {}  ratio ∈ {}\n",
            dyadic_interval(&jump, 10),
            dyadic_interval(&log_p, 10),
            dyadic_interval(&ratio, 10)
        ));
        shown += 1;
    }
    print!("{report}");
    fs::create_dir_all(OUTPUT).map_err(|e| e.to_string())?;
    let range = format!("{:05}-{:05}", x_min.max(2), x_max);
    fs::write(format!("{OUTPUT}/receipt-{range}.txt"), &report).map_err(|e| e.to_string())?;
    let mut table = String::from("n\tpsi(n)\t");
    for c in &cutoffs {
        table.push_str(&format!("psi_T_at_n_plus_half_T={c}\t"));
    }
    table.push('\n');
    for (n, psi, recs) in rows.iter() {
        table.push_str(&format!("{n}\t{}\t", psi));
        for r in recs {
            table.push_str(&format!("{}\t", r));
        }
        table.push('\n');
    }
    fs::write(format!("{OUTPUT}/reconstruction-{range}.tsv"), table).map_err(|e| e.to_string())?;
    println!("artifact={OUTPUT}/receipt-{range}.txt");
    Ok(())
}
