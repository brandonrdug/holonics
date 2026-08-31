//! Do the vortices repel, and in which symmetry class?
//!
//! The 649 certified zeros of the atlas are read as a one-dimensional gas on the mirror. Two
//! readings, both exact and both ratios: the gap-ratio statistic
//! `r_i = min(g_i, g_{i+1}) / max(g_i, g_{i+1})` (Oganesyan–Huse), whose mean needs no unfolding
//! and separates the ensembles — Poisson `⟨r⟩ = 2 ln 2 − 1 ≈ 0.3863`, orthogonal `≈ 0.5359`,
//! unitary `≈ 0.5996`, symplectic `≈ 0.6744`; and the unfolded spacing `s_i = (θ(γ_{i+1}) −
//! θ(γ_i))/π`, the tide's own increment between consecutive zeros, whose small-`s` mass
//! distinguishes repulsion (`P(s < 1/2) ≈ 0.107` for the unitary surmise `(32/π²) s² e^{−4s²/π}`,
//! `≈ 0.393` for Poisson). Every ordinate enters as its certified interval midpoint; every
//! statistic is an exact rational, rendered at the end.

use std::env;
use std::fs;
use std::path::PathBuf;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{ToPrimitive, Zero};
use relational_geometry::{EtaRatioAtlas, RatInterval, pi_interval, riemann_siegel_theta};

const DEFAULT_ARTIFACTS: &str =
    "output/the_card_returns_the_eta_boundary_and_the_zero_is_a_winding";
const OUTPUT: &str = "output/the_vortices_repel_like_a_unitary_gas";

fn render(value: &BigRational) -> String {
    format!("{} (≈ {:.4})", value, value.to_f64().unwrap_or(f64::NAN))
}

fn main() -> Result<(), String> {
    let directory = PathBuf::from(
        env::args()
            .nth(1)
            .unwrap_or_else(|| DEFAULT_ARTIFACTS.to_owned()),
    );
    let mut paths: Vec<PathBuf> = fs::read_dir(&directory)
        .map_err(|error| error.to_string())?
        .filter_map(|entry| entry.ok().map(|e| e.path()))
        .filter(|path| {
            path.file_name().and_then(|n| n.to_str()).is_some_and(|n| {
                n.starts_with("holonic-eta-ratio-atlas-resident-") && n.ends_with(".ron")
            })
        })
        .collect();
    paths.sort();
    let mut ordinates: Vec<RatInterval> = Vec::new();
    let mut config = None;
    for path in &paths {
        let encoded = fs::read_to_string(path).map_err(|error| error.to_string())?;
        let atlas: EtaRatioAtlas =
            ron::from_str(&encoded).map_err(|error| format!("{}: {error}", path.display()))?;
        if config.is_none() {
            config = Some(atlas.config.clone());
        }
        for lineage in &atlas.zero_lineages {
            ordinates.push(lineage.final_receiver.tau.clone());
        }
    }
    let config = config.ok_or_else(|| "no artifacts".to_owned())?;
    ordinates.sort_by(|a, b| a.lower.cmp(&b.lower));
    for pair in ordinates.windows(2) {
        if pair[0].upper > pair[1].lower {
            return Err(format!(
                "two certified zero intervals overlap: {} and {}",
                pair[0], pair[1]
            ));
        }
    }
    let midpoints: Vec<BigRational> = ordinates.iter().map(|o| o.midpoint()).collect();
    let count = midpoints.len();

    // gap ratios, no unfolding
    let gaps: Vec<BigRational> = midpoints.windows(2).map(|p| &p[1] - &p[0]).collect();
    let mut ratio_sum = BigRational::zero();
    let mut ratio_count = 0usize;
    for pair in gaps.windows(2) {
        let (a, b) = (&pair[0], &pair[1]);
        let r = if a < b { a / b } else { b / a };
        ratio_sum += r;
        ratio_count += 1;
    }
    let mean_ratio = &ratio_sum / BigRational::from_integer(BigInt::from(ratio_count as i64));

    // unfolded spacings by the exact tide
    let pi = pi_interval(config.dyadic_bits);
    let mut thetas: Vec<RatInterval> = Vec::with_capacity(count);
    for gamma in &midpoints {
        thetas.push(riemann_siegel_theta(gamma, &config).map_err(|error| error.to_string())?);
    }
    let mut spacings: Vec<BigRational> = Vec::with_capacity(count - 1);
    for pair in thetas.windows(2) {
        let increment = pair[1]
            .subtract(&pair[0])
            .divide(&pi)
            .map_err(|e| e.to_string())?;
        spacings.push(increment.midpoint());
    }
    let n = BigRational::from_integer(BigInt::from(spacings.len() as i64));
    let mean_spacing = spacings.iter().fold(BigRational::zero(), |a, b| a + b) / &n;
    let below = |threshold: BigRational| -> BigRational {
        let c = spacings.iter().filter(|s| **s < threshold).count();
        BigRational::from_integer(BigInt::from(c as i64)) / &n
    };
    let quarter = BigRational::new(BigInt::from(1), BigInt::from(4));
    let half = BigRational::new(BigInt::from(1), BigInt::from(2));
    let one = BigRational::from_integer(BigInt::from(1));
    let (p_quarter, p_half, p_one) = (below(quarter), below(half), below(one));
    let variance = spacings
        .iter()
        .map(|s| {
            let d = s - &mean_spacing;
            &d * &d
        })
        .fold(BigRational::zero(), |a, b| a + b)
        / &n;
    let smallest = spacings
        .iter()
        .min()
        .cloned()
        .unwrap_or_else(BigRational::zero);

    let report = format!(
        "zeros read: {count} (certified intervals, none overlapping)\n\
         gap-ratio mean ⟨min(r,1/r)⟩ over {ratio_count} triples = {}\n\
         \x20  reference: Poisson 2ln2−1 ≈ 0.3863 · orthogonal ≈ 0.5359 · unitary ≈ 0.5996 · symplectic ≈ 0.6744\n\
         unfolded spacing s = Δθ/π: mean = {}  variance = {}  smallest = {}\n\
         \x20  P(s < 1/4) = {}   P(s < 1/2) = {}   P(s < 1) = {}\n\
         \x20  reference unitary surmise: P(s<1/4) ≈ 0.0158, P(s<1/2) ≈ 0.107, P(s<1) ≈ 0.516, variance ≈ 0.178; Poisson: 0.221, 0.393, 0.632, 1\n",
        render(&mean_ratio),
        render(&mean_spacing),
        render(&variance),
        render(&smallest),
        render(&p_quarter),
        render(&p_half),
        render(&p_one)
    );
    print!("{report}");
    fs::create_dir_all(OUTPUT).map_err(|e| e.to_string())?;
    fs::write(format!("{OUTPUT}/receipt.txt"), &report).map_err(|e| e.to_string())?;
    let mut table = String::from("gamma_midpoint\tunfolded_spacing_to_next\n");
    for (gamma, s) in midpoints.iter().zip(spacings.iter()) {
        table.push_str(&format!("{}\t{}\n", gamma, s));
    }
    fs::write(format!("{OUTPUT}/spacings.tsv"), table).map_err(|e| e.to_string())?;
    println!("artifact={OUTPUT}/receipt.txt");
    Ok(())
}
