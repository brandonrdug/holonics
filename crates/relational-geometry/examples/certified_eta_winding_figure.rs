//! The certified winding of the Dirichlet eta function over the critical strip,
//! emitted as exact rational tables for an external rendering membrane.
//!
//! Nothing here samples, estimates, or approximates.  Each band of the strip is
//! a rational receiver box; its boundary is carried through Euler--Maclaurin
//! with exact Bernoulli corrections and an outward-rounded rational remainder;
//! the boundary image polygon is closed and its winding about the origin is
//! read off by an exact ray-crossing count.  There is no `atan2`, no branch
//! cut, and no floating-point scalar anywhere in this file.  The integer that
//! comes back is the argument-principle zero count of eta inside the box, and
//! it is certified rather than observed.
//!
//! Every knob is a declared typed option on `WindingSurfaceOptions` -- the
//! receiver window, the mesh function that cuts it into bands, the certified
//! subdivision depth, the walk length -- so the surface is parametric and no
//! constant is buried in the logic.  Colour and layout are not decided here;
//! this file emits exact rationals and the rendering membrane owns the gauge.

use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, mpsc};
use std::thread;
use std::time::Instant;

use num_rational::BigRational;

use relational_geometry::{
    ComplexReceiverBox, EtaCurrentReceipt, ExactSeriesConfig, RatComplex, RatInterval,
    WindingReceipt, eta_boundary_winding, eta_partial_current, format_rat, integer, rat,
};

type Rat = BigRational;

/// Declared options for the winding surface.
///
/// Mathematica-style: every parameter of the model is a named typed field with
/// a lawful default, never a literal spelled inside a computation.
#[derive(Clone, Debug)]
struct WindingSurfaceOptions {
    /// Real-part window of the receiver, straddling the critical line.
    sigma_window: RatInterval,
    /// Imaginary-part window scanned by the mesh function.
    tau_window: RatInterval,
    /// Mesh function grain: the exact height of one band.
    band_step: Rat,
    /// Maximum certified subdivision depth per boundary segment.
    boundary_depth: u32,
    /// Number of terms retained in the eta partial-sum walk.
    walk_terms: u32,
    /// Real part at which the partial-sum walk is taken.
    walk_sigma: Rat,
    /// Physical worker count for the band scan.
    workers: usize,
    /// Directory into which the exact tables are emitted.
    output_root: PathBuf,
    /// Series enclosure grain shared by every evaluation.
    series: ExactSeriesConfig,
}

impl Default for WindingSurfaceOptions {
    fn default() -> Self {
        Self {
            sigma_window: RatInterval::new(rat(2, 5), rat(3, 5)),
            tau_window: RatInterval::new(integer(12), integer(20)),
            band_step: integer(1),
            boundary_depth: 14,
            walk_terms: 96,
            walk_sigma: rat(1, 2),
            workers: 8,
            output_root: PathBuf::from("target/certified-eta-winding-figure"),
            series: ExactSeriesConfig {
                dyadic_bits: 96,
                euler_maclaurin_start: 12,
                euler_maclaurin_order: 10,
                log_terms: 28,
                exponential_terms: 18,
                trigonometric_terms: 16,
            },
        }
    }
}

impl WindingSurfaceOptions {
    /// The mesh function: cut the declared tau window into exact bands.
    ///
    /// Only whole steps are emitted; a trailing remainder shorter than one
    /// grain is refused rather than silently widened.
    fn mesh(&self) -> Vec<RatInterval> {
        let mut bands = Vec::new();
        let mut lower = self.tau_window.lower.clone();
        while &lower + &self.band_step <= self.tau_window.upper {
            let upper = &lower + &self.band_step;
            bands.push(RatInterval::new(lower.clone(), upper.clone()));
            lower = upper;
        }
        bands
    }

    /// A receiver box over the declared sigma window at one mesh band.
    fn receiver(&self, band: &RatInterval) -> ComplexReceiverBox {
        ComplexReceiverBox::new(self.sigma_window.clone(), band.clone())
    }
}

#[derive(Clone, Debug)]
struct BandOutcome {
    ordinal: usize,
    band: RatInterval,
    /// `Ok` carries the certified receipt; `Err` carries the refusal verbatim.
    receipt: Result<WindingReceipt, String>,
    milliseconds: u128,
}

/// Scan every mesh band, retaining refusals as first-class outcomes.
fn scan_bands(options: &WindingSurfaceOptions) -> Vec<BandOutcome> {
    let bands = Arc::new(options.mesh());
    let cursor = Arc::new(AtomicUsize::new(0));
    let series = Arc::new(options.series.clone());
    let shared = Arc::new(options.clone());
    let (sender, inbox) = mpsc::channel();

    thread::scope(|scope| {
        for _ in 0..options.workers {
            let bands = Arc::clone(&bands);
            let cursor = Arc::clone(&cursor);
            let series = Arc::clone(&series);
            let shared = Arc::clone(&shared);
            let sender = sender.clone();
            scope.spawn(move || {
                loop {
                    let ordinal = cursor.fetch_add(1, Ordering::Relaxed);
                    let Some(band) = bands.get(ordinal) else {
                        break;
                    };
                    let started = Instant::now();
                    let receipt = eta_boundary_winding(
                        &shared.receiver(band),
                        &series,
                        shared.boundary_depth,
                    )
                    .map_err(|error| error.to_string());
                    sender
                        .send(BandOutcome {
                            ordinal,
                            band: band.clone(),
                            receipt,
                            milliseconds: started.elapsed().as_millis(),
                        })
                        .expect("the scan inbox remains live");
                }
            });
        }
    });
    drop(sender);

    let mut outcomes = inbox.into_iter().collect::<Vec<_>>();
    outcomes.sort_by_key(|outcome| outcome.ordinal);
    outcomes
}

fn write_table(root: &PathBuf, name: &str, header: &str, rows: &[String]) -> PathBuf {
    let path = root.join(name);
    let mut file = fs::File::create(&path).expect("the emission directory is writable");
    writeln!(file, "{header}").expect("the header is writable");
    for row in rows {
        writeln!(file, "{row}").expect("a row is writable");
    }
    path
}

/// Read declared options from the command line, leaving every unstated field at
/// its lawful default.  Usage: `-- <tau_lo> <tau_hi> [workers]`, integers only,
/// so the receiver window stays exactly rational.
fn options_from_arguments() -> WindingSurfaceOptions {
    let mut options = WindingSurfaceOptions::default();
    let arguments = std::env::args().skip(1).collect::<Vec<_>>();
    if arguments.len() >= 2 {
        let lower: i64 = arguments[0].parse().expect("tau_lo is an integer");
        let upper: i64 = arguments[1].parse().expect("tau_hi is an integer");
        assert!(lower < upper, "the tau window must be nonempty");
        options.tau_window = RatInterval::new(integer(lower), integer(upper));
    }
    if arguments.len() >= 3 {
        options.workers = arguments[2].parse().expect("workers is an integer");
        assert!(options.workers >= 1, "the scan needs at least one worker");
    }
    options
}

fn main() {
    let options = options_from_arguments();
    fs::create_dir_all(&options.output_root).expect("the emission directory is creatable");

    let started = Instant::now();
    let outcomes = scan_bands(&options);

    // ---- Table A: the certified winding atlas ------------------------------
    let mut atlas_rows = Vec::new();
    for outcome in &outcomes {
        let (winding, vertices, ray, status) = match &outcome.receipt {
            Ok(receipt) => (
                receipt.winding.to_string(),
                receipt.polygon.len().to_string(),
                receipt.ray_parameter.to_string(),
                "certified".to_owned(),
            ),
            Err(error) => (
                "NA".to_owned(),
                "NA".to_owned(),
                "NA".to_owned(),
                format!("refused: {error}"),
            ),
        };
        atlas_rows.push(format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            format_rat(&outcome.band.lower),
            format_rat(&outcome.band.upper),
            format_rat(&options.sigma_window.lower),
            format_rat(&options.sigma_window.upper),
            winding,
            vertices,
            ray,
            status,
            outcome.milliseconds
        ));
    }
    let atlas_path = write_table(
        &options.output_root,
        "eta_winding_atlas.tsv",
        "tau_lo\ttau_hi\tsigma_lo\tsigma_hi\twinding\tpolygon_vertices\tray_parameter\tstatus\tmilliseconds",
        &atlas_rows,
    );

    // ---- Table B: boundary image polygons of the charged bands ------------
    let charged = outcomes
        .iter()
        .filter_map(|outcome| match &outcome.receipt {
            Ok(receipt) if receipt.winding != 0 => Some((outcome, receipt)),
            _ => None,
        })
        .collect::<Vec<_>>();

    let mut polygon_rows = Vec::new();
    for (outcome, receipt) in &charged {
        for (index, vertex) in receipt.polygon.iter().enumerate() {
            polygon_rows.push(format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}",
                outcome.ordinal,
                format_rat(&outcome.band.lower),
                format_rat(&outcome.band.upper),
                receipt.winding,
                index,
                format_rat(&vertex.re),
                format_rat(&vertex.im)
            ));
        }
    }
    let polygon_path = write_table(
        &options.output_root,
        "eta_boundary_polygon.tsv",
        "band_ordinal\ttau_lo\ttau_hi\twinding\tvertex_index\tre\tim",
        &polygon_rows,
    );

    // ---- Table C: the eta partial-sum walk on the critical line -----------
    // The walk is taken at the midpoint of the first charged band, so the
    // ordinate is selected by the certified winding rather than declared.
    let mut walk_rows = Vec::new();
    let mut walk_note = "no charged band: the walk was not taken".to_owned();
    if let Some((outcome, _)) = charged.first() {
        let tau = outcome.band.midpoint();
        match eta_partial_current(
            options.walk_sigma.clone(),
            tau.clone(),
            options.walk_terms,
            &options.series,
        ) {
            Ok(EtaCurrentReceipt {
                terms, tail_radius, ..
            }) => {
                for term in &terms {
                    let step: RatComplex = term.contribution.midpoint();
                    let point: RatComplex = term.partial_sum.midpoint();
                    walk_rows.push(format!(
                        "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                        term.ordinal,
                        term.hand,
                        format_rat(&step.re),
                        format_rat(&step.im),
                        format_rat(&point.re),
                        format_rat(&point.im),
                        format_rat(&tail_radius),
                        format_rat(&tau)
                    ));
                }
                walk_note = format!(
                    "walk taken at sigma={} tau={} over {} terms; tail radius {}",
                    format_rat(&options.walk_sigma),
                    format_rat(&tau),
                    options.walk_terms,
                    format_rat(&tail_radius)
                );
            }
            Err(error) => {
                walk_note = format!("the walk refused: {error}");
            }
        }
    }
    let walk_path = write_table(
        &options.output_root,
        "eta_partial_walk.tsv",
        "ordinal\thand\tstep_re\tstep_im\tpartial_re\tpartial_im\ttail_radius\ttau",
        &walk_rows,
    );

    // ---- Console receipt --------------------------------------------------
    println!("# certified eta winding over the critical strip");
    println!(
        "# sigma in [{}, {}], tau in [{}, {}], grain {}, depth {}",
        format_rat(&options.sigma_window.lower),
        format_rat(&options.sigma_window.upper),
        format_rat(&options.tau_window.lower),
        format_rat(&options.tau_window.upper),
        format_rat(&options.band_step),
        options.boundary_depth
    );
    for outcome in &outcomes {
        match &outcome.receipt {
            Ok(receipt) => println!(
                "band [{}, {}]\twinding {}\tvertices {}\tray {}\t{} ms",
                format_rat(&outcome.band.lower),
                format_rat(&outcome.band.upper),
                receipt.winding,
                receipt.polygon.len(),
                receipt.ray_parameter,
                outcome.milliseconds
            ),
            Err(error) => println!(
                "band [{}, {}]\tREFUSED\t{}\t{} ms",
                format_rat(&outcome.band.lower),
                format_rat(&outcome.band.upper),
                error,
                outcome.milliseconds
            ),
        }
    }
    let certified_total: i32 = outcomes
        .iter()
        .filter_map(|outcome| outcome.receipt.as_ref().ok())
        .map(|receipt| receipt.winding)
        .sum();
    // A refused band contributes nothing to this sum while its zeros remain in the window, so the
    // total is a LOWER BOUND whenever any band refused, and calling it a count would be an aperture
    // reporting what it admitted and dropping what it excluded. The refusals are named here for the
    // same reason `ArrivalResponse` reports its exclusions rather than discarding them.
    let refused = outcomes
        .iter()
        .filter(|outcome| outcome.receipt.is_err())
        .count();
    if refused == 0 {
        println!("# certified zero count over the scanned window: {certified_total}");
    } else {
        println!(
            "# certified zero count over the scanned window: AT LEAST {certified_total} \
             ({refused} band(s) refused and their zeros are still in the window)"
        );
    }
    println!("# charged bands: {}", charged.len());
    println!("# {walk_note}");
    println!("# atlas -> {}", atlas_path.display());
    println!("# polygon -> {}", polygon_path.display());
    println!("# walk -> {}", walk_path.display());
    println!("# elapsed milliseconds: {}", started.elapsed().as_millis());
}
