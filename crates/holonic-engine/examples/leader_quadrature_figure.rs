//! Drive `leader_quadrature` and deposit the lineage as exact rational TSV rows for a figure.
//!
//! This example adds nothing to the model. It declares material and laws using the module's own
//! test fixtures verbatim, calls [`integrate_by_leaders`], and writes what came back — every
//! number through `format_rat`, no decimal anywhere, no float type in this file.
//!
//! What it deposits, per declared run:
//!
//!   * `founded_path.tsv`   — the material boundary `f` evaluated EXACTLY on a declared mesh,
//!                            carrying `germ_index` so a renderer can break the piecewise curve at
//!                            the standing forms rather than joining across a real discontinuity.
//!   * `extensions.tsv`     — one row per discrete extension event: base point, span, the exact
//!                            winding swept, the running sum, FOUND/RIDE, and the refusal (a
//!                            retained `RefoundingObstruction` and/or a `RefusedRide`) at that index.
//!   * `summary.tsv`        — per run: the returned area, the independent germwise oracle, their
//!                            disagreement, and the population counts.
//!
//! The oracle column is the grading. If a run's area differs from `germwise_oracle_area`, that
//! difference is deposited as-is: under `UnclampedAncestry` a non-zero disagreement is the module's
//! own measured aperture violation and is a first-class return, not an error to hide.

use std::error::Error;
use std::fmt::Write as _;
use std::fs;
use std::path::PathBuf;

use holonic_engine::leader_quadrature::{
    ExtensionKind, LeaderLaw, LeaderQuadrature, LocalJet, MaterialBoundary, RationalGerm,
    RideDiscipline, germwise_oracle_area, integrate_by_leaders,
};
use relational_geometry::{Rat, format_rat, integer, rat};

// ------------------------------------------------------------------------------------------
// declared options — every knob is a named declaration, none is a literal buried in logic

/// How the founded path is sampled for rendering. This is a *rendering* mesh only: it never
/// touches the quadrature, which has no mesh at all.
struct PathMesh {
    /// Samples per germ, endpoints included. The germ's own jet is evaluated exactly at each.
    samples_per_germ: usize,
}

/// One declared growth: which law a leader population grows under.
struct RunDeclaration {
    label: &'static str,
    grain: Rat,
    discipline: RideDiscipline,
    witness_depth: usize,
    /// Whether this run is inside the module's declared aperture.
    inside_aperture: bool,
}

/// One declared material boundary, reproduced from the module's own test fixtures.
struct MaterialDeclaration {
    label: &'static str,
    /// The area the fixture carries as a hand-computed literal in the test module.
    hand_figure: Rat,
    boundary: MaterialBoundary,
}

fn jet(coefficients: &[(i64, i64)]) -> LocalJet {
    LocalJet::new(
        coefficients
            .iter()
            .map(|(numerator, denominator)| rat(*numerator, *denominator))
            .collect(),
    )
    .expect("a jet carries at least one coefficient")
}

fn germ(extent: Rat, coefficients: &[(i64, i64)]) -> RationalGerm {
    RationalGerm::new(extent, jet(coefficients)).expect("a germ conducts over a positive extent")
}

/// `unaligned_piecewise` from `leader_quadrature::tests`, verbatim.
///
/// `f = t` on `[0, 7/3)`, `f = 5/2` on the next `4/5`, `f = 11/4 + 2t` on the last `3/2`.
/// Hand figure `799/72`.
fn unaligned_piecewise() -> MaterialDeclaration {
    MaterialDeclaration {
        label: "unaligned-piecewise",
        hand_figure: rat(799, 72),
        boundary: MaterialBoundary::new(vec![
            germ(rat(7, 3), &[(0, 1), (1, 1)]),
            germ(rat(4, 5), &[(5, 2)]),
            germ(rat(3, 2), &[(11, 4), (2, 1)]),
        ])
        .expect("a non-empty material boundary"),
    }
}

/// `abrupt_material` from `leader_quadrature::tests`, verbatim.
///
/// `f = x` on `[0,2)`, then `g(u) = 7 + 3u^2` on the next `4`. Hand figure `94`.
fn abrupt_material() -> MaterialDeclaration {
    MaterialDeclaration {
        label: "abrupt-material",
        hand_figure: integer(94),
        boundary: MaterialBoundary::new(vec![
            germ(integer(2), &[(0, 1), (1, 1)]),
            germ(integer(4), &[(7, 1), (0, 1), (3, 1)]),
        ])
        .expect("a non-empty material boundary"),
    }
}

/// `reverting_material` from `leader_quadrature::tests`, verbatim.
///
/// `f = x` on `[0,3)`, `f = 2` on `[3,4)`, `f = x` on `[4,7)`. Hand figure `23`.
fn reverting_material() -> MaterialDeclaration {
    MaterialDeclaration {
        label: "reverting-material",
        hand_figure: integer(23),
        boundary: MaterialBoundary::new(vec![
            germ(integer(3), &[(0, 1), (1, 1)]),
            germ(integer(1), &[(2, 1)]),
            germ(integer(3), &[(4, 1), (1, 1)]),
        ])
        .expect("a non-empty material boundary"),
    }
}

// ------------------------------------------------------------------------------------------

/// Absolute left endpoints of each germ, by accumulating declared extents.
fn germ_origins(boundary: &MaterialBoundary) -> Vec<Rat> {
    let mut origins = Vec::with_capacity(boundary.germ_count());
    let mut running = Rat::from_integer(0.into());
    for germ in boundary.germs() {
        origins.push(running.clone());
        running = &running + germ.extent();
    }
    origins
}

/// The founded path sampled exactly: `(germ_index, x, f(x))` with `f` the germ's own jet.
///
/// The right endpoint of each germ is emitted as that germ's left-limit value. Where the material
/// jumps, the two germs report different values at the same `x`; that disagreement is the standing
/// form changing and is deposited rather than smoothed.
fn founded_path_rows(boundary: &MaterialBoundary, mesh: &PathMesh) -> Vec<(usize, Rat, Rat)> {
    let origins = germ_origins(boundary);
    let divisor = Rat::from_integer(i64::try_from(mesh.samples_per_germ).unwrap_or(1).into());
    let mut rows = Vec::new();
    for (index, germ) in boundary.germs().iter().enumerate() {
        for step in 0..=mesh.samples_per_germ {
            let numerator = Rat::from_integer(i64::try_from(step).unwrap_or(0).into());
            let local = germ.extent() * &numerator / &divisor;
            let value = germ.jet().value_at(&local);
            rows.push((index, &origins[index] + &local, value));
        }
    }
    rows
}

fn classification(kind: &ExtensionKind) -> (&'static str, String) {
    match kind {
        ExtensionKind::Found => ("FOUND", String::new()),
        ExtensionKind::Ride { scale } => ("RIDE", format_rat(scale)),
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let mesh = PathMesh {
        samples_per_germ: 48,
    };

    let materials = vec![
        unaligned_piecewise(),
        abrupt_material(),
        reverting_material(),
    ];

    let runs = vec![
        RunDeclaration {
            label: "grain-only",
            grain: rat(1, 4),
            discipline: RideDiscipline::GrainOnly,
            witness_depth: 1,
            inside_aperture: true,
        },
        RunDeclaration {
            label: "germ-bounded",
            grain: rat(1, 4),
            discipline: RideDiscipline::GermBounded,
            witness_depth: 1,
            inside_aperture: true,
        },
        RunDeclaration {
            label: "unclamped-ancestry",
            grain: rat(1, 4),
            discipline: RideDiscipline::UnclampedAncestry,
            witness_depth: 1,
            inside_aperture: false,
        },
    ];

    let output_directory = PathBuf::from("target/leader_quadrature_figure");
    fs::create_dir_all(&output_directory)?;

    let mut path_tsv = String::new();
    writeln!(path_tsv, "material\tgerm_index\tx\tf_x")?;
    for declaration in &materials {
        for (germ_index, x, value) in founded_path_rows(&declaration.boundary, &mesh) {
            writeln!(
                path_tsv,
                "{}\t{}\t{}\t{}",
                declaration.label,
                germ_index,
                format_rat(&x),
                format_rat(&value)
            )?;
        }
    }
    fs::write(output_directory.join("founded_path.tsv"), &path_tsv)?;

    let mut extensions_tsv = String::new();
    writeln!(
        extensions_tsv,
        "material\trun\tindex\tgerm_index\tbase_point\tspan\tf_at_base\tswept\trunning_sum\t\
         classification\tride_scale\trefusal\trefusal_residual\trefused_span"
    )?;

    let mut summary_tsv = String::new();
    writeln!(
        summary_tsv,
        "material\trun\tgrain\tdiscipline\twitness_depth\tinside_aperture\tspan\tjet_aperture\t\
         area\toracle_area\thand_figure\tarea_minus_oracle\textensions\tfound\trides\t\
         obstructions\trefused_rides\tscale_witnesses"
    )?;

    let mut console = String::new();
    for declaration in &materials {
        let oracle = germwise_oracle_area(&declaration.boundary);
        for run in &runs {
            let law = LeaderLaw::new(run.grain.clone(), run.discipline, run.witness_depth);
            let quadrature: LeaderQuadrature = integrate_by_leaders(&declaration.boundary, &law)?;

            for extension in &quadrature.extensions {
                let (kind, scale) = classification(&extension.kind);
                let obstruction = quadrature
                    .obstructions
                    .iter()
                    .find(|entry| entry.extension_index == extension.index);
                let refused = quadrature
                    .refused_rides
                    .iter()
                    .find(|entry| entry.extension_index == extension.index);
                let refusal = match (obstruction.is_some(), refused.is_some()) {
                    (true, true) => "REFOUNDING+REFUSED-RIDE",
                    (true, false) => "REFOUNDING-OBSTRUCTION",
                    (false, true) => "REFUSED-RIDE",
                    (false, false) => "NONE",
                };
                let standing = declaration
                    .boundary
                    .standing_at(&extension.base_offset)
                    .expect("every extension base point is inside the region");
                let value_at_base = standing.jet.value_at(&Rat::from_integer(0.into()));

                writeln!(
                    extensions_tsv,
                    "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                    declaration.label,
                    run.label,
                    extension.index,
                    extension.germ_index,
                    format_rat(&extension.base_offset),
                    format_rat(&extension.span),
                    format_rat(&value_at_base),
                    format_rat(&extension.winding),
                    format_rat(&extension.running_sum),
                    kind,
                    scale,
                    refusal,
                    obstruction
                        .map(|entry| format_rat(&entry.winding_residual))
                        .unwrap_or_default(),
                    refused
                        .map(|entry| format_rat(&entry.proposed_span))
                        .unwrap_or_default(),
                )?;
            }

            let disagreement = &quadrature.area - &oracle;
            writeln!(
                summary_tsv,
                "{}\t{}\t{}\t{:?}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                declaration.label,
                run.label,
                format_rat(&run.grain),
                run.discipline,
                run.witness_depth,
                run.inside_aperture,
                format_rat(declaration.boundary.span()),
                quadrature.jet_aperture,
                format_rat(&quadrature.area),
                format_rat(&oracle),
                format_rat(&declaration.hand_figure),
                format_rat(&disagreement),
                quadrature.extension_count(),
                quadrature.found_count(),
                quadrature.ride_count(),
                quadrature.obstructions.len(),
                quadrature.refused_rides.len(),
                quadrature.scale_witnesses.len(),
            )?;

            writeln!(
                console,
                "{:<20} {:<20} area {:<10} oracle {:<10} hand {:<10} delta {:<8} ext {:<4} \
                 found {:<4} ride {:<3} obstr {:<3} refused {:<3} witness {}",
                declaration.label,
                run.label,
                format_rat(&quadrature.area),
                format_rat(&oracle),
                format_rat(&declaration.hand_figure),
                format_rat(&disagreement),
                quadrature.extension_count(),
                quadrature.found_count(),
                quadrature.ride_count(),
                quadrature.obstructions.len(),
                quadrature.refused_rides.len(),
                quadrature.scale_witnesses.len(),
            )?;
        }
    }

    fs::write(output_directory.join("extensions.tsv"), &extensions_tsv)?;
    fs::write(output_directory.join("summary.tsv"), &summary_tsv)?;

    print!("{console}");
    println!("deposited under {}", output_directory.display());
    Ok(())
}
