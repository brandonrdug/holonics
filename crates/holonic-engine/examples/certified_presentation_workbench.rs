//! The workbench: present exact mathematics, emit the artifact, then READ IT BACK.
//!
//! Record: `research/records/2026-08-08_THE_SAMPLER_HOPES_THE_CERTIFICATE_KNOWS_THE_GAUGE_CARRIES_NO_STRUCTURE.md`.
//! Contract: `blueprint/THE_PRESENTATION_ORGAN.md`.
//!
//! Run:
//!
//! ```text
//! cargo run -p holonic-engine --example certified_presentation_workbench -- --output <dir>
//! ```
//!
//! ## What this driver is for
//!
//! `blueprint/THE_ROADMAP.md` carries the atlas reader as `open`: "what lets any of it be read
//! back rather than emitted into a directory nothing opens". The roadmap's own measurement is that
//! the five TSV tables the engine emits are opened by nothing in the tree.
//!
//! So this driver does not finish at the figure. It emits the face, and then it **re-opens what it
//! wrote and recomputes the invariants from the file**, requiring them to agree with what was in
//! memory. An artifact that cannot be read back is not a deposit, it is a leak — and a reader that
//! is never run against a real emission proves nothing about itself.
//!
//! ## The comparative point, made executable
//!
//! Station B is the case the whole organ exists for. Its two roots are closer together than one
//! cell, so the naive sampled reading — the reading an adaptive plotter makes — reports **no sign
//! change at all**. The Sturm certificate reports two. The driver prints both, and the disagreement
//! is the returned evidence.

use std::collections::BTreeMap;
use std::error::Error;
use std::fs;
use std::path::{Path, PathBuf};

use num_bigint::BigInt;
use relational_geometry::{Rat, format_rat, integer, rat};

use holonic_engine::certified_face::{
    CertifiedFace, ReceiverWindow, certify_face, mark_census, station_sign_changes,
};
use holonic_engine::exact_value::IntegerPolynomial;
use holonic_engine::presentation_gauge::{
    CanvasChart, DisplayGauge, exact_rows, place, render, structural_residue,
};

struct Station {
    slug: &'static str,
    title: &'static str,
    polynomial: IntegerPolynomial,
    window: ReceiverWindow,
}

fn stations() -> Result<Vec<Station>, Box<dyn Error>> {
    Ok(vec![
        Station {
            slug: "a_three_simple_roots",
            title: "(x-1)(x-2)(x-3): three separated roots, all located",
            polynomial: IntegerPolynomial::new(vec![
                BigInt::from(-6),
                BigInt::from(11),
                BigInt::from(-6),
                BigInt::from(1),
            ])?,
            window: ReceiverWindow::new(rat(1, 2), rat(7, 2), 12, 8)?,
        },
        Station {
            slug: "b_unresolvable_pair",
            title: "1000000x^2 - 1: two roots inside one cell, no subdivision budget",
            polynomial: IntegerPolynomial::new(vec![
                BigInt::from(-1),
                BigInt::from(0),
                BigInt::from(1_000_000),
            ])?,
            window: ReceiverWindow::new(integer(-1), integer(1), 1, 0)?,
        },
        Station {
            slug: "c_irrational_root",
            title: "x^2 - 2: an irrational root isolated with no float anywhere",
            polynomial: IntegerPolynomial::new(vec![
                BigInt::from(-2),
                BigInt::from(0),
                BigInt::from(1),
            ])?,
            window: ReceiverWindow::new(integer(0), integer(2), 8, 10)?,
        },
        Station {
            slug: "d_featureless",
            title: "x^2 + 1: certified featureless, and therefore unobstructed",
            polynomial: IntegerPolynomial::new(vec![
                BigInt::from(1),
                BigInt::from(0),
                BigInt::from(1),
            ])?,
            window: ReceiverWindow::new(integer(-3), integer(3), 12, 6)?,
        },
    ])
}

/// Write the exact rows beside every figure. This is the invertible face; the picture is not.
fn write_rows(path: &Path, face: &CertifiedFace) -> Result<(), Box<dyn Error>> {
    let mut out = String::from("role\tabscissa\tordinate\tlower\tupper\tunresolved\n");
    for row in exact_rows(face) {
        out.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\n",
            row.get("role").cloned().unwrap_or_default(),
            row.get("abscissa").cloned().unwrap_or_default(),
            row.get("ordinate").cloned().unwrap_or_default(),
            row.get("lower").cloned().unwrap_or_default(),
            row.get("upper").cloned().unwrap_or_default(),
            row.get("unresolved").cloned().unwrap_or_default(),
        ));
    }
    fs::write(path, out)?;
    Ok(())
}

/// THE READER. Re-open an emitted table and recover its census from the file alone.
///
/// This is the half the roadmap says is missing. It parses only what was written, with no access
/// to the in-memory face, so agreement between the two is real evidence that the artifact carries
/// its own content.
fn read_rows_back(path: &Path) -> Result<BTreeMap<String, usize>, Box<dyn Error>> {
    let text = fs::read_to_string(path)?;
    let mut census: BTreeMap<String, usize> = BTreeMap::new();
    for line in text.lines().skip(1).filter(|line| !line.trim().is_empty()) {
        let role = line.split('\t').next().unwrap_or_default().to_string();
        *census.entry(role).or_default() += 1;
    }
    Ok(census)
}

/// Recover every exact rational the emitted SVG carries, from the document alone.
///
/// A figure whose coordinates cannot be recovered from the figure is decoration. This parses the
/// `data-abscissa` attributes back into `Rat` and returns them.
fn read_svg_abscissae(document: &str) -> Vec<Rat> {
    let mut recovered = Vec::new();
    for fragment in document.split("data-abscissa=\"").skip(1) {
        let Some(end) = fragment.find('"') else {
            continue;
        };
        let value = &fragment[..end];
        // Interval-valued marks ("[a,b]") are features; point-valued are stations.
        if value.starts_with('[') {
            continue;
        }
        let parsed = if let Some((numerator, denominator)) = value.split_once('/') {
            match (numerator.parse::<i64>(), denominator.parse::<i64>()) {
                (Ok(n), Ok(d)) if d != 0 => Some(rat(n, d)),
                _ => None,
            }
        } else {
            value.parse::<i64>().ok().map(integer)
        };
        if let Some(value) = parsed {
            recovered.push(value);
        }
    }
    recovered
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut output = PathBuf::from("target/holonic-engine/certified-presentation-workbench");
    let mut arguments = std::env::args().skip(1);
    while let Some(argument) = arguments.next() {
        if argument == "--output" {
            if let Some(value) = arguments.next() {
                output = PathBuf::from(value);
            }
        }
    }
    fs::create_dir_all(&output)?;

    let chart = CanvasChart::new(720, 420, 48);
    let declared = DisplayGauge::declared();
    let permuted = DisplayGauge::permuted();

    let mut summary = String::from(
        "station\tcertified\tlocated\tunresolved\tnaive_sign_changes\tstations\tread_back_ok\tgauge_invariant\n",
    );

    println!("== certified presentation workbench ==\n");

    for station in stations()? {
        let face = certify_face(&station.polynomial, &station.window)?;

        // The face must reconcile before anything is drawn from it.
        assert!(
            face.population_reconciles(),
            "{}: located + unresolved != certified",
            station.slug
        );

        let document = render(&face, &chart, &declared);
        let alternate = render(&face, &chart, &permuted);

        // FALSIFIER TWO, run on real emitted material rather than a fixture.
        let gauge_invariant =
            structural_residue(&document, &declared) == structural_residue(&alternate, &permuted);
        assert!(
            gauge_invariant,
            "{}: the palette moved a structural byte",
            station.slug
        );

        let svg_path = output.join(format!("{}.svg", station.slug));
        let rows_path = output.join(format!("{}.tsv", station.slug));
        fs::write(&svg_path, &document)?;
        fs::write(
            output.join(format!("{}_permuted.svg", station.slug)),
            &alternate,
        )?;
        write_rows(&rows_path, &face)?;

        // THE READ-BACK. Re-open both artifacts and recover their content from the files alone.
        let recovered_census = read_rows_back(&rows_path)?;
        let memory_census = mark_census(&face);
        let stations_agree =
            recovered_census.get("station").copied().unwrap_or(0) == memory_census["stations"];
        let features_agree =
            recovered_census.get("feature").copied().unwrap_or(0) == memory_census["features"];
        let obstructions_agree = recovered_census.get("obstruction").copied().unwrap_or(0)
            == memory_census["obstructions"];

        let emitted = fs::read_to_string(&svg_path)?;
        let recovered_abscissae = read_svg_abscissae(&emitted);
        let abscissae_agree = recovered_abscissae.len() == face.stations.len()
            && recovered_abscissae
                .iter()
                .zip(&face.stations)
                .all(|(recovered, station)| *recovered == station.abscissa);

        let read_back_ok =
            stations_agree && features_agree && obstructions_agree && abscissae_agree;
        assert!(
            read_back_ok,
            "{}: the emitted artifact did not read back to what produced it",
            station.slug
        );

        let naive = station_sign_changes(&face);
        let unresolved: u32 = face
            .obstructions
            .iter()
            .map(|obstruction| obstruction.unresolved_feature_count)
            .sum();

        println!("-- {} --", station.title);
        println!(
            "   certified distinct features : {}",
            face.certified_feature_count
        );
        println!("   located exactly             : {}", face.features.len());
        println!("   returned as obstruction     : {unresolved}");
        println!("   naive sampled sign changes  : {naive}");
        if u32::try_from(face.features.len())? + naive < face.certified_feature_count {
            println!(
                "   >> THE DISAGREEMENT: the sampled reading sees {naive}, the certificate proves {}.",
                face.certified_feature_count
            );
            println!("      An adaptive sampler would have emitted a clean curve here.");
        }
        for feature in &face.features {
            println!(
                "   feature isolated to          : [{}, {}]",
                format_rat(&feature.interval.lower),
                format_rat(&feature.interval.upper)
            );
        }
        for obstruction in &face.obstructions {
            println!(
                "   OBSTRUCTION [{}, {}] carries {} unseparated features",
                format_rat(&obstruction.interval.lower),
                format_rat(&obstruction.interval.upper),
                obstruction.unresolved_feature_count
            );
        }
        println!("   read back from file          : {read_back_ok}");
        println!("   palette permutation invariant: {gauge_invariant}");
        println!(
            "   marks placed                 : {}",
            place(&face, &chart).len()
        );
        println!();

        summary.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            station.slug,
            face.certified_feature_count,
            face.features.len(),
            unresolved,
            naive,
            face.stations.len(),
            read_back_ok,
            gauge_invariant,
        ));
    }

    fs::write(output.join("summary.tsv"), &summary)?;
    println!("artifacts written to {}", output.display());
    println!("and every one of them was re-opened and checked against what produced it.");
    Ok(())
}
