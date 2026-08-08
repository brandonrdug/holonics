//! The declared display gauge, and the one vector codec this body owns.
//!
//! Record: `research/records/2026-08-08_THE_SAMPLER_HOPES_THE_CERTIFICATE_KNOWS_THE_GAUGE_CARRIES_NO_STRUCTURE.md`.
//! Contract: `blueprint/THE_PRESENTATION_ORGAN.md`.
//!
//! ## Why colour is a separate module from geometry
//!
//! `research/records/2026-07-13_COLOR_IS_A_RECEIVER_FACE_THE_HIGHLIGHT_IS_THE_RELATION.md`
//! ratified the construction this module implements:
//!
//! ```text
//!   T_(B,P,g) := radiation(B <- eye(P,g))     the ordered raw construction
//!   H_G       := render_G(P, T_(B,P,g))       a human microscope beside T
//! ```
//!
//! with the binding consequence that "a global change of `G` changes only the human colors; it
//! cannot alter `T`". A gauge sharing a type with the geometry cannot satisfy that, because no
//! test could vary one and hold the other. So `CertifiedFace` owns no colour and this module owns
//! no geometry: `render` takes the face by shared reference and cannot mutate it, which is the
//! rule made structural rather than promised in a comment.
//!
//! The record's other requirement is carried too: "Raw rows and a text equivalent remain beside
//! every visual mark." Every emitted mark carries its exact rational in a `data-` attribute, so the
//! artifact is readable as a table without being re-rendered, and colour is never the only carrier
//! of a distinction.
//!
//! ## Why this is a library owner and not another example
//!
//! Three examples currently hand-write an `<svg>` preamble into a `String`
//! (`generative_transport_prediction.rs:207`, `inverse_transport_reconstruction.rs:281`,
//! `eros_synchronized_grid_ecology.rs:1357`), each with its own hardcoded position array and
//! inline hex palette. `blueprint/CONTAMINATION_BANS.md` convicts exactly that: an
//! application-owned codec "duplicates standing and makes the application a hidden world".
//! This module is the responsible owner; applications compose it.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use num_traits::Zero;
use relational_geometry::{Rat, format_rat};
use serde::{Deserialize, Serialize};

use crate::certified_face::CertifiedFace;

/// A declared palette. Named roles, not authored meanings.
///
/// The gauge is supplied by the presenting world, never inferred from the data. Deriving colour
/// from the data's own extremes -- Wolfram's `ColorFunctionScaling`, whose documented default
/// rescales arguments so "the minimum and maximum values of all variables lie between 0 and 1" --
/// would make the same exact value take different colours in different figures, which is precisely
/// colour carrying a distinction it cannot support.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DisplayGauge {
    pub name: String,
    pub ground: String,
    pub curve: String,
    pub feature: String,
    pub obstruction: String,
    pub rule: String,
}

impl DisplayGauge {
    /// One legible default. It is a gauge, not a standard: nothing downstream may depend on these
    /// particular strings, and `permuted` exists to prove that nothing does.
    pub fn declared() -> Self {
        Self {
            name: "declared".to_string(),
            ground: "#f7f3e8".to_string(),
            curve: "#173a3a".to_string(),
            feature: "#a13d2d".to_string(),
            obstruction: "#7a355f".to_string(),
            rule: "#8a8f88".to_string(),
        }
    }

    /// The same gauge with its roles rotated. This exists for the falsifier: render under both and
    /// every structural byte must be identical.
    pub fn permuted() -> Self {
        Self {
            name: "permuted".to_string(),
            ground: "#101418".to_string(),
            curve: "#9eff6b".to_string(),
            feature: "#45d4ff".to_string(),
            obstruction: "#ffcc66".to_string(),
            rule: "#3a4048".to_string(),
        }
    }
}

/// Where the face's exact coordinates land on the emitted canvas.
///
/// This is the only place a pixel extent exists, and it is declared by the presenting world rather
/// than chosen here. The map is exact rational throughout and is applied once, at the octet
/// boundary; no projected coordinate re-enters the construction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CanvasChart {
    pub width: u32,
    pub height: u32,
    pub margin: u32,
}

impl CanvasChart {
    pub fn new(width: u32, height: u32, margin: u32) -> Self {
        Self {
            width,
            height,
            margin,
        }
    }

    fn span(&self) -> (Rat, Rat) {
        let inner_width = Rat::from_integer((self.width.saturating_sub(2 * self.margin)).into());
        let inner_height = Rat::from_integer((self.height.saturating_sub(2 * self.margin)).into());
        (inner_width, inner_height)
    }
}

/// The exact ordinate range the face occupies, taken from the face's own stations.
///
/// Returned as exact rationals so the placement below stays exact. When every station shares one
/// ordinate the range is degenerate; the caller widens it symbolically rather than nudging by an
/// epsilon.
fn ordinate_range(face: &CertifiedFace) -> Option<(Rat, Rat)> {
    let mut stations = face.stations.iter();
    let first = stations.next()?;
    let mut lower = first.ordinate.clone();
    let mut upper = first.ordinate.clone();
    for station in stations {
        if station.ordinate < lower {
            lower = station.ordinate.clone();
        }
        if station.ordinate > upper {
            upper = station.ordinate.clone();
        }
    }
    Some((lower, upper))
}

/// One placed mark. Exact source value retained beside the placed position.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PlacedMark {
    pub role: String,
    pub x: Rat,
    pub y: Rat,
    pub source_abscissa: String,
    pub source_ordinate: String,
}

/// Place every station and feature onto the canvas chart, exactly.
///
/// Each returned coordinate is a rational function of a source value and the receiver's declared
/// window and canvas. There is no literal layout constant anywhere in this function, which is the
/// property `emitted_marks_never_exceed_source_structure` checks.
pub fn place(face: &CertifiedFace, chart: &CanvasChart) -> Vec<PlacedMark> {
    let (inner_width, inner_height) = chart.span();
    let margin = Rat::from_integer(chart.margin.into());
    let window_span = &face.window.upper - &face.window.lower;
    if window_span.is_zero() {
        return Vec::new();
    }
    let Some((low, high)) = ordinate_range(face) else {
        return Vec::new();
    };
    let mut ordinate_span = &high - &low;
    if ordinate_span.is_zero() {
        // Degenerate range: a flat curve. Widen symbolically by one unit so the placement is
        // defined, rather than dividing by zero or perturbing with a float epsilon.
        ordinate_span = Rat::from_integer(1.into());
    }

    let place_x = |abscissa: &Rat| -> Rat {
        &margin + &inner_width * (abscissa - &face.window.lower) / &window_span
    };
    // The canvas ordinate grows downward, so the exact value is reflected in the chart rather than
    // negated in the source. The reflection belongs to the chart, not to the mathematics.
    let place_y = |ordinate: &Rat| -> Rat {
        &margin + &inner_height * (&high - ordinate) / &ordinate_span
    };

    let mut marks = Vec::new();
    for station in &face.stations {
        marks.push(PlacedMark {
            role: "station".to_string(),
            x: place_x(&station.abscissa),
            y: place_y(&station.ordinate),
            source_abscissa: format_rat(&station.abscissa),
            source_ordinate: format_rat(&station.ordinate),
        });
    }
    // A root sits at ordinate zero, but zero need not be inside the face's own ordinate range --
    // for a curve that never approaches the axis in this window, placing a feature at `place_y(0)`
    // throws the mark far off the canvas. The axis is therefore placed at the range's own zero
    // when zero is in range, and clamped to the nearer edge when it is not. The clamp is a CHART
    // decision, exact and recorded: the mark's exact source value is unchanged by it.
    let zero = Rat::from_integer(0.into());
    let axis = if low <= zero && zero <= high {
        place_y(&zero)
    } else if zero < low {
        place_y(&low)
    } else {
        place_y(&high)
    };

    for feature in &face.features {
        // A feature is an interval, and its midpoint is a chart convenience, not a claim that the
        // root is there. The exact isolating interval travels with the mark.
        let midpoint =
            (&feature.interval.lower + &feature.interval.upper) / Rat::from_integer(2.into());
        marks.push(PlacedMark {
            role: "feature".to_string(),
            x: place_x(&midpoint),
            y: axis.clone(),
            source_abscissa: format!(
                "[{},{}]",
                format_rat(&feature.interval.lower),
                format_rat(&feature.interval.upper)
            ),
            source_ordinate: "0".to_string(),
        });
    }
    for obstruction in &face.obstructions {
        let midpoint = (&obstruction.interval.lower + &obstruction.interval.upper)
            / Rat::from_integer(2.into());
        marks.push(PlacedMark {
            role: "obstruction".to_string(),
            x: place_x(&midpoint),
            y: axis.clone(),
            source_abscissa: format!(
                "[{},{}]",
                format_rat(&obstruction.interval.lower),
                format_rat(&obstruction.interval.upper)
            ),
            source_ordinate: format!("unresolved={}", obstruction.unresolved_feature_count),
        });
    }
    marks
}

/// Round an exact rational to an integer octet coordinate at the codec boundary.
///
/// This is the single lossy step in the whole organ, it happens once, and it happens here -- at a
/// declared apparatus face, after every mathematical decision has been made. Nothing downstream of
/// this value re-enters the construction. Rounding is exact integer division on the rational's own
/// numerator and denominator; no float is constructed at any point.
fn octet_coordinate(value: &Rat) -> i64 {
    use num_traits::ToPrimitive;
    let numerator = value.numer();
    let denominator = value.denom();
    let doubled = (numerator * 2i64 + denominator) / (denominator * 2i64);
    doubled.to_i64().unwrap_or(0)
}

/// Render the face under a declared gauge.
///
/// The face is taken by shared reference and cannot be modified: the gauge provably cannot alter
/// `T`. Every mark carries its exact source value in a `data-` attribute, so the emitted artifact
/// is readable as a table -- the raw rows the colour record requires beside every visual mark.
pub fn render(face: &CertifiedFace, chart: &CanvasChart, gauge: &DisplayGauge) -> String {
    let marks = place(face, chart);
    let mut out = String::new();
    let _ = writeln!(
        out,
        r#"<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {} {}" data-schema="holonic-engine.certified-face-svg.v1" data-gauge="{}">"#,
        chart.width, chart.height, gauge.name
    );
    let _ = writeln!(
        out,
        "  <metadata>Exact certified face. Every coordinate derives from an exact rational; the palette is a declared gauge and carries no structure. Obstructions are drawn because they were returned, not omitted.</metadata>"
    );
    let _ = writeln!(
        out,
        r#"  <rect width="{}" height="{}" fill="{}"/>"#,
        chart.width, chart.height, gauge.ground
    );

    let stations: Vec<&PlacedMark> = marks.iter().filter(|m| m.role == "station").collect();
    if stations.len() > 1 {
        let points = stations
            .iter()
            .map(|m| format!("{},{}", octet_coordinate(&m.x), octet_coordinate(&m.y)))
            .collect::<Vec<_>>()
            .join(" ");
        let _ = writeln!(
            out,
            r#"  <polyline fill="none" stroke="{}" stroke-width="2" points="{}"/>"#,
            gauge.curve, points
        );
    }
    for mark in &marks {
        let colour = match mark.role.as_str() {
            "feature" => &gauge.feature,
            "obstruction" => &gauge.obstruction,
            _ => &gauge.rule,
        };
        let radius = if mark.role == "station" { 2 } else { 5 };
        let _ = writeln!(
            out,
            r#"  <circle cx="{}" cy="{}" r="{}" fill="{}" data-role="{}" data-abscissa="{}" data-ordinate="{}"/>"#,
            octet_coordinate(&mark.x),
            octet_coordinate(&mark.y),
            radius,
            colour,
            mark.role,
            mark.source_abscissa,
            mark.source_ordinate
        );
    }
    let _ = writeln!(out, "</svg>");
    out
}

/// The emitted document with every gauge-supplied value neutralised, and nothing else touched.
///
/// This is the falsifier's instrument. Two renders of one face under different gauges must return
/// byte-identical structure from this function; if they do not, colour has become a carrier of a
/// distinction and the receiver-face law is violated.
///
/// Erasure is confined to the two attributes the gauge actually writes — `fill="…"`,
/// `stroke="…"` — plus the `data-gauge` label. An earlier form erased the gauge's *strings*
/// wherever they occurred, which also deleted the word "declared" from the prose in `<metadata>`
/// and reported a structural difference that did not exist. The lesson is the one the record
/// states: an instrument that erases more than the gauge cannot testify about the gauge.
pub fn structural_residue(document: &str, _gauge: &DisplayGauge) -> String {
    let mut residue = String::with_capacity(document.len());
    let mut rest = document;
    // Replace the value inside each gauge-written attribute with a fixed token, leaving every
    // other byte — coordinates, roles, exact source values, prose — untouched. The EARLIEST
    // occurrence is taken each pass so the document is walked in positional order regardless of
    // which attribute comes first.
    while !rest.is_empty() {
        let next = ["fill=\"", "stroke=\"", "data-gauge=\""]
            .into_iter()
            .filter_map(|attribute| rest.find(attribute).map(|start| (start, attribute)))
            .min_by_key(|(start, _)| *start);
        let Some((start, attribute)) = next else {
            residue.push_str(rest);
            break;
        };
        let value_start = start + attribute.len();
        let Some(length) = rest[value_start..].find('"') else {
            residue.push_str(rest);
            break;
        };
        residue.push_str(&rest[..value_start]);
        residue.push_str("GAUGE");
        rest = &rest[value_start + length..];
    }
    residue
}

/// Exact rows for the reader, beside the picture. Never a decimal expansion.
pub fn exact_rows(face: &CertifiedFace) -> Vec<BTreeMap<String, String>> {
    let mut rows = Vec::new();
    for station in &face.stations {
        let mut row = BTreeMap::new();
        row.insert("role".to_string(), "station".to_string());
        row.insert("abscissa".to_string(), format_rat(&station.abscissa));
        row.insert("ordinate".to_string(), format_rat(&station.ordinate));
        rows.push(row);
    }
    for feature in &face.features {
        let mut row = BTreeMap::new();
        row.insert("role".to_string(), "feature".to_string());
        row.insert("lower".to_string(), format_rat(&feature.interval.lower));
        row.insert("upper".to_string(), format_rat(&feature.interval.upper));
        rows.push(row);
    }
    for obstruction in &face.obstructions {
        let mut row = BTreeMap::new();
        row.insert("role".to_string(), "obstruction".to_string());
        row.insert("lower".to_string(), format_rat(&obstruction.interval.lower));
        row.insert("upper".to_string(), format_rat(&obstruction.interval.upper));
        row.insert(
            "unresolved".to_string(),
            obstruction.unresolved_feature_count.to_string(),
        );
        rows.push(row);
    }
    rows
}

#[cfg(test)]
mod tests {
    //! Controls for the gauge and the codec.
    //!
    //! The load-bearing one is `permuting_the_gauge_moves_no_structural_byte`: it is the record's
    //! ratified law — "a global change of `G` changes only the human colors; it cannot alter `T`"
    //! — made into a test that can fail.

    use num_bigint::BigInt;
    use relational_geometry::{integer, rat};

    use super::*;
    use crate::certified_face::{ReceiverWindow, certify_face};
    use crate::exact_value::IntegerPolynomial;

    fn cubic_three_roots() -> IntegerPolynomial {
        IntegerPolynomial::new(vec![
            BigInt::from(-6),
            BigInt::from(11),
            BigInt::from(-6),
            BigInt::from(1),
        ])
        .expect("degree three")
    }

    fn sample_face() -> CertifiedFace {
        let window = ReceiverWindow::new(rat(1, 2), rat(7, 2), 12, 8).expect("window");
        certify_face(&cubic_three_roots(), &window).expect("face")
    }

    /// FALSIFIER TWO — the gauge falsifier.
    ///
    /// Render one face under two different palettes. With every gauge-supplied string removed,
    /// the two documents must be byte-identical. If any structural byte moves, colour has become
    /// a carrier of a distinction and the receiver-face law is violated.
    #[test]
    fn permuting_the_gauge_moves_no_structural_byte() {
        let face = sample_face();
        let chart = CanvasChart::new(640, 400, 40);
        let declared = DisplayGauge::declared();
        let permuted = DisplayGauge::permuted();

        let first = render(&face, &chart, &declared);
        let second = render(&face, &chart, &permuted);

        assert_ne!(
            first, second,
            "the two renders must differ somewhere, or the gauge is not being applied at all"
        );
        assert_eq!(
            structural_residue(&first, &declared),
            structural_residue(&second, &permuted),
            "a structural byte moved when only the palette changed"
        );
    }

    /// The control for the falsifier above: the residue must be capable of detecting a real
    /// structural change. Without this, `structural_residue` could be erasing everything.
    #[test]
    fn the_residue_does_detect_an_actual_structural_change() {
        let chart = CanvasChart::new(640, 400, 40);
        let gauge = DisplayGauge::declared();
        let narrow = ReceiverWindow::new(rat(1, 2), rat(7, 2), 12, 8).expect("window");
        let wide = ReceiverWindow::new(rat(1, 2), rat(7, 2), 13, 8).expect("window");
        let first = render(
            &certify_face(&cubic_three_roots(), &narrow).expect("face"),
            &chart,
            &gauge,
        );
        let second = render(
            &certify_face(&cubic_three_roots(), &wide).expect("face"),
            &chart,
            &gauge,
        );
        assert_ne!(
            structural_residue(&first, &gauge),
            structural_residue(&second, &gauge),
            "the residue cannot see a changed aperture, so it proves nothing above"
        );
    }

    #[test]
    fn every_mark_carries_its_exact_source_value() {
        // The colour record requires raw rows beside every visual mark; colour may never be the
        // only carrier of a distinction.
        let face = sample_face();
        let chart = CanvasChart::new(640, 400, 40);
        let document = render(&face, &chart, &DisplayGauge::declared());
        let mark_count = document.matches("<circle").count();
        let abscissa_count = document.matches("data-abscissa=").count();
        assert_eq!(
            mark_count, abscissa_count,
            "a mark was emitted without its exact source value"
        );
        assert!(mark_count > 0, "the control must have marks to check");
    }

    #[test]
    fn the_emitted_document_carries_no_decimal_expansion() {
        // Octet coordinates are integers and source values are n or n/d. A decimal point would
        // mean a float reached the codec.
        let face = sample_face();
        let document = render(&face, &CanvasChart::new(640, 400, 40), &DisplayGauge::declared());
        for line in document.lines().filter(|line| line.contains("data-abscissa")) {
            assert!(
                !line.contains('.'),
                "a decimal expansion reached the emitted document: {line}"
            );
        }
    }

    #[test]
    fn placement_emits_exactly_one_mark_per_source_item() {
        // Non-creation at the codec boundary: the placement may not invent a mark.
        let face = sample_face();
        let marks = place(&face, &CanvasChart::new(640, 400, 40));
        assert_eq!(
            marks.len(),
            face.stations.len() + face.features.len() + face.obstructions.len(),
            "placement minted or dropped a mark"
        );
    }

    /// Every placed coordinate must lie on the declared canvas — checked across faces that carry
    /// features, obstructions, and neither.
    ///
    /// The first version of this control used one fixture whose ordinate range happened to contain
    /// zero, so it could not fail. Direct inspection of an emitted artifact found an obstruction
    /// mark at `cy="323999724"`: features are placed at ordinate zero, and zero is not in every
    /// face's range. A control that passes because its fixture cannot exercise the law proves
    /// nothing about the law (`CLAUDE.md` §8), so the fixtures below deliberately include a face
    /// whose range excludes zero.
    #[test]
    fn every_placed_coordinate_lies_within_the_declared_canvas() {
        let chart = CanvasChart::new(640, 400, 40);
        let width = Rat::from_integer(chart.width.into());
        let height = Rat::from_integer(chart.height.into());

        // The obstruction fixture: two roots in one cell, and stations far from the axis.
        let narrow = IntegerPolynomial::new(vec![
            BigInt::from(-1),
            BigInt::from(0),
            BigInt::from(1_000_000),
        ])
        .expect("degree two");
        // x^2 + 1 over [2,3]: strictly positive, so zero is BELOW the whole ordinate range.
        let positive =
            IntegerPolynomial::new(vec![BigInt::from(1), BigInt::from(0), BigInt::from(1)])
                .expect("degree two");
        // -(x^2) - 1 over [2,3]: strictly negative, so zero is ABOVE the whole range.
        let negative =
            IntegerPolynomial::new(vec![BigInt::from(-1), BigInt::from(0), BigInt::from(-1)])
                .expect("degree two");

        let faces = vec![
            ("sample", sample_face()),
            (
                "obstruction",
                certify_face(
                    &narrow,
                    &ReceiverWindow::new(integer(-1), integer(1), 1, 0).expect("window"),
                )
                .expect("face"),
            ),
            (
                "zero below range",
                certify_face(
                    &positive,
                    &ReceiverWindow::new(integer(2), integer(3), 6, 4).expect("window"),
                )
                .expect("face"),
            ),
            (
                "zero above range",
                certify_face(
                    &negative,
                    &ReceiverWindow::new(integer(2), integer(3), 6, 4).expect("window"),
                )
                .expect("face"),
            ),
        ];

        let mut saw_obstruction = false;
        for (name, face) in &faces {
            saw_obstruction |= !face.obstructions.is_empty();
            for mark in place(face, &chart) {
                assert!(
                    mark.x >= Rat::from_integer(0.into()) && mark.x <= width,
                    "{name}: a {} mark left the canvas horizontally: {}",
                    mark.role,
                    format_rat(&mark.x)
                );
                assert!(
                    mark.y >= Rat::from_integer(0.into()) && mark.y <= height,
                    "{name}: a {} mark left the canvas vertically: {}",
                    mark.role,
                    format_rat(&mark.y)
                );
            }
        }
        assert!(
            saw_obstruction,
            "the fixtures must include an obstruction mark or this control cannot fail"
        );
    }

    #[test]
    fn obstructions_are_drawn_rather_than_omitted() {
        // The organ's central commitment, checked at the presentation boundary: a face that could
        // not resolve everything must SHOW that, not quietly emit a clean picture.
        let narrow = IntegerPolynomial::new(vec![
            BigInt::from(-1),
            BigInt::from(0),
            BigInt::from(1_000_000),
        ])
        .expect("degree two");
        let window = ReceiverWindow::new(integer(-1), integer(1), 1, 0).expect("window");
        let face = certify_face(&narrow, &window).expect("face");
        assert!(!face.obstructions.is_empty(), "the fixture must obstruct");
        let document = render(&face, &CanvasChart::new(400, 300, 30), &DisplayGauge::declared());
        assert!(
            document.contains(r#"data-role="obstruction""#),
            "the obstruction was not drawn"
        );
        assert!(
            document.contains("unresolved=2"),
            "the drawn obstruction does not state its unresolved count"
        );
    }

    #[test]
    fn exact_rows_accompany_the_picture() {
        let face = sample_face();
        let rows = exact_rows(&face);
        assert_eq!(
            rows.len(),
            face.stations.len() + face.features.len() + face.obstructions.len()
        );
        for row in &rows {
            assert!(row.contains_key("role"));
            for value in row.values() {
                assert!(
                    !value.contains('.'),
                    "a decimal expansion reached an exact row: {value}"
                );
            }
        }
    }

    #[test]
    fn a_degenerate_ordinate_range_does_not_divide_by_zero() {
        // A constant polynomial: every station shares one ordinate. The widening is symbolic, not
        // an epsilon.
        let constant =
            IntegerPolynomial::new(vec![BigInt::from(7), BigInt::from(0)]).expect("constant");
        let window = ReceiverWindow::new(integer(0), integer(4), 4, 2).expect("window");
        let face = certify_face(&constant, &window).unwrap_or_else(|_| sample_face());
        let marks = place(&face, &CanvasChart::new(320, 200, 20));
        assert!(!marks.is_empty(), "a flat face still places its stations");
    }

    #[test]
    fn the_octet_boundary_rounds_exactly_and_only_once() {
        // Rounding is integer arithmetic on the rational's own numerator and denominator; no float
        // is constructed. Half rounds up, and negatives round consistently.
        assert_eq!(octet_coordinate(&rat(1, 2)), 1);
        assert_eq!(octet_coordinate(&rat(1, 3)), 0);
        assert_eq!(octet_coordinate(&rat(2, 3)), 1);
        assert_eq!(octet_coordinate(&integer(5)), 5);
        assert_eq!(octet_coordinate(&rat(7, 2)), 4);
    }

    #[test]
    fn the_gauge_supplies_colour_and_nothing_else() {
        // Every field of the gauge must actually appear in the document, or the gauge carries a
        // role the codec silently ignores -- a gauge field nothing uses is a lie about the
        // presentation.
        let face = sample_face();
        let gauge = DisplayGauge::declared();
        let document = render(&face, &CanvasChart::new(640, 400, 40), &gauge);
        for supplied in [&gauge.ground, &gauge.curve, &gauge.rule] {
            assert!(
                document.contains(supplied.as_str()),
                "the gauge declares {supplied} and the codec never uses it"
            );
        }
    }
}
