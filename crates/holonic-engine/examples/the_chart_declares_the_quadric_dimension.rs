//! The chart declares the quadric dimension; the organ authors nothing.
//!
//! `field_atlas.rs` carried two authored levels:
//!
//! ```text
//!   const QUADRIC_COEFFICIENT_COUNT: usize = 10;
//!   const AFFINE_PHASE_COEFFICIENT_COUNT: usize = 4;
//! ```
//!
//! Ten is `C(n+2,2)` at `n = 3` and four is `n + 1` at `n = 3`, so both pinned
//! the ambient dimension while the names read as coefficient counts. This
//! driver runs the excision's orbit: one fixed body of oriented material, read
//! under several declared charts, with the difference exhibited rather than
//! argued.
//!
//! Run:
//!
//! ```text
//!   cargo run -p holonic-engine --example the_chart_declares_the_quadric_dimension
//! ```

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::{
    CausalFieldAtlasLaw, CausalFieldAtlasMount, CausalFieldEvent, CausalFieldStanding, EventId,
    ExactAffineVersionFiber, ExactEventLaw, ExactQuadric3, ExactRay, ExactTorus, FieldAtlasError,
    FieldChart, FieldChartAxis, FieldPhaseChannel, FieldReceiverQuery, FieldRegionId,
    FieldSupportStanding, ImplicitCellId, OrientedFieldSample, SourceTorusOccurrence,
};
use relational_geometry::{Rat, RatVec3, ReceiverId, integer};

fn rat(numerator: i64, denominator: i64) -> Rat {
    Rat::new(numerator.into(), denominator.into())
}

fn chart(axes: &[FieldChartAxis]) -> FieldChart {
    FieldChart::new(axes.to_vec()).unwrap()
}

/// Five exact rational points of the circle `x^2 + y^2 = 4` in the plane
/// `z = 0`, each carrying its own radial in-plane normal.
fn coplanar_circle_samples(region: FieldRegionId) -> Vec<OrientedFieldSample> {
    [
        RatVec3::from_i64(2, 0, 0),
        RatVec3::from_i64(-2, 0, 0),
        RatVec3::from_i64(0, 2, 0),
        RatVec3::from_i64(0, -2, 0),
        RatVec3::new(rat(6, 5), rat(8, 5), integer(0)),
    ]
    .into_iter()
    .map(|point| oriented(region, point.clone(), point))
    .collect()
}

/// The same circle turned into the plane `y = 0`, so the declared chart is not
/// a prefix of the ambient coordinate list.
fn coplanar_circle_samples_in_xz(region: FieldRegionId) -> Vec<OrientedFieldSample> {
    [
        RatVec3::from_i64(2, 0, 0),
        RatVec3::from_i64(-2, 0, 0),
        RatVec3::from_i64(0, 0, 2),
        RatVec3::from_i64(0, 0, -2),
        RatVec3::new(rat(6, 5), integer(0), rat(8, 5)),
    ]
    .into_iter()
    .map(|point| oriented(region, point.clone(), point))
    .collect()
}

fn oriented(region: FieldRegionId, point: RatVec3, normal: RatVec3) -> OrientedFieldSample {
    OrientedFieldSample {
        regions: BTreeSet::from([region]),
        point,
        normal,
        phase: BTreeMap::new(),
        receiver_contact: None,
    }
}

struct Reading {
    variables: usize,
    rank: usize,
    affine_dimension: usize,
    resolved: Option<ExactQuadric3>,
    exact_fibers: usize,
    open_fibers: usize,
    roots: usize,
    /// The chart every returned fiber of this receipt states for itself.
    testified_charts: BTreeSet<Vec<FieldChartAxis>>,
}

fn read_under(
    declared: Option<FieldChart>,
    region: FieldRegionId,
    samples: Vec<OrientedFieldSample>,
) -> Result<Reading, FieldAtlasError> {
    let law = CausalFieldAtlasLaw;
    let mut standing: CausalFieldStanding = law.initial_standing();
    if let Some(chart) = declared {
        standing.declare_region_chart(region, chart)?;
    }
    let event = CausalFieldEvent {
        event: EventId(1),
        chronology: 1,
        images: Vec::new(),
        oriented_samples: samples,
        source_tori: Vec::new(),
    };
    let standing = law.enact(&standing, &event)?.standing_after;
    let germ = standing
        .germs
        .values()
        .next()
        .expect("one region founds one germ");
    let FieldSupportStanding::Quadric {
        fiber, resolved, ..
    } = &germ.support
    else {
        panic!("an oriented sample founds a quadric germ");
    };
    let receipt = CausalFieldAtlasMount::new(8)?.receive(
        &standing,
        &FieldReceiverQuery {
            receiver: ReceiverId(1),
            ray: ExactRay {
                origin: RatVec3::from_i64(-5, 0, 0),
                direction: RatVec3::from_i64(1, 0, 0),
            },
        },
    )?;
    Ok(Reading {
        variables: fiber.variable_count(),
        rank: fiber.rank(),
        affine_dimension: fiber.affine_dimension(),
        resolved: resolved.clone(),
        exact_fibers: receipt.fibers.len(),
        open_fibers: receipt.open_fibers.len(),
        roots: receipt
            .fibers
            .iter()
            .map(|fiber| match fiber {
                holonic_engine::ExactFieldRayFiber::Quadric { fiber, .. } => fiber.roots.len(),
                holonic_engine::ExactFieldRayFiber::Torus { fiber, .. } => fiber.roots.len(),
            })
            .sum(),
        testified_charts: receipt
            .fibers
            .iter()
            .map(|fiber| match fiber {
                holonic_engine::ExactFieldRayFiber::Quadric { testimony, .. }
                | holonic_engine::ExactFieldRayFiber::Torus { testimony, .. } => {
                    testimony.chart.axes().to_vec()
                }
            })
            .chain(
                receipt
                    .open_fibers
                    .iter()
                    .map(|fiber| fiber.testimony.chart.axes().to_vec()),
            )
            .collect(),
    })
}

fn show(label: &str, reading: &Reading) {
    println!("  {label}");
    println!(
        "    fiber            variables {}  rank {}  affine dimension {}",
        reading.variables, reading.rank, reading.affine_dimension
    );
    match &reading.resolved {
        Some(quadric) => println!("    resolved         {}", coefficients(quadric)),
        None => println!("    resolved         OPEN — no single quadric is determined"),
    }
    println!(
        "    receiver receipt exact fibers {}  open fibers {}  certified roots {}",
        reading.exact_fibers, reading.open_fibers, reading.roots
    );
    println!(
        "    the receipt states its own chart: {:?}",
        reading.testified_charts
    );
}

fn coefficients(quadric: &ExactQuadric3) -> String {
    let names = [
        "x^2", "y^2", "z^2", "xy", "xz", "yz", "x", "y", "z", "1",
    ];
    quadric
        .coefficients
        .iter()
        .zip(names)
        .filter(|(coefficient, _)| **coefficient != Rat::from_integer(0.into()))
        .map(|(coefficient, name)| format!("{coefficient}·{name}"))
        .collect::<Vec<_>>()
        .join("  +  ")
}

fn coefficient_population_law() {
    println!("THE COEFFICIENT POPULATIONS, READ OFF THE DECLARED CHART");
    println!("  chart               n   C(n+2,2)   n+1   tangents   monomials");
    for axes in [
        vec![FieldChartAxis::X],
        vec![FieldChartAxis::X, FieldChartAxis::Y],
        vec![FieldChartAxis::X, FieldChartAxis::Z],
        vec![FieldChartAxis::X, FieldChartAxis::Y, FieldChartAxis::Z],
    ] {
        let chart = FieldChart::new(axes).unwrap();
        let monomials = chart.quadric_monomials();
        assert_eq!(
            monomials.len(),
            chart.quadric_coefficient_count(),
            "the enumerated monomials are exactly C(n+2,2)"
        );
        println!(
            "  {:<18}  {}   {:<8}   {:<3}   {:<8}   {}",
            format!("{:?}", chart.axes()),
            chart.dimension(),
            chart.quadric_coefficient_count(),
            chart.affine_coefficient_count(),
            chart.dimension() - 1,
            monomials
                .iter()
                .map(|monomial| format!("{monomial:?}"))
                .collect::<Vec<_>>()
                .join(" ")
                .replace("FieldQuadricMonomial::", "")
        );
    }
    println!();
}

fn the_orbit() {
    let region = FieldRegionId(1);
    println!("THE ORBIT — ONE BODY OF COPLANAR ORIENTED MATERIAL, SEVERAL DECLARED CHARTS");
    println!("  material: five exact rational points of x^2 + y^2 = 4 in the plane z = 0,");
    println!("            each carrying its radial in-plane normal.");
    println!();

    let ambient = read_under(None, region, coplanar_circle_samples(region)).unwrap();
    show(
        "undeclared region — read in the ambient chart (the pinned behaviour)",
        &ambient,
    );
    let declared_ambient = read_under(
        Some(FieldChart::ambient()),
        region,
        coplanar_circle_samples(region),
    )
    .unwrap();
    assert_eq!(declared_ambient.variables, ambient.variables);
    assert_eq!(declared_ambient.affine_dimension, ambient.affine_dimension);
    assert_eq!(declared_ambient.resolved, ambient.resolved);
    println!("    (an explicitly declared ambient chart returns the identical reading)");
    println!();

    let plane = read_under(
        Some(chart(&[FieldChartAxis::X, FieldChartAxis::Y])),
        region,
        coplanar_circle_samples(region),
    )
    .unwrap();
    show("region declares the chart [X, Y]", &plane);
    println!();

    println!(
        "  MOVEMENT: affine dimension {} -> {}, resolved {} -> {}, exact receiver fibers {} -> {}",
        ambient.affine_dimension,
        plane.affine_dimension,
        if ambient.resolved.is_some() {
            "yes"
        } else {
            "OPEN"
        },
        if plane.resolved.is_some() {
            "yes"
        } else {
            "OPEN"
        },
        ambient.exact_fibers,
        plane.exact_fibers,
    );
    println!(
        "  The level was deciding the answer: in the ambient chart the coplanar material leaves a"
    );
    println!(
        "  two-dimensional pencil (lambda*(x^2+y^2-4) + mu*z^2) that no further sample can collapse,"
    );
    println!("  so the support never resolves and the receiver only ever sees an open fiber.");
    println!();
}

fn the_chart_is_declared_not_a_prefix() {
    let region = FieldRegionId(4);
    println!("THE CHART IS DECLARED, NOT 'THE FIRST N AXES'");
    let reading = read_under(
        Some(chart(&[FieldChartAxis::X, FieldChartAxis::Z])),
        region,
        coplanar_circle_samples_in_xz(region),
    )
    .unwrap();
    show("the same circle turned into y = 0, chart [X, Z]", &reading);
    println!();
}

fn the_axis_order_is_a_frame_the_return_does_not_see() {
    let region = FieldRegionId(6);
    println!("TWO FRAMES ON ONE MATERIAL — THE DECLARED AXIS ORDER");
    let forward = read_under(
        Some(chart(&[FieldChartAxis::X, FieldChartAxis::Y])),
        region,
        coplanar_circle_samples(region),
    )
    .unwrap();
    let reversed = read_under(
        Some(chart(&[FieldChartAxis::Y, FieldChartAxis::X])),
        region,
        coplanar_circle_samples(region),
    )
    .unwrap();
    println!(
        "  [X, Y] fiber coordinates: {:?}",
        chart(&[FieldChartAxis::X, FieldChartAxis::Y])
            .quadric_monomials()
            .iter()
            .map(|monomial| format!("{monomial:?}").replace("FieldQuadricMonomial::", ""))
            .collect::<Vec<_>>()
    );
    println!(
        "  [Y, X] fiber coordinates: {:?}",
        chart(&[FieldChartAxis::Y, FieldChartAxis::X])
            .quadric_monomials()
            .iter()
            .map(|monomial| format!("{monomial:?}").replace("FieldQuadricMonomial::", ""))
            .collect::<Vec<_>>()
    );
    assert_ne!(
        chart(&[FieldChartAxis::X, FieldChartAxis::Y]).quadric_monomials(),
        chart(&[FieldChartAxis::Y, FieldChartAxis::X]).quadric_monomials(),
        "the two frames must genuinely differ, or this is not a gauge"
    );
    assert_eq!(
        forward.resolved, reversed.resolved,
        "the returned ambient support must not depend on the order the caller listed the axes"
    );
    println!(
        "  the two frames differ; the returned support is the same object: {}",
        coefficients(forward.resolved.as_ref().unwrap())
    );
    println!();
}

fn the_phase_law_has_the_same_orbit() {
    let law = CausalFieldAtlasLaw;
    let region = FieldRegionId(11);
    let channel = FieldPhaseChannel::Declared(1);
    println!("THE SECOND CONSTANT — THE AFFINE PHASE LAW, n + 1 COEFFICIENTS");
    println!("  material: the same five coplanar points, each carrying 3x + 5y + 7.");
    let reading = |declared: FieldChart| {
        let mut standing = law.initial_standing();
        standing.declare_region_chart(region, declared).unwrap();
        let mut samples = coplanar_circle_samples(region);
        for sample in &mut samples {
            let value =
                integer(3) * &sample.point.x + integer(5) * &sample.point.y + integer(7);
            sample.phase = BTreeMap::from([(channel, value)]);
        }
        let event = CausalFieldEvent {
            event: EventId(1),
            chronology: 1,
            images: Vec::new(),
            oriented_samples: samples,
            source_tori: Vec::new(),
        };
        let standing = law.enact(&standing, &event).unwrap().standing_after;
        let germ = standing.germs.values().next().unwrap();
        let phase = &germ.phases[&channel];
        (phase.fiber.variable_count(), phase.law.clone())
    };

    for (label, declared) in [
        ("ambient chart [X, Y, Z]", FieldChart::ambient()),
        (
            "declared chart [X, Y]",
            chart(&[FieldChartAxis::X, FieldChartAxis::Y]),
        ),
    ] {
        let (variables, resolved) = reading(declared);
        match resolved {
            Some(phase) => println!(
                "  {label:<24} fiber variables {variables}  ->  law over {:?} coefficients {:?} gradient {:?}",
                phase.chart().axes(),
                phase
                    .coefficients()
                    .iter()
                    .map(std::string::ToString::to_string)
                    .collect::<Vec<_>>(),
                (
                    phase.gradient().x.to_string(),
                    phase.gradient().y.to_string(),
                    phase.gradient().z.to_string()
                )
            ),
            None => println!(
                "  {label:<24} fiber variables {variables}  ->  OPEN, no law is determined"
            ),
        }
    }
    println!("  The coordinate the material never varies in cannot become a pivot, so the ambient");
    println!("  chart's fourth coefficient is never determined and the phase law stays open at");
    println!("  every receiver query. In the chart the material actually lives in it resolves.");
    println!();
}

fn the_one_axis_chart() {
    let region = FieldRegionId(3);
    println!("A ONE-COORDINATE CHART — n = 1, C(3,2) = 3 COEFFICIENTS, ZERO TANGENTS");
    let samples = vec![
        oriented(
            region,
            RatVec3::from_i64(2, 0, 0),
            RatVec3::from_i64(1, 0, 0),
        ),
        oriented(
            region,
            RatVec3::from_i64(-2, 0, 0),
            RatVec3::from_i64(-1, 0, 0),
        ),
    ];
    let reading = read_under(Some(chart(&[FieldChartAxis::X])), region, samples).unwrap();
    show("two oriented points, chart [X]", &reading);
    println!("  a normal in one coordinate has no tangents, so each observation contributes");
    println!("  exactly one row and two observations determine the binary quadratic.");
    println!();
}

fn the_refusals() {
    println!("THE REFUSALS, WITH BOTH ARMS");
    let region = FieldRegionId(5);
    let declared = chart(&[FieldChartAxis::X, FieldChartAxis::Y]);

    let refused = read_under(
        Some(declared.clone()),
        region,
        vec![oriented(
            region,
            RatVec3::from_i64(2, 0, 0),
            RatVec3::from_i64(0, 0, 1),
        )],
    );
    let admitted = read_under(
        Some(declared.clone()),
        region,
        vec![oriented(
            region,
            RatVec3::from_i64(2, 0, 0),
            RatVec3::from_i64(1, 0, 0),
        )],
    );
    println!("  same point (2,0,0), chart [X, Y]:");
    println!(
        "    normal (0,0,1) -> {}",
        match &refused {
            Err(error) => format!("{error}"),
            Ok(_) => "ADMITTED — the refusal did not fire".to_owned(),
        }
    );
    println!(
        "    normal (1,0,0) -> {}",
        match &admitted {
            Ok(reading) => format!(
                "admitted, fiber variables {} affine dimension {}",
                reading.variables, reading.affine_dimension
            ),
            Err(error) => format!("REFUSED — {error}"),
        }
    );
    assert!(matches!(
        refused,
        Err(FieldAtlasError::SampleNormalOutsideChart { .. })
    ));
    assert!(admitted.is_ok());

    let law = CausalFieldAtlasLaw;
    let torus_region = FieldRegionId(2);
    let mut standing = law.initial_standing();
    standing
        .declare_region_chart(torus_region, declared.clone())
        .unwrap();
    let torus_event = CausalFieldEvent {
        event: EventId(1),
        chronology: 1,
        images: Vec::new(),
        oriented_samples: Vec::new(),
        source_tori: vec![SourceTorusOccurrence {
            region: torus_region,
            torus: ExactTorus::new(
                ImplicitCellId(1),
                EventId(1),
                RatVec3::zero(),
                RatVec3::from_i64(0, 0, 1),
                integer(3),
                integer(1),
            )
            .unwrap(),
            phases: BTreeMap::new(),
        }],
    };
    println!(
        "  a source torus in a region declaring [X, Y] -> {}",
        match law.enact(&standing, &torus_event) {
            Err(error) => format!("{error}"),
            Ok(_) => "ADMITTED — the carrier boundary did not fire".to_owned(),
        }
    );
    let mut ambient_standing = law.initial_standing();
    ambient_standing
        .declare_region_chart(torus_region, FieldChart::ambient())
        .unwrap();
    println!(
        "  the same source torus in a region declaring the ambient chart -> {}",
        match law.enact(&ambient_standing, &torus_event) {
            Ok(successor) => format!(
                "admitted, {} germ",
                successor.standing_after.germs.len()
            ),
            Err(error) => format!("REFUSED — {error}"),
        }
    );
    println!();
}

fn the_wall() {
    println!("THE WALL");
    println!("  The declared chart dimension ranges over 1..=3 and nothing above 3 can be named.");
    println!("  Two carriers fix that ceiling, and neither is in this module:");
    println!(
        "    relational_geometry::RatVec3   (crates/relational-geometry/src/exact.rs:298) — the"
    );
    println!("      sample, point and normal carrier, three named fields x, y, z.");
    println!(
        "    ExactQuadric3::coefficients: [Rat; 10]  (crates/holonic-engine/src/implicit.rs:39) —"
    );
    println!("      the resolved support carrier, with a fixed 3x3 hessian and a 3-term ray");
    println!("      restriction.");
    println!("  Everything between them is now dimension-general: the coefficient fiber");
    println!("  (ExactAffineVersionFiber, any positive variable count), the monomial enumeration,");
    println!("  the gradient rows, the tangent basis and the free-coordinate resolution.");
    println!(
        "  A chart of dimension n < 3 resolves in C(n+2,2) coefficients and is lifted into the"
    );
    println!("  ambient carrier as the cylinder over its quadric — an exact inclusion, not a pad.");
    println!();
    let ambient = FieldChart::ambient();
    let fiber = ExactAffineVersionFiber::new(ambient.quadric_coefficient_count()).unwrap();
    println!(
        "  the fiber machinery itself is agnostic: ExactAffineVersionFiber::new({}) -> {} variables,",
        ambient.quadric_coefficient_count(),
        fiber.variable_count()
    );
    println!(
        "  and ExactAffineVersionFiber::new(15) -> {} variables (a quadric in four coordinates),",
        ExactAffineVersionFiber::new(15).unwrap().variable_count()
    );
    println!("  which no sample carrier in this tree can feed.");
}

fn main() {
    coefficient_population_law();
    the_orbit();
    the_chart_is_declared_not_a_prefix();
    the_axis_order_is_a_frame_the_return_does_not_see();
    the_phase_law_has_the_same_orbit();
    the_one_axis_chart();
    the_refusals();
    the_wall();
}
