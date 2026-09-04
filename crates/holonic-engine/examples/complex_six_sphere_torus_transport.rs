//! The geometric four-torus fibre is transported around the three special base loops and received.
//!
//! This is a bounded receiver experiment over the finite algebra already checked in
//! `SixSphereMonodromy.lean`.  Its source occurrence is a four-dimensional geometric torus
//! sample `(S^1)^4`, not the engine's three-dimensional `ExactTorus`.  Four exact rational phase
//! circles carry the rank-four dual lattice.  The paper's `A1`, `A2`, and `M0` matrices transport
//! that lattice around the order-three, order-four, and cusp loops.  Several exact dimensional
//! receivers then expose different two-dimensional faces of the same source graph; a perspective
//! receiver and raster membrane consume those faces only after all source incidence is fixed.
//!
//! Truth status: `[established-bounded; implemented-exact]` for this finite sampled transport
//! occurrence and its exact receiver receipts; `[proved-derived; formal-checked]` for the matrix
//! identities copied from the named Lean files; `[open]` for the analytic period family, special
//! fillings, gluing, and identification of the completed body with `S^6`.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fs::{File, create_dir_all, write};
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};

use holonic_engine::{
    CausalChain, CoordinateCarrierId, CoordinateCarrierKind, CoordinateGermId, DimensionalAxis,
    DimensionalAxisId, DimensionalCarrierDisposition, DimensionalGermDisposition,
    DimensionalReceiverAtlas, DimensionalReceiverDeed, DimensionalReceiverFounding,
    DimensionalReceiverRequest, DimensionalSliceReceipt, DisplayFace, EventId,
    ExactComplexAxisPair, ExactCoordinateCarrier, ExactCoordinateGerm, ExactDimensionalSource,
    ExactSliceConstraint, ExactSliceCovector, GradedCausalComplex, Rgb8,
};
use image::{Rgb, RgbImage};
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use relational_geometry::{ProjectionLaw, Rat, RatVec3, ReceiverId, project_receiver_point};

const DEFAULT_OUT: &str = ".local/artifacts/complex-s6-torus-transport";
const EXTENT: i64 = 4;
const WIDTH: u32 = 1600;
const HEIGHT: u32 = 1100;

const BASE_STAGE: DimensionalAxisId = DimensionalAxisId(1);
const BASE_BRANCH: DimensionalAxisId = DimensionalAxisId(2);
const PHASE_AXES: [(DimensionalAxisId, DimensionalAxisId); 4] = [
    (DimensionalAxisId(10), DimensionalAxisId(11)),
    (DimensionalAxisId(12), DimensionalAxisId(13)),
    (DimensionalAxisId(14), DimensionalAxisId(15)),
    (DimensionalAxisId(16), DimensionalAxisId(17)),
];

type Matrix4 = [[i64; 4]; 4];
type Phase = [i64; 4];

const IDENTITY: Matrix4 = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]];

// Dual lattice actions from SixSphereMonodromy.lean.
const A1: Matrix4 = [[1, 0, 0, 0], [6, 0, 1, 0], [-6, -1, -1, 0], [-2, 1, 0, 1]];
const A2: Matrix4 = [[1, 0, 0, 0], [0, 0, -1, 0], [-6, 1, 0, 0], [3, 0, 1, 1]];
const M0: Matrix4 = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 1, 1, 0], [-1, 0, 0, 1]];

#[derive(Clone, Copy)]
struct SpecialLoop {
    name: &'static str,
    branch: i64,
    monodromy: Matrix4,
    last_stage: u32,
    closes: bool,
}

const LOOPS: [SpecialLoop; 3] = [
    SpecialLoop {
        name: "p1-order-three",
        branch: -1,
        monodromy: A1,
        last_stage: 3,
        closes: true,
    },
    SpecialLoop {
        name: "p2-order-four",
        branch: 0,
        monodromy: A2,
        last_stage: 4,
        closes: true,
    },
    SpecialLoop {
        name: "p0-unipotent-cusp",
        branch: 1,
        monodromy: M0,
        last_stage: 3,
        closes: false,
    },
];

#[derive(Default)]
struct SourceBuild {
    cells: BTreeMap<(usize, u32, Phase), holonic_engine::CausalCellId>,
    germs: BTreeMap<(usize, u32, Phase), CoordinateGermId>,
}

fn rat(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn event_set(event: EventId) -> BTreeSet<EventId> {
    BTreeSet::from([event])
}

fn matrix_multiply(left: Matrix4, right: Matrix4) -> Matrix4 {
    let mut product = [[0_i64; 4]; 4];
    for row in 0..4 {
        for column in 0..4 {
            product[row][column] = (0..4)
                .map(|middle| left[row][middle] * right[middle][column])
                .sum();
        }
    }
    product
}

fn matrix_power(mut base: Matrix4, mut exponent: u32) -> Matrix4 {
    let mut product = IDENTITY;
    while exponent != 0 {
        if exponent & 1 == 1 {
            product = matrix_multiply(product, base);
        }
        exponent >>= 1;
        if exponent != 0 {
            base = matrix_multiply(base, base);
        }
    }
    product
}

fn matrix_difference(left: Matrix4, right: Matrix4) -> Matrix4 {
    let mut difference = [[0_i64; 4]; 4];
    for row in 0..4 {
        for column in 0..4 {
            difference[row][column] = left[row][column] - right[row][column];
        }
    }
    difference
}

fn act_mod(matrix: Matrix4, phase: Phase) -> Phase {
    let mut result = [0_i64; 4];
    for row in 0..4 {
        result[row] = (0..4)
            .map(|column| matrix[row][column] * phase[column])
            .sum::<i64>()
            .rem_euclid(EXTENT);
    }
    result
}

fn phases() -> impl Iterator<Item = Phase> {
    (0..EXTENT).flat_map(|a| {
        (0..EXTENT).flat_map(move |b| {
            (0..EXTENT).flat_map(move |c| (0..EXTENT).map(move |d| [a, b, c, d]))
        })
    })
}

/// The four exact cardinal points form a `Z/4` phase circle.
fn phase_point(index: i64) -> (Rat, Rat) {
    match index.rem_euclid(EXTENT) {
        0 => (Rat::one(), Rat::zero()),
        1 => (Rat::zero(), Rat::one()),
        2 => (-Rat::one(), Rat::zero()),
        3 => (Rat::zero(), -Rat::one()),
        _ => unreachable!(),
    }
}

fn source_event(loop_index: usize, stage: u32) -> EventId {
    EventId(1_000 + u64::try_from(loop_index).expect("three loops") * 100 + u64::from(stage))
}

fn build_source() -> Result<ExactDimensionalSource, Box<dyn Error>> {
    assert_eq!(matrix_power(A1, 3), IDENTITY);
    assert_eq!(matrix_power(A2, 4), IDENTITY);
    assert_eq!(matrix_multiply(matrix_multiply(A1, A2), M0), IDENTITY);
    let nilpotent = matrix_difference(M0, IDENTITY);
    assert_eq!(matrix_multiply(nilpotent, nilpotent), [[0; 4]; 4]);

    let all_events = LOOPS
        .iter()
        .enumerate()
        .flat_map(|(loop_index, route)| {
            (0..=route.last_stage).map(move |stage| source_event(loop_index, stage))
        })
        .collect::<BTreeSet<_>>();
    let mut incidence = GradedCausalComplex::default();
    let mut build = SourceBuild::default();
    let mut germs = Vec::new();
    let mut next_germ = 1_u64;

    for (loop_index, route) in LOOPS.iter().enumerate() {
        for stage in 0..=route.last_stage {
            let event = source_event(loop_index, stage);
            let action = matrix_power(route.monodromy, stage);
            for phase in phases() {
                let transported = act_mod(action, phase);
                let cell = incidence.found_cell(
                    format!("{} stage {stage} fibre point {phase:?}", route.name),
                    event_set(event),
                    0,
                    CausalChain::default(),
                )?;
                let id = CoordinateGermId(next_germ);
                next_germ += 1;
                let mut coordinates = BTreeMap::from([
                    (BASE_STAGE, Rat::from_integer(BigInt::from(stage))),
                    (BASE_BRANCH, Rat::from_integer(BigInt::from(route.branch))),
                ]);
                for (phase_index, (real_axis, imaginary_axis)) in
                    PHASE_AXES.iter().copied().enumerate()
                {
                    let (real, imaginary) = phase_point(transported[phase_index]);
                    coordinates.insert(real_axis, real);
                    coordinates.insert(imaginary_axis, imaginary);
                }
                germs.push(ExactCoordinateGerm {
                    id,
                    name: format!("{} stage {stage} geometric T4 point {phase:?}", route.name),
                    source_cell: cell,
                    source_events: event_set(event),
                    coordinates,
                });
                build.cells.insert((loop_index, stage, phase), cell);
                build.germs.insert((loop_index, stage, phase), id);
            }
        }
    }

    let mut carriers = Vec::new();
    let mut next_carrier = 1_u64;
    for (loop_index, route) in LOOPS.iter().enumerate() {
        for stage in 0..=route.last_stage {
            let event = source_event(loop_index, stage);
            for phase in phases() {
                for direction in 0..4 {
                    let mut successor = phase;
                    successor[direction] = (successor[direction] + 1).rem_euclid(EXTENT);
                    carriers.push(ExactCoordinateCarrier {
                        id: CoordinateCarrierId(next_carrier),
                        name: format!(
                            "{} stage {stage} geometric fibre direction {direction}",
                            route.name
                        ),
                        from: build.germs[&(loop_index, stage, phase)],
                        to: build.germs[&(loop_index, stage, successor)],
                        source_events: event_set(event),
                        kind: CoordinateCarrierKind::PhaseReturn {
                            axis: PHASE_AXES[direction].0,
                        },
                    });
                    next_carrier += 1;
                }
                if stage < route.last_stage {
                    let next_event = source_event(loop_index, stage + 1);
                    carriers.push(ExactCoordinateCarrier {
                        id: CoordinateCarrierId(next_carrier),
                        name: format!("{} monodromy passage {stage}->{}", route.name, stage + 1),
                        from: build.germs[&(loop_index, stage, phase)],
                        to: build.germs[&(loop_index, stage + 1, phase)],
                        source_events: BTreeSet::from([event, next_event]),
                        kind: CoordinateCarrierKind::Interaction {
                            doctrine: format!(
                                "dual lattice transport by {}",
                                match loop_index {
                                    0 => "A1",
                                    1 => "A2",
                                    _ => "M0",
                                }
                            ),
                        },
                    });
                    next_carrier += 1;
                }
                if stage == route.last_stage && route.closes {
                    carriers.push(ExactCoordinateCarrier {
                        id: CoordinateCarrierId(next_carrier),
                        name: format!("{} exact ordered return", route.name),
                        from: build.germs[&(loop_index, stage, phase)],
                        to: build.germs[&(loop_index, 0, phase)],
                        source_events: BTreeSet::from([
                            source_event(loop_index, 0),
                            source_event(loop_index, stage),
                        ]),
                        kind: CoordinateCarrierKind::Interaction {
                            doctrine: "finite monodromy word returns identically".to_owned(),
                        },
                    });
                    next_carrier += 1;
                }
            }
        }
    }

    let axes = std::iter::once(DimensionalAxis::new(
        BASE_STAGE,
        "ordered transport stage",
        all_events.clone(),
    )?)
    .chain(std::iter::once(DimensionalAxis::new(
        BASE_BRANCH,
        "special base loop",
        all_events.clone(),
    )?))
    .chain(
        PHASE_AXES
            .iter()
            .enumerate()
            .flat_map(|(index, (real, imaginary))| {
                [
                    DimensionalAxis::new(
                        *real,
                        format!("fibre phase {index} real"),
                        all_events.clone(),
                    )
                    .expect("declared phase axis"),
                    DimensionalAxis::new(
                        *imaginary,
                        format!("fibre phase {index} imaginary"),
                        all_events.clone(),
                    )
                    .expect("declared phase axis"),
                ]
            }),
    )
    .collect::<Vec<_>>();
    let complex_pairs = PHASE_AXES
        .iter()
        .map(|(real, imaginary)| ExactComplexAxisPair {
            real: *real,
            imaginary: *imaginary,
            unit_conic: true,
        })
        .collect();
    Ok(ExactDimensionalSource::new(
        incidence,
        axes,
        complex_pairs,
        germs,
        carriers,
    )?)
}

fn covector(terms: &[(DimensionalAxisId, i64, i64)]) -> ExactSliceCovector {
    ExactSliceCovector::new(
        terms
            .iter()
            .map(|(axis, numerator, denominator)| (*axis, rat(*numerator, *denominator)))
            .collect(),
    )
    .expect("receiver covector is nonzero")
}

fn branch_constraint(branch: i64) -> ExactSliceConstraint {
    ExactSliceConstraint {
        covector: ExactSliceCovector::axis(BASE_BRANCH),
        center: Rat::from_integer(BigInt::from(branch)),
        radius: Rat::zero(),
    }
}

fn family_receiver() -> DimensionalReceiverFounding {
    DimensionalReceiverFounding {
        horizontal: covector(&[
            (BASE_STAGE, 1, 1),
            (PHASE_AXES[0].0, 1, 8),
            (PHASE_AXES[1].0, 1, 16),
            (PHASE_AXES[2].0, 1, 24),
            (PHASE_AXES[3].0, 1, 32),
        ]),
        vertical: covector(&[
            (BASE_BRANCH, 1, 1),
            (PHASE_AXES[0].1, 1, 8),
            (PHASE_AXES[1].1, 1, 16),
            (PHASE_AXES[2].1, 1, 24),
            (PHASE_AXES[3].1, 1, 32),
        ]),
        depth: Some(covector(&[
            (PHASE_AXES[0].0, 1, 8),
            (PHASE_AXES[1].1, -1, 10),
            (PHASE_AXES[2].0, 1, 12),
            (PHASE_AXES[3].1, -1, 14),
        ])),
        horizontal_center: rat(2, 1),
        vertical_center: Rat::zero(),
        horizontal_span: rat(5, 2),
        vertical_span: rat(3, 2),
        constraints: Vec::new(),
        causal_horizon: None,
        active_front: None,
    }
}

fn base_quotient_receiver() -> DimensionalReceiverFounding {
    DimensionalReceiverFounding {
        horizontal: ExactSliceCovector::axis(BASE_STAGE),
        vertical: ExactSliceCovector::axis(BASE_BRANCH),
        depth: None,
        horizontal_center: rat(2, 1),
        vertical_center: Rat::zero(),
        horizontal_span: rat(5, 2),
        vertical_span: rat(5, 4),
        constraints: Vec::new(),
        causal_horizon: None,
        active_front: None,
    }
}

fn fibre_receiver() -> DimensionalReceiverFounding {
    DimensionalReceiverFounding {
        horizontal: covector(&[
            (PHASE_AXES[0].0, 1, 1),
            (PHASE_AXES[1].0, 1, 2),
            (PHASE_AXES[2].0, 1, 4),
            (PHASE_AXES[3].0, 1, 8),
        ]),
        vertical: covector(&[
            (PHASE_AXES[0].1, 1, 1),
            (PHASE_AXES[1].1, 1, 2),
            (PHASE_AXES[2].1, 1, 4),
            (PHASE_AXES[3].1, 1, 8),
        ]),
        depth: Some(covector(&[
            (PHASE_AXES[0].0, 1, 4),
            (PHASE_AXES[1].1, 1, 6),
            (PHASE_AXES[2].0, -1, 8),
            (PHASE_AXES[3].1, -1, 10),
        ])),
        horizontal_center: Rat::zero(),
        vertical_center: Rat::zero(),
        horizontal_span: rat(2, 1),
        vertical_span: rat(2, 1),
        constraints: Vec::new(),
        causal_horizon: None,
        active_front: None,
    }
}

fn loop_receiver(branch: i64, last_stage: u32) -> DimensionalReceiverFounding {
    DimensionalReceiverFounding {
        horizontal: covector(&[
            (BASE_STAGE, 1, 1),
            (PHASE_AXES[0].0, 1, 7),
            (PHASE_AXES[2].0, 1, 13),
        ]),
        vertical: covector(&[
            (PHASE_AXES[0].1, 1, 1),
            (PHASE_AXES[1].1, 1, 2),
            (PHASE_AXES[2].1, 1, 4),
            (PHASE_AXES[3].1, 1, 8),
        ]),
        depth: Some(covector(&[
            (PHASE_AXES[0].0, 1, 5),
            (PHASE_AXES[1].0, -1, 7),
            (PHASE_AXES[2].1, 1, 9),
            (PHASE_AXES[3].1, -1, 11),
        ])),
        horizontal_center: rat(i64::from(last_stage), 2),
        vertical_center: Rat::zero(),
        horizontal_span: rat(i64::from(last_stage) + 1, 2),
        vertical_span: rat(2, 1),
        constraints: vec![branch_constraint(branch)],
        causal_horizon: None,
        active_front: None,
    }
}

fn found(
    atlas: &mut DimensionalReceiverAtlas,
    receiver: u64,
    event: u64,
    founding: DimensionalReceiverFounding,
) -> Result<DimensionalSliceReceipt, Box<dyn Error>> {
    Ok(atlas
        .receive(&DimensionalReceiverRequest {
            event: EventId(event),
            chronology: 1,
            receiver: ReceiverId(receiver),
            deed: DimensionalReceiverDeed::Found(founding),
        })?
        .receipt)
}

fn exact_pixel(value: &Rat, extent: u32) -> Option<i32> {
    if value.abs() > Rat::one() {
        return None;
    }
    let scaled = (value + Rat::one()) * Rat::from_integer(BigInt::from(extent.saturating_sub(1)))
        / Rat::from_integer(BigInt::from(2_u8));
    scaled.to_integer().to_i32()
}

fn received_position(
    disposition: &DimensionalGermDisposition,
    law: &ProjectionLaw,
) -> Result<Option<(i32, i32)>, Box<dyn Error>> {
    let DimensionalGermDisposition::Visible {
        normalized_horizontal,
        normalized_vertical,
        depth,
        ..
    } = disposition
    else {
        return Ok(None);
    };
    let point = RatVec3::new(
        normalized_horizontal.clone(),
        normalized_vertical.clone(),
        depth.clone().unwrap_or_else(Rat::zero),
    );
    let projected = project_receiver_point(&point, law)?;
    let rational = projected
        .rational
        .ok_or("the selected perspective receiver must remain rational")?;
    Ok(exact_pixel(&rational.x, WIDTH).zip(exact_pixel(&(-rational.y), HEIGHT)))
}

fn add_pixel(image: &mut RgbImage, x: i32, y: i32, contribution: [u8; 3]) {
    let (Ok(x), Ok(y)) = (u32::try_from(x), u32::try_from(y)) else {
        return;
    };
    if x >= image.width() || y >= image.height() {
        return;
    }
    let pixel = image.get_pixel_mut(x, y);
    for channel in 0..3 {
        pixel[channel] = pixel[channel].saturating_add(contribution[channel]);
    }
}

fn draw_line(
    image: &mut RgbImage,
    mut x0: i32,
    mut y0: i32,
    x1: i32,
    y1: i32,
    contribution: [u8; 3],
) {
    let dx = (x1 - x0).abs();
    let sx = if x0 < x1 { 1 } else { -1 };
    let dy = -(y1 - y0).abs();
    let sy = if y0 < y1 { 1 } else { -1 };
    let mut error = dx + dy;
    loop {
        add_pixel(image, x0, y0, contribution);
        if x0 == x1 && y0 == y1 {
            break;
        }
        let twice = 2 * error;
        if twice >= dy {
            error += dy;
            x0 += sx;
        }
        if twice <= dx {
            error += dx;
            y0 += sy;
        }
    }
}

fn carrier_color(carrier: &ExactCoordinateCarrier) -> [u8; 3] {
    match &carrier.kind {
        CoordinateCarrierKind::PhaseReturn { .. } => [2, 8, 12],
        CoordinateCarrierKind::Interaction { doctrine }
            if doctrine == "finite monodromy word returns identically" =>
        {
            [18, 2, 18]
        }
        CoordinateCarrierKind::Interaction { .. } => [18, 8, 2],
        CoordinateCarrierKind::Boundary { .. } | CoordinateCarrierKind::Chronology => [8, 8, 8],
    }
}

fn render(
    path: &Path,
    source: &ExactDimensionalSource,
    receipt: &DimensionalSliceReceipt,
    law: ProjectionLaw,
) -> Result<DisplayFace, Box<dyn Error>> {
    let mut image = RgbImage::from_pixel(WIDTH, HEIGHT, Rgb([2, 5, 11]));
    let positions = receipt
        .germs
        .iter()
        .filter_map(|(germ, body)| {
            received_position(&body.disposition, &law)
                .transpose()
                .map(|result| result.map(|position| (*germ, position)))
        })
        .collect::<Result<BTreeMap<_, _>, Box<dyn Error>>>()?;

    // Only source-declared carriers draw. Projected proximity creates no edge.
    for (id, carrier_receipt) in &receipt.carriers {
        if carrier_receipt.disposition != DimensionalCarrierDisposition::Visible {
            continue;
        }
        let (Some(from), Some(to)) = (
            positions.get(&carrier_receipt.from),
            positions.get(&carrier_receipt.to),
        ) else {
            continue;
        };
        draw_line(
            &mut image,
            from.0,
            from.1,
            to.0,
            to.1,
            carrier_color(&source.carriers()[id]),
        );
    }

    // A point's intensity is the number of source germs arriving at that exact raster address.
    let mut pixel_population = BTreeMap::<(i32, i32), u32>::new();
    for position in positions.values() {
        *pixel_population.entry(*position).or_default() += 1;
    }
    for ((x, y), population) in pixel_population {
        let increment = 28_u8.saturating_add(
            u8::try_from(population.min(20))
                .expect("bounded terminal population")
                .saturating_mul(8),
        );
        for dx in -1..=1 {
            for dy in -1..=1 {
                add_pixel(
                    &mut image,
                    x + dx,
                    y + dy,
                    [increment / 2, increment, increment],
                );
            }
        }
    }

    image.save(path)?;
    Ok(DisplayFace {
        schema: "holonic-engine.complex-s6-torus-transport-display.v1".to_owned(),
        width: WIDTH,
        height: HEIGHT,
        pixels: image
            .pixels()
            .map(|pixel| Rgb8 {
                red: pixel[0],
                green: pixel[1],
                blue: pixel[2],
            })
            .collect(),
    })
}

fn write_summary(
    output: &Path,
    source: &ExactDimensionalSource,
    receipts: &BTreeMap<String, DimensionalSliceReceipt>,
) -> Result<(), Box<dyn Error>> {
    let mut summary = BufWriter::new(File::create(output.join("source-summary.tsv"))?);
    writeln!(
        summary,
        "source_germs\tsource_carriers\tphase_factors\tfinite_phase_extent\tA1_order\tA2_order\tM0_nilpotence"
    )?;
    writeln!(
        summary,
        "{}\t{}\t4\t{}\t3\t4\t2",
        source.germs().len(),
        source.carriers().len(),
        EXTENT,
    )?;
    writeln!(summary)?;
    writeln!(
        summary,
        "receiver\tvisible_germs\tcollapsed_buckets\tvisible_carriers\tlocal_dimension\tprojection_cells"
    )?;
    for (name, receipt) in receipts {
        let visible_carriers = receipt
            .carriers
            .values()
            .filter(|carrier| carrier.disposition == DimensionalCarrierDisposition::Visible)
            .count();
        writeln!(
            summary,
            "{}\t{}\t{}\t{}\t{}\t{}",
            name,
            receipt.visible_germs,
            receipt.collapsed_buckets,
            visible_carriers,
            receipt.received_maximum_local_dimension,
            receipt.projection_cells,
        )?;
    }
    summary.flush()?;
    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let output = std::env::args_os()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_OUT));
    create_dir_all(&output)?;

    let source = build_source()?;
    let mut atlas = DimensionalReceiverAtlas::new(source)?;
    let mut receipts = BTreeMap::new();

    let base = found(&mut atlas, 100, 90_000, base_quotient_receiver())?;
    render(
        &output.join("00-base-quotient.png"),
        atlas.source(),
        &base,
        ProjectionLaw::PerspectiveRay {
            focal_distance: rat(4, 1),
        },
    )?;
    receipts.insert("base-quotient".to_owned(), base);

    let family = found(&mut atlas, 1, 90_001, family_receiver())?;
    render(
        &output.join("01-family-perspective.png"),
        atlas.source(),
        &family,
        ProjectionLaw::PerspectiveRay {
            focal_distance: rat(4, 1),
        },
    )?;
    receipts.insert("family-perspective".to_owned(), family);

    let fibre = found(&mut atlas, 2, 90_002, fibre_receiver())?;
    render(
        &output.join("02-fibre-perspective.png"),
        atlas.source(),
        &fibre,
        ProjectionLaw::PerspectiveRay {
            focal_distance: rat(4, 1),
        },
    )?;
    receipts.insert("fibre-perspective".to_owned(), fibre);

    let turned = atlas
        .receive(&DimensionalReceiverRequest {
            event: EventId(90_003),
            chronology: 2,
            receiver: ReceiverId(2),
            deed: DimensionalReceiverDeed::Turn {
                first: PHASE_AXES[0].0,
                second: PHASE_AXES[0].1,
                ratio: rat(1, 2),
            },
        })?
        .receipt;
    render(
        &output.join("03-fibre-after-exact-receiver-turn.png"),
        atlas.source(),
        &turned,
        ProjectionLaw::PerspectiveRay {
            focal_distance: rat(4, 1),
        },
    )?;
    receipts.insert("fibre-after-exact-receiver-turn".to_owned(), turned);

    for (ordinal, (filename, loop_index)) in [
        ("04-order-three-monodromy.png", 0_usize),
        ("05-order-four-monodromy.png", 1_usize),
        ("06-unipotent-cusp-shear.png", 2_usize),
    ]
    .into_iter()
    .enumerate()
    {
        let route = LOOPS[loop_index];
        let receipt = found(
            &mut atlas,
            10 + u64::try_from(ordinal)?,
            91_000 + u64::try_from(ordinal)?,
            loop_receiver(route.branch, route.last_stage),
        )?;
        render(
            &output.join(filename),
            atlas.source(),
            &receipt,
            ProjectionLaw::PerspectiveRay {
                focal_distance: rat(4, 1),
            },
        )?;
        receipts.insert(route.name.to_owned(), receipt);
    }

    atlas.validate()?;
    write(
        output.join("receiver-receipts.json"),
        serde_json::to_vec_pretty(&receipts)?,
    )?;
    write_summary(&output, atlas.source(), &receipts)?;
    println!(
        "returned {} exact receiver renderings from {} geometric T4 sample germs and {} declared carriers at {}",
        receipts.len(),
        atlas.source().germs().len(),
        atlas.source().carriers().len(),
        output.display(),
    );
    Ok(())
}
