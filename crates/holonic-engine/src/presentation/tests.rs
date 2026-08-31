use std::num::NonZeroUsize;

use relational_geometry::{Construction, EntityId, Geometry, ProjectionLaw, Receiver, integer};

use super::*;
use crate::{ProjectiveDepthLaw, RayFamily, ReceiverFaceExtent, ReceiverFaceSpec, receive_face};

#[test]
fn exact_support_equality_excludes_executor_work_testimony() {
    let receiver = ReceiverId(91);
    let primitive = ReceiverPrimitiveId::NativeConic(crate::ConicCellId(4));
    let address = PresentationAddress { column: 2, row: 3 };
    let trace = |address, queries| {
        ReceiverApertureTrace::from_primitive_sections(
            receiver,
            [PrimitiveApertureTrace {
                key: PresentedPrimitiveKey {
                    receiver,
                    primitive,
                },
                addresses: BTreeSet::from([address]),
                exact_support_queries: BigUint::from(queries),
            }],
        )
        .unwrap()
    };
    let cpu = trace(address, 17_u8);
    let device = trace(address, 41_u8);
    assert_ne!(cpu, device);
    assert!(cpu.has_same_exact_support(&device));
    assert!(!cpu.has_same_exact_support(&trace(PresentationAddress { column: 3, row: 3 }, 17_u8,)));
}

fn assembly() -> PluralReceiverAssembly {
    let (mut construction, frame) = Construction::new("source");
    construction
        .add_entity(
            "large triangle",
            frame,
            Geometry::Triangle {
                vertices: [
                    RatVec3::from_i64(-2, -2, 2),
                    RatVec3::from_i64(2, -2, 2),
                    RatVec3::from_i64(0, 2, 2),
                ],
            },
        )
        .unwrap();
    let spec = |id| ReceiverFaceSpec {
        receiver: Receiver::new(
            ReceiverId(id),
            "receiver",
            frame,
            ProjectionLaw::PerspectiveRay {
                focal_distance: integer(1),
            },
        ),
        extent: ReceiverFaceExtent {
            horizontal_span: integer(3),
            vertical_span: integer(2),
        },
        rays: RayFamily::Central {
            center: RatVec3::zero(),
            forward: RatVec3::from_i64(0, 0, 1),
            horizontal: RatVec3::from_i64(1, 0, 0),
            vertical: RatVec3::from_i64(0, 1, 0),
        },
        acceptance: None,
    };
    let left = receive_face(&construction, &spec(1)).unwrap();
    let right = receive_face(&construction, &spec(2)).unwrap();
    PluralReceiverAssembly::new(
        "caused pair",
        vec![left, right],
        vec![
            ReceiverStandingRelation::identity(ReceiverId(1), EventId(1)),
            ReceiverStandingRelation::new(
                ReceiverId(2),
                EventId(2),
                RatMat3::from_i64([[1, 0, 1], [0, 1, 0], [0, 0, 1]]),
            )
            .unwrap(),
        ],
    )
    .unwrap()
}

fn terminal() -> TerminalMatrixSpec {
    TerminalMatrixSpec {
        width: 11,
        height: 7,
        boundary: PresentationBoundary {
            horizontal_span: integer(4),
            vertical_span: integer(3),
        },
    }
}

#[test]
fn continuous_assembly_precedes_area_classification() {
    let assembly = assembly();
    let executed = quotient_presentation(&assembly, &terminal(), &CpuExecutor::serial()).unwrap();
    assert_eq!(executed.continuous.primitives.len(), 2);
    assert!(
        executed
            .matrix
            .members
            .iter()
            .any(|member| member.primitives.len() == 2)
    );
    let center = executed
        .matrix
        .members
        .iter()
        .find(|member| member.address == PresentationAddress { column: 5, row: 3 })
        .expect("the terminal matrix carries its center member");
    assert!(!center.depth_phases.is_empty());
    assert!(center.depth_phases.iter().all(|phase| {
        phase.levels
            == IntegralPhaseCell::Levels {
                first: BigInt::from(2),
                last: BigInt::from(2),
            }
    }));
}

#[test]
fn serial_and_multicore_terminal_quotients_are_identical() {
    let assembly = assembly();
    let serial = quotient_presentation(&assembly, &terminal(), &CpuExecutor::serial()).unwrap();
    let parallel = quotient_presentation(
        &assembly,
        &terminal(),
        &CpuExecutor::multicore(NonZeroUsize::new(4).unwrap()),
    )
    .unwrap();
    assert_eq!(serial.continuous, parallel.continuous);
    assert_eq!(serial.matrix, parallel.matrix);
    assert_ne!(serial.execution, parallel.execution);
}

#[test]
fn aperture_trace_follows_simplex_support_without_scanning_the_matrix() {
    let continuous = assemble_presentation(&assembly()).unwrap();
    let trace = trace_receiver_aperture(&continuous, &terminal(), ReceiverId(1)).unwrap();
    assert!(!trace.addresses.is_empty());
    assert!(
        trace.addresses.len()
            < usize::try_from(terminal().width * terminal().height)
                .expect("the test matrix is bounded")
    );
    assert_eq!(trace.primitive_traces, BigUint::from(1_u8));
    assert!(trace.exact_support_queries >= BigUint::from(trace.addresses.len()));
}

#[test]
fn a_projective_edge_crossing_infinity_casts_two_finite_aperture_branches() {
    let start = ProjectivePoint2::new(integer(-1), integer(0), integer(1)).unwrap();
    let end = ProjectivePoint2::new(integer(-1), integer(0), integer(-1)).unwrap();
    let pieces = clip_projective_segment_to_aperture(&start, &end, &terminal());
    assert_eq!(pieces.len(), 2);
    let mut horizontal = pieces
        .into_iter()
        .flat_map(|(first, last)| [first[0].clone(), last[0].clone()])
        .collect::<Vec<_>>();
    horizontal.sort();
    assert_eq!(
        horizontal,
        vec![integer(-2), integer(-1), integer(1), integer(2)]
    );
}

#[test]
fn integral_span_is_exact_across_negative_and_positive_boundaries() {
    assert_eq!(
        integral_span(
            &relational_geometry::rat(-21, 5),
            &relational_geometry::rat(29, 5)
        ),
        IntegralPhaseCell::Levels {
            first: BigInt::from(-4),
            last: BigInt::from(5),
        }
    );
    assert_eq!(
        integral_span(
            &relational_geometry::rat(1, 5),
            &relational_geometry::rat(4, 5)
        ),
        IntegralPhaseCell::NoLevel
    );
}

#[test]
fn coordinate_phase_has_no_authored_finite_level_cutoff() {
    let family = ProjectiveLineFamily {
        zero: ProjectiveLine2 {
            a: integer(1),
            b: Rat::zero(),
            c: Rat::zero(),
        },
        coefficient: ProjectiveLine2 {
            a: Rat::zero(),
            b: Rat::zero(),
            c: integer(-1),
        },
    };
    let cell = ExactCell {
        lower: [integer(20), integer(-1)],
        upper: [integer(21), integer(1)],
    };

    assert_eq!(
        integral_line_family_span(&family, &cell),
        IntegralPhaseCell::Levels {
            first: BigInt::from(20),
            last: BigInt::from(21),
        }
    );
}

#[test]
fn quadratic_phase_exposes_curved_levels_beyond_zero_contour() {
    let circle_levels = HomogeneousConic::new([
        integer(1),
        Rat::zero(),
        integer(1),
        Rat::zero(),
        Rat::zero(),
        Rat::zero(),
    ])
    .unwrap();
    let cell = ExactCell {
        lower: [integer(3), integer(4)],
        upper: [integer(4), integer(5)],
    };
    let range = quadratic_range(&circle_levels, &cell).unwrap();

    assert_eq!(range.0, integer(25));
    assert_eq!(range.1, integer(41));
    assert_eq!(
        integral_span(&range.0, &range.1),
        IntegralPhaseCell::Levels {
            first: BigInt::from(25),
            last: BigInt::from(41),
        }
    );
}

fn one_cell() -> TerminalMatrixSpec {
    TerminalMatrixSpec {
        width: 1,
        height: 1,
        boundary: PresentationBoundary {
            horizontal_span: integer(2),
            vertical_span: integer(2),
        },
    }
}

fn exact_depth(value: i64) -> ProjectiveDepthLaw {
    ProjectiveDepthLaw {
        numerator: ProjectiveLine2 {
            a: Rat::zero(),
            b: Rat::zero(),
            c: integer(value),
        },
        denominator: ProjectiveLine2 {
            a: Rat::zero(),
            b: Rat::zero(),
            c: integer(1),
        },
    }
}

fn point(x: i64, y: i64) -> ProjectivePoint2 {
    ProjectivePoint2::new(integer(x), integer(y), integer(1)).unwrap()
}

fn triangle(receiver: u64, entity: u64, depth: i64) -> PresentedPrimitive {
    PresentedPrimitive {
        receiver: ReceiverId(receiver),
        primitive: ReceiverPrimitive::Triangle(ProjectedTriangle {
            source: ReceiverPrimitiveId::Entity(EntityId(entity)),
            vertices: [point(-1, -1), point(1, -1), point(-1, 1)],
            receiver_depths: [integer(depth), integer(depth), integer(depth)],
            receiver_depth: Some(Box::new(exact_depth(depth))),
        }),
    }
}

fn triangle_at(receiver: u64, entity: u64, center_x: i64, depth: i64) -> PresentedPrimitive {
    let vertices = [
        point(center_x - 1, -1),
        point(center_x + 1, -1),
        point(center_x - 1, 1),
    ];
    PresentedPrimitive {
        receiver: ReceiverId(receiver),
        primitive: ReceiverPrimitive::Triangle(ProjectedTriangle {
            source: ReceiverPrimitiveId::Entity(EntityId(entity)),
            vertices,
            receiver_depths: [integer(depth), integer(depth), integer(depth)],
            receiver_depth: Some(Box::new(exact_depth(depth))),
        }),
    }
}

fn presentation(primitives: Vec<PresentedPrimitive>) -> ContinuousPresentation {
    ContinuousPresentation {
        schema: "test.exact-surface-presentation".to_owned(),
        boundary_name: "test receiver".to_owned(),
        primitives,
        coordinate_fields: Vec::new(),
        relations: Vec::new(),
        seams: Vec::new(),
    }
}

#[test]
fn exact_surface_returns_rational_triangle_coverage() {
    let surface =
        exact_surface_presentation(&presentation(vec![triangle(1, 1, 2)]), &one_cell()).unwrap();
    let cell = surface.cells.values().next().unwrap();
    assert_eq!(surface.occupied_cells, BigUint::from(1_u8));
    assert_eq!(cell.contributions.len(), 1);
    assert_eq!(
        cell.contributions[0].coverage,
        SurfaceCoverage::AreaFraction(relational_geometry::rat(1, 2))
    );
    assert_eq!(
        cell.contributions[0].depth,
        SurfaceDepth::Range {
            near: integer(2),
            far: integer(2)
        }
    );
}

#[test]
fn exact_surface_orders_separated_depth_layers() {
    let surface = exact_surface_presentation(
        &presentation(vec![triangle(1, 1, 2), triangle(1, 2, 5)]),
        &one_cell(),
    )
    .unwrap();
    let cell = surface.cells.values().next().unwrap();
    assert_eq!(
        cell.occlusion,
        OcclusionFace::Ordered {
            front_to_back: vec![
                SurfaceMemberId {
                    key: PresentedPrimitiveKey {
                        receiver: ReceiverId(1),
                        primitive: ReceiverPrimitiveId::Entity(EntityId(1)),
                    },
                    segment: None,
                },
                SurfaceMemberId {
                    key: PresentedPrimitiveKey {
                        receiver: ReceiverId(1),
                        primitive: ReceiverPrimitiveId::Entity(EntityId(2)),
                    },
                    segment: None,
                },
            ]
        }
    );
}

#[test]
fn exact_surface_evaluates_each_primitive_only_in_its_addressed_section() {
    let specification = TerminalMatrixSpec {
        width: 12,
        height: 4,
        boundary: PresentationBoundary {
            horizontal_span: integer(12),
            vertical_span: integer(4),
        },
    };
    let surface = exact_surface_presentation(
        &presentation(vec![triangle_at(1, 1, -4, 2), triangle_at(1, 2, 4, 5)]),
        &specification,
    )
    .unwrap();
    assert!(surface.candidate_cells > BigUint::zero());
    assert!(surface.primitive_evaluations < surface.candidate_cells.clone() * 2_u8);
}

#[test]
fn exact_surface_keeps_equal_depth_open() {
    let surface = exact_surface_presentation(
        &presentation(vec![triangle(1, 1, 2), triangle(1, 2, 2)]),
        &one_cell(),
    )
    .unwrap();
    let cell = surface.cells.values().next().unwrap();
    assert_eq!(surface.open_occlusion_cells, BigUint::from(1_u8));
    assert!(matches!(
        cell.occlusion,
        OcclusionFace::Open {
            reason: OcclusionObstruction::EqualDepth,
            ..
        }
    ));
}

#[test]
fn exact_surface_keeps_thread_source_parameter_intervals() {
    let primitive = PresentedPrimitive {
        receiver: ReceiverId(7),
        primitive: ReceiverPrimitive::Thread(ProjectedThread {
            source: ReceiverPrimitiveId::Entity(EntityId(9)),
            vertices: vec![point(-1, 0), point(1, 0)],
            receiver_depths: vec![integer(2), integer(2)],
            closed: false,
        }),
    };
    let specification = TerminalMatrixSpec {
        width: 2,
        height: 1,
        boundary: PresentationBoundary {
            horizontal_span: integer(2),
            vertical_span: integer(2),
        },
    };
    let surface =
        exact_surface_presentation(&presentation(vec![primitive]), &specification).unwrap();
    let intervals = surface
        .cells
        .values()
        .flat_map(|cell| cell.contributions.iter())
        .map(|contribution| match &contribution.coverage {
            SurfaceCoverage::SourceParameterInterval { start, end } => (start.clone(), end.clone()),
            other => panic!("unexpected thread coverage: {other:?}"),
        })
        .collect::<Vec<_>>();
    assert_eq!(
        intervals,
        vec![
            (Rat::zero(), relational_geometry::rat(1, 2)),
            (relational_geometry::rat(1, 2), Rat::one()),
        ]
    );
}
