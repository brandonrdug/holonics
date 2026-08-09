use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fs::{File, create_dir_all};
use std::io::{BufWriter, Write};
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::thread;
use std::time::Duration;

#[cfg(test)]
use std::time::Instant;

use holonic_engine::{
    AdmittedCudaApertureExecutor, AffineHingeForm, CausalWorld, ConicChart, ConicFamilyLaw,
    CpuExecutor, CudaApertureExecutor, CudaApertureReceipt, DisplayFace, DisplayPatch, Edge,
    EventId, FaceId, HingeId, HingeTrajectory, HingeTransportNetwork, HingeUnitSystem,
    HingeWorldLaw, LocalCurrentTransport, LocalStarError, LocalStarEvent, LocalStarLaw,
    LocalStarMaterial, LocalStarRadiation, LocalStarStanding, PlatformMembrane,
    PluralReceiverAssembly, PresentationAddress, PresentationBoundary, QuadraticHingeAction,
    RawPlatformInput, RayFamily, ReceiverApertureTrace, ReceiverBoundaryDeed,
    ReceiverFaceFormationCause, ReceiverFaceFormationReceipt, ReceiverFaceSpec, ReceiverFounding,
    ReceiverLocalCoupling, ReceiverPrimitive, ReceiverRotationCoupling, ReceiverSourceSection,
    ReceiverSourceSelection, ReceiverStandingRelation, ReceiverTraversalOccurrence,
    ReceiverTraversalStep, Rgb8, SimplicialComplex, TerminalMatrixSpec, TerminalTubeAtlas,
    TerminalTubePlan, TerminalTubeRadiation, TerminalTubeReceipt, VertexId, VertexStarLink,
    X11Platform, assemble_support_presentation_with_cpu, classify_presentation_address,
};
#[cfg(test)]
use holonic_engine::{
    ApertureExecutionBackend, ContinuousPresentation, MemoryPlatform,
    assemble_presentation_with_cpu,
};
use num_bigint::BigUint;
use num_traits::{ToPrimitive, Zero};
use relational_geometry::{
    Construction, EntityId, Geometry, ProjectiveRatio, Rat, RatMat3, RatVec3, ReceiverId,
    ReceiverOrientation, ReceiverRotationAxis, integer,
};

const TERMINAL_RECEIVER: ReceiverId = ReceiverId(1);

type TubeTraceResult = Result<
    (
        BTreeMap<ReceiverId, ReceiverApertureTrace>,
        Option<CudaApertureReceipt>,
    ),
    Box<dyn std::error::Error>,
>;

/// Project one receiver-relative exact phase triple into the monitor's local
/// three-primary chart. Subtracting the least component retains signed phase
/// orientation; exact barycentric ratios determine the channels. RGB is the
/// outer transducer's basis, not a universal color ontology.
#[derive(Clone, Copy)]
enum PhaseColorLaw {
    Neutral,
    Oriented { base: [u8; 3] },
}

impl PhaseColorLaw {
    fn from_phase(phase: &RatVec3) -> Self {
        let minimum = [&phase.x, &phase.y, &phase.z]
            .into_iter()
            .min()
            .expect("one physical phase has three components");
        let weights = [&phase.x - minimum, &phase.y - minimum, &phase.z - minimum];
        let total = weights.iter().fold(Rat::zero(), |sum, value| sum + value);
        if total.is_zero() {
            return Self::Neutral;
        }
        let channel = |weight: &Rat| {
            let scaled = weight * integer(184) / &total;
            let quotient = scaled.numer() / scaled.denom();
            36_u8.saturating_add(quotient.to_u8().unwrap_or(184))
        };
        Self::Oriented {
            base: [
                channel(&weights[0]),
                channel(&weights[1]),
                channel(&weights[2]),
            ],
        }
    }

    fn color(self, multiplicity: &BigUint) -> Rgb8 {
        let count = multiplicity.to_u8().unwrap_or(u8::MAX);
        match self {
            Self::Neutral => {
                let energy = 56_u8.saturating_add(count.saturating_mul(40)).min(240);
                Rgb8 {
                    red: energy,
                    green: energy,
                    blue: energy,
                }
            }
            Self::Oriented { base } => {
                let support = count.saturating_sub(1).saturating_mul(12);
                Rgb8 {
                    red: base[0].saturating_add(support).min(240),
                    green: base[1].saturating_add(support).min(240),
                    blue: base[2].saturating_add(support).min(240),
                }
            }
        }
    }
}

#[cfg(test)]
fn phase_color(phase: &RatVec3, multiplicity: &BigUint) -> Rgb8 {
    PhaseColorLaw::from_phase(phase).color(multiplicity)
}

fn receiver_phases(standing: &LocalStarStanding) -> BTreeMap<ReceiverId, RatVec3> {
    standing
        .receivers
        .iter()
        .map(|(receiver, body)| (*receiver, body.physical_phase.clone()))
        .collect()
}

fn integer_bits(value: &num_bigint::BigInt) -> u64 {
    value.magnitude().bits()
}

fn rational_bits(value: &Rat) -> u64 {
    integer_bits(value.numer()).max(integer_bits(value.denom()))
}

fn vector_bits(value: &RatVec3) -> u64 {
    [&value.x, &value.y, &value.z]
        .into_iter()
        .map(rational_bits)
        .max()
        .unwrap_or(0)
}

fn matrix_bits(value: &RatMat3) -> u64 {
    value
        .rows
        .iter()
        .flatten()
        .map(rational_bits)
        .max()
        .unwrap_or(0)
}

fn line_bits(value: &holonic_engine::ProjectiveLine2) -> u64 {
    [&value.a, &value.b, &value.c]
        .into_iter()
        .map(rational_bits)
        .max()
        .unwrap_or(0)
}

fn point_bits(value: &holonic_engine::ProjectivePoint2) -> u64 {
    [&value.x, &value.y, &value.w]
        .into_iter()
        .map(rational_bits)
        .max()
        .unwrap_or(0)
}

fn depth_bits(value: &holonic_engine::ProjectiveDepthLaw) -> u64 {
    line_bits(&value.numerator).max(line_bits(&value.denominator))
}

fn conic_bits(value: &holonic_engine::HomogeneousConic) -> u64 {
    [
        &value.xx, &value.xy, &value.yy, &value.xw, &value.yw, &value.ww,
    ]
    .into_iter()
    .map(rational_bits)
    .max()
    .unwrap_or(0)
}

fn primitive_bits(value: &ReceiverPrimitive) -> u64 {
    match value {
        ReceiverPrimitive::Triangle(triangle) => triangle
            .vertices
            .iter()
            .map(point_bits)
            .chain(triangle.receiver_depths.iter().map(rational_bits))
            .chain(
                triangle
                    .receiver_depth
                    .iter()
                    .map(|depth| depth_bits(depth)),
            )
            .max()
            .unwrap_or(0),
        ReceiverPrimitive::Thread(thread) => thread
            .vertices
            .iter()
            .map(point_bits)
            .chain(thread.receiver_depths.iter().map(rational_bits))
            .max()
            .unwrap_or(0),
        ReceiverPrimitive::Conic(conic) => {
            conic_bits(&conic.form).max(depth_bits(&conic.receiver_depth))
        }
    }
}

#[derive(Clone, Copy)]
struct TraceArithmeticHeights {
    trajectory: u64,
    receiver_translation: u64,
    receiver_spin: u64,
    receiver_phase: u64,
    presentation_factor: u64,
    presented_support: u64,
}

fn trace_arithmetic_heights(
    standing: &LocalStarStanding,
    atlas: &TerminalTubeAtlas,
) -> TraceArithmeticHeights {
    let trajectory = standing
        .trajectories
        .values()
        .flat_map(|trajectory| [&trajectory.previous, &trajectory.current])
        .chain(standing.kinematic.parameters.values())
        .map(rational_bits)
        .max()
        .unwrap_or(0);
    let receiver_translation = standing
        .receivers
        .values()
        .flat_map(|body| [&body.previous_local_offset, &body.local_offset])
        .map(vector_bits)
        .max()
        .unwrap_or(0);
    let receiver_spin = standing
        .receivers
        .values()
        .flat_map(|body| {
            body.previous_orientation
                .spin()
                .components()
                .iter()
                .chain(body.orientation.spin().components())
        })
        .map(integer_bits)
        .max()
        .unwrap_or(0);
    let receiver_phase = standing
        .receivers
        .values()
        .map(|body| vector_bits(&body.physical_phase))
        .max()
        .unwrap_or(0);
    let presentation_factor = atlas
        .tubes
        .values()
        .flat_map(|tube| {
            std::iter::once(&tube.relation.into_presentation)
                .chain(tube.presentation_word.iter().map(|step| &step.map))
        })
        .map(matrix_bits)
        .max()
        .unwrap_or(0);
    let presented_support = atlas
        .tubes
        .values()
        .flat_map(|tube| tube.presented_primitives.iter())
        .map(primitive_bits)
        .max()
        .unwrap_or(0);
    TraceArithmeticHeights {
        trajectory,
        receiver_translation,
        receiver_spin,
        receiver_phase,
        presentation_factor,
        presented_support,
    }
}

fn add_color(target: &mut Rgb8, addition: Rgb8) {
    target.red = target.red.saturating_add(addition.red);
    target.green = target.green.saturating_add(addition.green);
    target.blue = target.blue.saturating_add(addition.blue);
}

struct DesktopEcology {
    construction: Construction,
    face_entities: BTreeMap<FaceId, EntityId>,
    face_vertices: BTreeMap<FaceId, [VertexId; 3]>,
    physical: CausalWorld<LocalStarLaw>,
    frame: relational_geometry::FrameId,
    radiation: LocalStarRadiation,
}

fn third_vertex(vertices: [VertexId; 3], edge: Edge) -> VertexId {
    vertices
        .into_iter()
        .find(|vertex| *vertex != edge.lower && *vertex != edge.upper)
        .expect("a face incident to an edge has one opposite vertex")
}

fn conic_family(
    ordinal: usize,
    founding: EventId,
    frame: relational_geometry::FrameId,
    hinge: HingeId,
    edge: Edge,
    complex: &SimplicialComplex,
    positions: &BTreeMap<VertexId, RatVec3>,
) -> Result<ConicFamilyLaw, Box<dyn std::error::Error>> {
    let hinge_body = complex
        .hinges
        .get(&hinge)
        .expect("the family hinge belongs to the complex");
    let incident_face = complex
        .faces
        .get(&hinge_body.cofaces[0].face)
        .expect("a hinge's coface belongs to the complex");
    let left = &positions[&edge.lower];
    let right = &positions[&edge.upper];
    let opposite = &positions[&third_vertex(incident_face.vertices, edge)];
    let half = integer(1) / integer(2);
    let midpoint = left.add(right).scale(&half);
    let axis_x = right.subtract(left).scale(&half);
    let axis_y = opposite.subtract(&midpoint).scale(&half);
    let zero = || AffineHingeForm::constant(integer(0));
    let one = || AffineHingeForm::constant(integer(1));
    let negative_one = || AffineHingeForm::constant(integer(-1));
    let q = |constant| AffineHingeForm::constant(integer(constant)).plus_hinge(hinge, integer(1));
    let coefficients = match ordinal % 3 {
        // The family species is not assigned as a label. Its exact
        // homogeneous quadratic changes with the local hinge parameter and
        // the receiver derives its chart-relative class from that form.
        0 => [one(), zero(), one(), zero(), zero(), q(-1)],
        1 => [q(1), zero(), one(), zero(), zero(), negative_one()],
        _ => [one(), zero(), negative_one(), zero(), zero(), q(-1)],
    };
    Ok(ConicFamilyLaw::new(
        format!("hinge {} emitted quadratic family", hinge.0),
        founding,
        frame,
        ConicChart::new(midpoint, axis_x, axis_y)?,
        coefficients,
    ))
}

fn build_ecology(executor: CpuExecutor) -> Result<DesktopEcology, Box<dyn std::error::Error>> {
    let founding = EventId(1);
    let mut complex = SimplicialComplex::default();
    let a = complex.found_vertex("a", founding);
    let b = complex.found_vertex("b", founding);
    let c = complex.found_vertex("c", founding);
    let d = complex.found_vertex("d", founding);
    let e = complex.found_vertex("e", founding);
    let f = complex.found_vertex("f", founding);
    let positions = BTreeMap::from([
        (a, RatVec3::from_i64(3, 0, 7)),
        (b, RatVec3::from_i64(0, 3, 7)),
        (c, RatVec3::from_i64(-3, 0, 7)),
        (d, RatVec3::from_i64(0, -3, 7)),
        (e, RatVec3::from_i64(0, 0, 11)),
        (f, RatVec3::from_i64(0, 0, 3)),
    ]);
    // The octahedral boundary supplies plural cycles and admits genuine
    // 2-to-2 edge-flip openings: the two opposite vertices around a radial
    // hinge are not already joined.
    complex.found_face("eab", founding, [e, a, b])?;
    complex.found_face("ebc", founding, [e, b, c])?;
    complex.found_face("ecd", founding, [e, c, d])?;
    complex.found_face("eda", founding, [e, d, a])?;
    complex.found_face("fba", founding, [f, b, a])?;
    complex.found_face("fcb", founding, [f, c, b])?;
    complex.found_face("fdc", founding, [f, d, c])?;
    complex.found_face("fad", founding, [f, a, d])?;
    let face_vertices = complex
        .faces
        .iter()
        .map(|(face, body)| (*face, body.vertices))
        .collect::<BTreeMap<_, _>>();

    let (mut construction, frame) = Construction::new("causal simplicial desktop ecology");
    let mut face_entities = BTreeMap::new();
    for face in complex.faces.values() {
        let entity = construction.add_entity(
            format!("simplex face {}", face.name),
            frame,
            Geometry::Triangle {
                vertices: face.vertices.map(|vertex| positions[&vertex].clone()),
            },
        )?;
        face_entities.insert(face.id, entity);
    }

    let edges = complex
        .faces
        .values()
        .flat_map(|face| face.boundary().into_iter().map(|(edge, _)| edge))
        .collect::<BTreeSet<_>>();
    let mut hinges = BTreeMap::new();
    for (ordinal, edge) in edges.into_iter().enumerate() {
        let hinge = complex.found_hinge(format!("shared edge {}", ordinal + 1), founding, edge)?;
        hinges.insert(edge, hinge);
    }

    let families = hinges
        .iter()
        .enumerate()
        .take(3)
        .map(|(ordinal, (edge, hinge))| {
            conic_family(
                ordinal, founding, frame, *hinge, *edge, &complex, &positions,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let parameters = hinges
        .values()
        .copied()
        .map(|hinge| (hinge, integer(0)))
        .collect::<BTreeMap<_, _>>();
    // Conic realization consumes the complete local-star successor. It does
    // not run the former instantaneous identity flood.
    let kinematic = HingeWorldLaw::new(complex, HingeTransportNetwork::default(), families)?;
    let kinematic_standing = kinematic.initial_standing(parameters)?;
    let units = HingeUnitSystem {
        coordinate: "projective hinge turn".to_owned(),
        event_step: "causal event".to_owned(),
        action: "hinge action".to_owned(),
        momentum: "hinge action / turn".to_owned(),
        impulse: "hinge action / turn".to_owned(),
    };
    let materials = hinges
        .iter()
        .enumerate()
        .map(|(ordinal, (edge, hinge))| {
            let edge_direction = positions[&edge.upper]
                .subtract(&positions[&edge.lower])
                .scale(&(integer(1) / integer(16)));
            Ok((
                *hinge,
                LocalStarMaterial {
                    action: QuadraticHingeAction::new(
                        integer(2 + i64::try_from(ordinal % 3).expect("small modulus")),
                        integer(1 + i64::try_from(ordinal % 2).expect("small modulus")),
                        units.clone(),
                    )?,
                    stress_response: integer(1)
                        / integer(4 + i64::try_from(ordinal % 3).expect("small modulus")),
                    geometry_response: edge_direction,
                },
            ))
        })
        .collect::<Result<BTreeMap<_, _>, holonic_engine::PhysicalLawError>>()?;

    // One current retains one quarter of its action in the active star and
    // distributes the other three quarters among only face-adjacent hinges.
    // Nothing can jump across the complex in the same event.
    //
    // Hand is selected by an exact source-declared field covector in this
    // bounded chart, not by hinge identifiers or container order.
    let field_axis = RatVec3::from_i64(1, 2, 4);
    let hinge_potential = hinges
        .iter()
        .map(|(edge, hinge)| {
            (
                *hinge,
                positions[&edge.lower]
                    .add(&positions[&edge.upper])
                    .dot(&field_axis),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut current_transports = Vec::new();
    for source in hinges.values().copied() {
        let adjacent = hinges
            .values()
            .copied()
            .filter(|target| {
                *target != source
                    && kinematic
                        .complex
                        .hinges_share_face(source, *target)
                        .expect("all declared hinges remain in the complex")
            })
            .collect::<Vec<_>>();
        for hand in [-1, 1] {
            let targets = adjacent
                .iter()
                .copied()
                .filter(|target| {
                    (hand == 1 && hinge_potential[target] < hinge_potential[&source])
                        || (hand == -1 && hinge_potential[target] > hinge_potential[&source])
                })
                .collect::<Vec<_>>();
            if targets.is_empty() {
                continue;
            }
            let coefficient = integer(3)
                / integer(i64::try_from(4 * targets.len()).expect("bounded target count"));
            current_transports.extend(targets.into_iter().map(|target| {
                LocalCurrentTransport::with_hand(source, target, hand, coefficient.clone())
            }));
        }
    }
    let first_port = hinges
        .iter()
        .find_map(|(edge, hinge)| (edge.lower == e || edge.upper == e).then_some(*hinge))
        .expect("receiver a has incident hinges");
    let second_port = hinges
        .iter()
        .rev()
        .find_map(|(edge, hinge)| (edge.lower == f || edge.upper == f).then_some(*hinge))
        .expect("receiver d has incident hinges");
    let receiver_couplings = |anchor: VertexId, direction: RatVec3, precession: RatVec3| {
        let rotation_scale = integer(1) / integer(32);
        let rotations_per_turn = [
            (ReceiverRotationAxis::X, &precession.x),
            (ReceiverRotationAxis::Y, &precession.y),
            (ReceiverRotationAxis::Z, &precession.z),
        ]
        .into_iter()
        .filter(|(_, coefficient)| !coefficient.is_zero())
        .map(|(axis, coefficient)| ReceiverRotationCoupling {
            axis,
            cayley_per_turn: coefficient * &rotation_scale,
        })
        .collect::<Vec<_>>();
        hinges
            .iter()
            .filter_map(|(edge, hinge)| {
                (edge.lower == anchor || edge.upper == anchor).then_some(ReceiverLocalCoupling {
                    hinge: *hinge,
                    translation_per_turn: direction.scale(&(integer(1) / integer(16))),
                    rotations_per_turn: rotations_per_turn.clone(),
                })
            })
            .collect::<Vec<_>>()
    };
    let physical_law = LocalStarLaw::new(kinematic, materials, current_transports, executor)?;
    let trajectories = hinges
        .values()
        .copied()
        .map(|hinge| {
            (
                hinge,
                HingeTrajectory {
                    previous: integer(0),
                    current: integer(0),
                },
            )
        })
        .collect();
    let receiver_body = |receiver,
                         anchor,
                         port,
                         desired_position: RatVec3,
                         couplings: Vec<ReceiverLocalCoupling>| {
        let local_offset = desired_position.subtract(&positions[&anchor]);
        ReceiverFounding {
            receiver,
            source_event: founding,
            anchor,
            port,
            couplings,
            local_offset: local_offset.clone(),
            orientation: ReceiverOrientation::identity(),
        }
    };
    let receiver_bodies = vec![
        receiver_body(
            ReceiverId(1),
            e,
            first_port,
            RatVec3::zero(),
            receiver_couplings(e, RatVec3::from_i64(0, 0, 1), RatVec3::from_i64(1, 0, 1)),
        ),
        receiver_body(
            ReceiverId(2),
            f,
            second_port,
            RatVec3::from_i64(1, -1, 0),
            receiver_couplings(f, RatVec3::from_i64(0, 1, 0), RatVec3::from_i64(0, 1, -1)),
        ),
    ];
    let physical_standing = physical_law.initial_standing(
        kinematic_standing,
        trajectories,
        positions,
        receiver_bodies,
    )?;
    let initial_receiver_chart = physical_standing.receiver_traversal_chart(ReceiverId(1))?;
    let mut physical = CausalWorld::new(physical_law, physical_standing);
    let receipt = physical.receive(&LocalStarEvent {
        event: EventId(2),
        source_currents: BTreeMap::new(),
        receiver_deeds: vec![ReceiverBoundaryDeed {
            receiver: ReceiverId(1),
            traversal: ReceiverTraversalOccurrence {
                source_chart: initial_receiver_chart,
                steps: Vec::new(),
            },
            port_current: integer(1),
        }],
        receiver_population: Vec::new(),
        topology_deeds: Vec::new(),
    })?;
    let radiation = receipt
        .radiation
        .into_iter()
        .next()
        .expect("one local-star event emits one complete radiation");
    sync_construction(
        &mut construction,
        &face_entities,
        physical.standing(),
        &face_vertices,
    )?;

    Ok(DesktopEcology {
        construction,
        face_entities,
        face_vertices,
        physical,
        frame,
        radiation,
    })
}

fn terminal(width: u32, height: u32) -> TerminalMatrixSpec {
    let horizontal_span = integer(2);
    TerminalMatrixSpec {
        width,
        height,
        boundary: PresentationBoundary {
            horizontal_span: horizontal_span.clone(),
            vertical_span: horizontal_span * Rat::from_integer(height.into())
                / Rat::from_integer(width.into()),
        },
    }
}

fn sync_construction(
    construction: &mut Construction,
    face_entities: &BTreeMap<FaceId, EntityId>,
    standing: &LocalStarStanding,
    face_vertices: &BTreeMap<FaceId, [VertexId; 3]>,
) -> Result<(), Box<dyn std::error::Error>> {
    let vertices = standing.realized_vertices()?;
    for (face, entity) in face_entities {
        let vertex_ids = face_vertices
            .get(face)
            .expect("every presented face retains its local incidence");
        let geometry = &mut construction
            .entities
            .get_mut(entity)
            .expect("every presented face retains its caused entity")
            .geometry;
        *geometry = Geometry::Triangle {
            vertices: vertex_ids.map(|vertex| vertices[&vertex].position.clone()),
        };
    }
    Ok(())
}

fn receiver_specification(
    frame: relational_geometry::FrameId,
    receiver: ReceiverId,
    standing: &LocalStarStanding,
) -> Result<ReceiverFaceSpec, Box<dyn std::error::Error>> {
    Ok(standing.receiver_face_specification(frame, receiver)?)
}

fn central_chart(specification: &ReceiverFaceSpec) -> (&RatVec3, &RatVec3, &RatVec3) {
    match &specification.rays {
        RayFamily::Central {
            center,
            horizontal,
            vertical,
            ..
        } => (center, horizontal, vertical),
        RayFamily::Parallel { .. } => {
            unreachable!("the local-star application supplies central receiver fibers")
        }
    }
}

fn coordinates_in_face(vector: &RatVec3, horizontal: &RatVec3, vertical: &RatVec3) -> [Rat; 2] {
    let hh = horizontal.dot(horizontal);
    let hv = horizontal.dot(vertical);
    let vv = vertical.dot(vertical);
    let determinant = &hh * &vv - &hv * &hv;
    debug_assert!(!determinant.is_zero());
    let vh = vector.dot(horizontal);
    let vvect = vector.dot(vertical);
    [
        (&vh * &vv - &vvect * &hv) / &determinant,
        (&vvect * &hh - &vh * &hv) / determinant,
    ]
}

/// Derive every face-to-presentation map from the explicitly addressed
/// terminal receiver's own chart. Identity occurs only for that receiver;
/// other faces are carried by the exact change of basis and relative center
/// displacement.  The terminal matrix never supplies this relation.
fn receiver_relations(
    specifications: &[ReceiverFaceSpec],
    standing: &LocalStarStanding,
    terminal_receiver: ReceiverId,
) -> Result<Vec<ReceiverStandingRelation>, Box<dyn std::error::Error>> {
    let primary = specifications
        .iter()
        .find(|specification| specification.receiver.id == terminal_receiver)
        .ok_or("the declared terminal receiver is absent from the active overlap component")?;
    let (primary_center, primary_horizontal, primary_vertical) = central_chart(primary);
    specifications
        .iter()
        .map(|specification| {
            let (center, horizontal, vertical) = central_chart(specification);
            let horizontal_in_primary =
                coordinates_in_face(horizontal, primary_horizontal, primary_vertical);
            let vertical_in_primary =
                coordinates_in_face(vertical, primary_horizontal, primary_vertical);
            let center_in_primary = coordinates_in_face(
                &center.subtract(primary_center),
                primary_horizontal,
                primary_vertical,
            );
            let relation = RatMat3::new([
                [
                    horizontal_in_primary[0].clone(),
                    vertical_in_primary[0].clone(),
                    center_in_primary[0].clone(),
                ],
                [
                    horizontal_in_primary[1].clone(),
                    vertical_in_primary[1].clone(),
                    center_in_primary[1].clone(),
                ],
                [Rat::zero(), Rat::zero(), integer(1)],
            ]);
            let body = standing
                .receivers
                .get(&specification.receiver.id)
                .ok_or("receiver standing disappeared during assembly")?;
            Ok(ReceiverStandingRelation::new(
                specification.receiver.id,
                body.source_event,
                relation,
            )?)
        })
        .collect()
}

struct ReceiverSupportCut {
    assembly: PluralReceiverAssembly,
    source_sections: BTreeMap<ReceiverId, ReceiverSourceSection>,
    formations: BTreeMap<ReceiverId, ReceiverFaceFormationReceipt>,
    topologies: BTreeMap<ReceiverId, VertexStarLink>,
    projected_faces: usize,
    reused_faces: usize,
    rebased_faces: usize,
}

fn support_assembly(
    construction: &Construction,
    frame: relational_geometry::FrameId,
    physical: &CausalWorld<LocalStarLaw>,
    face_entities: &BTreeMap<FaceId, EntityId>,
    terminal_receiver: ReceiverId,
    atlas: Option<&TerminalTubeAtlas>,
    executor: &CpuExecutor,
) -> Result<ReceiverSupportCut, Box<dyn std::error::Error>> {
    let standing = physical.standing();
    let law = physical.law();
    let conics = &standing.kinematic.conics;
    let admitted_receivers = standing
        .receiver_overlap_component(terminal_receiver)
        .ok_or("the declared terminal receiver has departed")?;
    let specifications = admitted_receivers
        .iter()
        .map(|receiver| receiver_specification(frame, *receiver, standing))
        .collect::<Result<Vec<_>, _>>()?;
    let specifications_by_receiver = specifications
        .iter()
        .map(|specification| (specification.receiver.id, specification))
        .collect::<BTreeMap<_, _>>();
    let mut projected_specifications = Vec::new();
    let mut projected_selections = BTreeMap::new();
    let mut faces = Vec::new();
    let mut reused_faces = 0_usize;
    let mut rebased_faces = 0_usize;
    let mut source_sections = BTreeMap::new();
    let mut formations = BTreeMap::new();
    let mut topologies = BTreeMap::new();
    for receiver in &admitted_receivers {
        let body = standing
            .receivers
            .get(receiver)
            .ok_or("receiver disappeared while factoring its local star")?;
        let topology = standing
            .receiver_topology(*receiver)
            .ok_or("receiver topology disappeared while factoring its local star")?;
        let entities = topology
            .star_faces
            .iter()
            .map(|face| {
                face_entities
                    .get(face)
                    .copied()
                    .ok_or("one intrinsic star face has no geometric entity")
            })
            .collect::<Result<BTreeSet<_>, _>>()?;
        let selection = ReceiverSourceSelection {
            entities,
            conics: law.kinematic.conic_cells_incident_to(&topology.star_hinges),
        };
        let source_section = selection.section(construction, conics)?;
        let specification = specifications_by_receiver
            .get(receiver)
            .copied()
            .expect("the specification population was derived from these receivers");
        if let Some(carried) = atlas.and_then(|atlas| {
            atlas.carried_receiver_formation(
                standing.event,
                specification,
                body.source_event,
                &topology,
                &source_section,
            )
        }) {
            if matches!(
                carried.formation.cause(),
                ReceiverFaceFormationCause::Rebased { .. }
            ) {
                rebased_faces += 1;
            }
            formations.insert(*receiver, carried.formation);
            faces.push(carried.face);
            reused_faces += 1;
        } else {
            projected_specifications.push(specification.clone());
            projected_selections.insert(*receiver, selection);
        }
        source_sections.insert(*receiver, source_section);
        topologies.insert(*receiver, topology);
    }
    let projected_faces = projected_specifications.len();
    if !projected_specifications.is_empty() {
        let (formed, _) = holonic_engine::receive_selected_faces_with_conics_certified_cpu(
            standing.event,
            construction,
            conics,
            &projected_specifications,
            &projected_selections,
            executor,
        )?;
        for formed in formed {
            formations.insert(formed.face.receiver, formed.formation);
            faces.push(formed.face);
        }
    }
    let relations = receiver_relations(&specifications, standing, terminal_receiver)?;
    Ok(ReceiverSupportCut {
        assembly: PluralReceiverAssembly::new(
            "star-local receiver sections in the terminal overlap component",
            faces,
            relations,
        )?,
        source_sections,
        formations,
        topologies,
        projected_faces,
        reused_faces,
        rebased_faces,
    })
}

/// Turn an exact discriminant opening into one caused receiver founding.
///
/// This is not a display-camera spawn. The opening chooses an existing
/// simplicial vertex, its actual incident star supplies the receiver port and
/// constitutive couplings, and the resulting receiver enters the physical
/// successor before it can contribute a projected face.
struct ResearchTrace {
    path: PathBuf,
    writer: BufWriter<File>,
    records: u64,
}

struct ResearchTraceEvent<'a> {
    event: u64,
    kind: &'a str,
    physical: &'a CausalWorld<LocalStarLaw>,
    radiation: Option<&'a LocalStarRadiation>,
    atlas: &'a TerminalTubeAtlas,
    render: &'a ApertureRenderReceipt,
    tubes: &'a TerminalTubeReceipt,
    specification: &'a TerminalMatrixSpec,
}

impl ResearchTrace {
    fn create() -> Result<Self, Box<dyn std::error::Error>> {
        let path = std::env::var_os("HOLONIC_ENGINE_TRACE").map_or_else(
            || PathBuf::from("target/holonic-engine/desktop_receiver_trace.tsv"),
            PathBuf::from,
        );
        if let Some(parent) = path.parent().filter(|parent| *parent != Path::new("")) {
            create_dir_all(parent)?;
        }
        let mut writer = BufWriter::new(File::create(&path)?);
        writeln!(
            writer,
            "event\tkind\tactive_hinges\topen_frontier\taction_balances\tcurrent_routes\tface_fields\treceiver_worldlines\trewrite_candidates\tphysics_tasks\tphysics_workers\tchanged_hinges\tchanged_faces\tchanged_conics\taperture_width\taperture_height\ttrajectory_bits\treceiver_translation_bits\treceiver_spin_bits\treceiver_phase_bits\tpresentation_factor_bits\tpresented_support_bits\tdevice_arithmetic\tintermediate_bits\ttraced_addresses\tsupport_queries\twall_nanoseconds\tselected_primitives\tdevice_primitives\thost_primitives\tdevice_output_bytes\tselection_pack_ns\tdevice_prepare_ns\tdevice_execute_ns\tdevice_download_ns\tdevice_decode_ns\thost_trace_ns\thost_merge_ns\ttube_founded\ttube_refounded\ttube_deformed\ttube_transported\ttube_aperture_changed\ttube_retained\ttube_departed\ttube_shared_traces\ttube_reused_addresses\ttube_avoided_queries\ttube_changed_addresses\tpresentation_materialized_receivers\tpresentation_materialized_primitives\tcomplete_hinge_state\tcomplete_receiver_state\treceiver_event_nerve\treceiver_population\tcausal_layers\tpropagation_boundary\ttube_rebased"
        )?;
        Ok(Self {
            path,
            writer,
            records: 0,
        })
    }

    fn record(&mut self, record: ResearchTraceEvent<'_>) -> Result<(), std::io::Error> {
        let ResearchTraceEvent {
            event,
            kind,
            physical,
            radiation,
            atlas,
            render,
            tubes,
            specification,
        } = record;
        let heights = trace_arithmetic_heights(physical.standing(), atlas);
        let active_hinges = radiation.map_or_else(
            || "-".to_owned(),
            |value| {
                value
                    .active_hinges
                    .iter()
                    .map(|hinge| hinge.0.to_string())
                    .collect::<Vec<_>>()
                    .join(",")
            },
        );
        let open_frontier = physical
            .standing()
            .open_frontier()
            .iter()
            .map(|(hinge, current)| {
                // The arms, not only the net: a hinge two opposed currents reached is not a hinge
                // nothing reached, and until 2026-08-08 the frontier could not say which.
                format!(
                    "{}:{}({}/{})",
                    hinge.0,
                    current.net(),
                    current.toward(),
                    current.against()
                )
            })
            .collect::<Vec<_>>()
            .join(";");
        let action_balances = radiation.map_or_else(
            || "-".to_owned(),
            |value| {
                value
                    .balances
                    .iter()
                    .map(|balance| {
                        format!(
                            "{}:q={}->{}:p={}->{}:j={}:r={}",
                            balance.hinge.0,
                            balance.coordinate_before,
                            balance.coordinate_after,
                            balance.momentum_before,
                            balance.momentum_after,
                            &balance.internal_impulse + &balance.external_impulse,
                            balance.exact_residual,
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(";")
            },
        );
        let current_routes = radiation.map_or_else(
            || "-".to_owned(),
            |value| {
                value
                    .current_balances
                    .iter()
                    .map(|balance| {
                        let emitted = balance
                            .emitted
                            .iter()
                            .map(|(target, current)| {
                                format!(
                                    "{}:{}({}/{})",
                                    target.0,
                                    current.net(),
                                    current.toward(),
                                    current.against()
                                )
                            })
                            .collect::<Vec<_>>()
                            .join(",");
                        format!(
                            "{}:in={}:held={}:out=[{}]:departed={}:r={}",
                            balance.hinge.0,
                            balance.entered,
                            balance.deposited,
                            emitted,
                            balance.departed,
                            balance.exact_residual,
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(";")
            },
        );
        let face_fields = physical
            .standing()
            .faces
            .iter()
            .map(|(face, field)| {
                format!(
                    "{}:c={}->{}:stress={}",
                    face.0, field.previous_circulation, field.circulation, field.stress,
                )
            })
            .collect::<Vec<_>>()
            .join(";");
        let receiver_worldlines = radiation.map_or_else(
            || "-".to_owned(),
            |value| {
                value
                    .receiver_worldlines
                    .iter()
                    .map(|step| {
                        let before = step.orientation_before.spin().components();
                        let after = step.orientation_after.spin().components();
                        format!(
                            "{}:pos=({},{},{})->({},{},{}):spin=[{},{},{},{}]->[{},{},{},{}]:traversal={:?}",
                            step.receiver.0,
                            step.position_before.x,
                            step.position_before.y,
                            step.position_before.z,
                            step.position_after.x,
                            step.position_after.y,
                            step.position_after.z,
                            before[0],
                            before[1],
                            before[2],
                            before[3],
                            after[0],
                            after[1],
                            after[2],
                            after[3],
                            step.traversal,
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(";")
            },
        );
        let rewrite_candidates = radiation.map_or_else(
            || "-".to_owned(),
            |value| {
                value
                    .rewrite_candidates
                    .iter()
                    .map(|candidate| {
                        format!(
                            "{}:{}-{}",
                            candidate.hinge.0,
                            candidate.proposed_diagonal.lower.0,
                            candidate.proposed_diagonal.upper.0,
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(";")
            },
        );
        let hinge_state = physical
            .standing()
            .trajectories
            .iter()
            .map(|(hinge, trajectory)| {
                format!("{}:{},{}", hinge.0, trajectory.previous, trajectory.current)
            })
            .collect::<Vec<_>>()
            .join(";");
        let receiver_state = physical
            .standing()
            .receivers
            .iter()
            .map(|(receiver, body)| {
                let position = physical
                    .standing()
                    .receiver_position(*receiver)
                    .expect("receiver retains anchor");
                let spin = body.orientation.spin().components();
                format!(
                    "{}:anchor={}:pos=({},{},{}):spin=[{},{},{},{}]:phase=({},{},{})",
                    receiver.0,
                    body.anchor.0,
                    position.x,
                    position.y,
                    position.z,
                    spin[0],
                    spin[1],
                    spin[2],
                    spin[3],
                    body.physical_phase.x,
                    body.physical_phase.y,
                    body.physical_phase.z,
                )
            })
            .collect::<Vec<_>>()
            .join(";");
        let receiver_nerve = radiation.map_or_else(
            || "-".to_owned(),
            |value| {
                value
                    .receiver_nerve
                    .cells
                    .iter()
                    .map(|cell| {
                        format!(
                            "{:?}:[{}]",
                            cell.occurrence,
                            cell.receivers
                                .iter()
                                .map(|receiver| receiver.0.to_string())
                                .collect::<Vec<_>>()
                                .join(","),
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(";")
            },
        );
        let receiver_population = radiation.map_or_else(
            || "-".to_owned(),
            |value| {
                value
                    .receiver_population
                    .iter()
                    .map(|change| format!("{change:?}"))
                    .collect::<Vec<_>>()
                    .join(";")
            },
        );
        let fields = vec![
            event.to_string(),
            kind.to_owned(),
            active_hinges,
            open_frontier,
            action_balances,
            current_routes,
            face_fields,
            receiver_worldlines,
            rewrite_candidates,
            radiation.map_or_else(
                || "0".to_owned(),
                |value| value.cpu_execution.tasks.to_string(),
            ),
            radiation.map_or_else(
                || "0".to_owned(),
                |value| value.cpu_execution.workers_used.to_string(),
            ),
            radiation
                .map_or(0, |value| value.kinematic.changed_hinges.len())
                .to_string(),
            radiation
                .map_or(0, |value| value.kinematic.changed_faces.len())
                .to_string(),
            radiation
                .map_or(0, |value| value.kinematic.changed_conics.len())
                .to_string(),
            specification.width.to_string(),
            specification.height.to_string(),
            heights.trajectory.to_string(),
            heights.receiver_translation.to_string(),
            heights.receiver_spin.to_string(),
            heights.receiver_phase.to_string(),
            heights.presentation_factor.to_string(),
            heights.presented_support.to_string(),
            render.device_arithmetic.clone(),
            render.intermediate_bits.to_string(),
            render.traced_addresses.to_string(),
            render.exact_support_queries.to_string(),
            render.wall_nanoseconds.to_string(),
            render.selected_primitives.to_string(),
            render.device_primitives.to_string(),
            render.host_primitives.to_string(),
            render.device_output_bytes.to_string(),
            render.selection_pack_nanoseconds.to_string(),
            render.device_prepare_nanoseconds.to_string(),
            render.device_execute_nanoseconds.to_string(),
            render.device_download_nanoseconds.to_string(),
            render.device_decode_nanoseconds.to_string(),
            render.host_trace_nanoseconds.to_string(),
            render.host_merge_nanoseconds.to_string(),
            tubes.founded.to_string(),
            tubes.refounded.to_string(),
            tubes.deformed.to_string(),
            tubes.transported.to_string(),
            tubes.aperture_changed.to_string(),
            tubes.retained.to_string(),
            tubes.departed.to_string(),
            tubes.shared_trace_receivers.to_string(),
            tubes.reused_addresses.to_string(),
            tubes.avoided_support_queries.to_string(),
            tubes.changed_addresses.to_string(),
            tubes.materialized_receivers.to_string(),
            tubes.materialized_primitives.to_string(),
            hinge_state,
            receiver_state,
            receiver_nerve,
            receiver_population,
            radiation
                .map_or(0, |value| value.causal_layers.len())
                .to_string(),
            radiation.map_or_else(
                || "-".to_owned(),
                |value| format!("{:?}", value.propagation_boundary),
            ),
            tubes.rebased.to_string(),
        ];
        writeln!(self.writer, "{}", fields.join("\t"))?;
        self.records += 1;
        self.writer.flush()?;
        Ok(())
    }
}

#[derive(Debug)]
struct PendingAction {
    source: ReceiverId,
    deed: ReceiverBoundaryDeed,
}

fn pending_traversal(
    standing: &LocalStarStanding,
    receiver: ReceiverId,
    steps: Vec<ReceiverTraversalStep>,
) -> Result<PendingAction, Box<dyn std::error::Error>> {
    Ok(PendingAction {
        source: receiver,
        deed: ReceiverBoundaryDeed {
            receiver,
            traversal: ReceiverTraversalOccurrence {
                source_chart: standing.receiver_traversal_chart(receiver)?,
                steps,
            },
            port_current: Rat::zero(),
        },
    })
}

fn append_elementary_traversal(
    steps: &mut Vec<ReceiverTraversalStep>,
    generator: ReceiverTraversalStep,
) {
    match steps.last_mut() {
        Some(ReceiverTraversalStep::Repeat {
            generator: previous,
            repetitions,
        }) if previous.as_ref() == &generator => {
            *repetitions += BigUint::from(1_u8);
        }
        Some(previous) if previous == &generator => {
            let retained = previous.clone();
            *previous = ReceiverTraversalStep::Repeat {
                generator: Box::new(retained),
                repetitions: BigUint::from(2_u8),
            };
        }
        _ => steps.push(generator),
    }
}

fn enqueue_traversal(
    pending: &mut VecDeque<PendingAction>,
    standing: &LocalStarStanding,
    receiver: ReceiverId,
    steps: Vec<ReceiverTraversalStep>,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut occurrence = pending_traversal(standing, receiver, Vec::new())?;
    if let Some(previous) = pending.back_mut()
        && previous.source == receiver
        && previous.deed.port_current.is_zero()
        && previous.deed.traversal.source_chart == occurrence.deed.traversal.source_chart
    {
        for step in steps {
            append_elementary_traversal(&mut previous.deed.traversal.steps, step);
        }
        return Ok(());
    }
    for step in steps {
        append_elementary_traversal(&mut occurrence.deed.traversal.steps, step);
    }
    pending.push_back(occurrence);
    Ok(())
}

fn relative_pointer_chord(
    horizontal_counts: i64,
    vertical_counts: i64,
    width: u32,
    height: u32,
) -> RatVec3 {
    RatVec3::new(
        integer(2) * Rat::new(horizontal_counts.into(), width.into()),
        integer(-2) * Rat::new(vertical_counts.into(), height.into()),
        Rat::zero(),
    )
}

fn receiver_ordinal(specification: &TerminalMatrixSpec, address: PresentationAddress) -> usize {
    usize::try_from(
        u64::from(address.row) * u64::from(specification.width) + u64::from(address.column),
    )
    .expect("a terminal address fits memory addressing")
}

fn background_color() -> Rgb8 {
    Rgb8 {
        red: 3,
        green: 8,
        blue: 12,
    }
}

fn compose_pixel<'a>(
    traces: impl IntoIterator<Item = (ReceiverId, &'a ReceiverApertureTrace)>,
    phases: &BTreeMap<ReceiverId, RatVec3>,
    address: PresentationAddress,
) -> Rgb8 {
    let mut color = Rgb8 {
        red: 3,
        green: 8,
        blue: 12,
    };
    let mut participating = 0_u8;
    for (receiver, trace) in traces {
        let Some(multiplicity) = trace.support_multiplicity.get(&address) else {
            continue;
        };
        let phase = phases
            .get(&receiver)
            .expect("every terminal tube carries one transported physical phase");
        participating = participating.saturating_add(1);
        add_color(
            &mut color,
            PhaseColorLaw::from_phase(phase).color(multiplicity),
        );
    }
    if participating > 1 {
        add_color(
            &mut color,
            Rgb8 {
                red: 35,
                green: 35,
                blue: 35,
            },
        );
    }
    color
}

fn compose_display(
    specification: &TerminalMatrixSpec,
    atlas: &TerminalTubeAtlas,
    phases: &BTreeMap<ReceiverId, RatVec3>,
) -> Result<DisplayFace, Box<dyn std::error::Error>> {
    if atlas.specification.as_ref() != Some(specification) {
        return Err("the terminal tube atlas does not carry the requested aperture".into());
    }
    let member_count =
        usize::try_from(u64::from(specification.width) * u64::from(specification.height))?;
    let mut pixels = vec![background_color(); member_count];
    let addresses = atlas
        .tubes
        .values()
        .flat_map(|tube| tube.terminal_trace.addresses.iter().copied())
        .collect::<BTreeSet<_>>();
    for address in addresses {
        pixels[receiver_ordinal(specification, address)] = compose_pixel(
            atlas
                .tubes
                .iter()
                .map(|(receiver, tube)| (*receiver, &tube.terminal_trace)),
            phases,
            address,
        );
    }
    Ok(DisplayFace {
        schema: "holonic-engine.receiver-superstate.v3".to_owned(),
        width: specification.width,
        height: specification.height,
        pixels,
    })
}

fn affected_terminal_addresses(
    atlas: &TerminalTubeAtlas,
    radiation: &TerminalTubeRadiation,
    previous_phases: &BTreeMap<ReceiverId, RatVec3>,
    phases: &BTreeMap<ReceiverId, RatVec3>,
) -> BTreeSet<PresentationAddress> {
    let mut affected = radiation
        .support_deltas
        .iter()
        .map(|delta| delta.address)
        .collect::<BTreeSet<_>>();
    for (receiver, phase) in phases {
        if previous_phases.get(receiver) != Some(phase)
            && let Some(trace) = atlas.trace(*receiver)
        {
            affected.extend(trace.addresses.iter().copied());
        }
    }
    affected
}

fn update_display_patches(
    display: &mut DisplayFace,
    specification: &TerminalMatrixSpec,
    atlas: &TerminalTubeAtlas,
    phases: &BTreeMap<ReceiverId, RatVec3>,
    affected: &BTreeSet<PresentationAddress>,
) -> Result<Vec<DisplayPatch>, Box<dyn std::error::Error>> {
    if (display.width, display.height) != (specification.width, specification.height) {
        return Err("the retained exact display and terminal aperture differ".into());
    }
    let mut changed = BTreeMap::<u32, BTreeMap<u32, Rgb8>>::new();
    for address in affected {
        if address.column >= specification.width || address.row >= specification.height {
            return Err("a terminal support delta lies outside its aperture".into());
        }
        let color = compose_pixel(
            atlas
                .tubes
                .iter()
                .map(|(receiver, tube)| (*receiver, &tube.terminal_trace)),
            phases,
            *address,
        );
        let ordinal = receiver_ordinal(specification, *address);
        if display.pixels[ordinal] != color {
            display.pixels[ordinal] = color;
            changed
                .entry(address.row)
                .or_default()
                .insert(address.column, color);
        }
    }
    let mut patches = Vec::new();
    for (row, columns) in changed {
        let mut run_left = None;
        let mut run_pixels = Vec::new();
        let mut previous_column = None;
        for (column, color) in columns {
            if previous_column.is_some_and(|previous| column != previous + 1) {
                let left = run_left.expect("one nonempty run has a left boundary");
                patches.push(DisplayPatch {
                    left,
                    top: row,
                    face: DisplayFace {
                        schema: "holonic-engine.receiver-superstate-patch.v1".to_owned(),
                        width: u32::try_from(run_pixels.len())?,
                        height: 1,
                        pixels: std::mem::take(&mut run_pixels),
                    },
                });
                run_left = None;
            }
            run_left.get_or_insert(column);
            run_pixels.push(color);
            previous_column = Some(column);
        }
        if let Some(left) = run_left {
            patches.push(DisplayPatch {
                left,
                top: row,
                face: DisplayFace {
                    schema: "holonic-engine.receiver-superstate-patch.v1".to_owned(),
                    width: u32::try_from(run_pixels.len())?,
                    height: 1,
                    pixels: run_pixels,
                },
            });
        }
    }
    Ok(patches)
}

fn refusal_display(width: u32, height: u32) -> Result<DisplayFace, Box<dyn std::error::Error>> {
    let member_count = usize::try_from(
        u64::from(width)
            .checked_mul(u64::from(height))
            .ok_or("the refused platform extent exceeds the display carrier")?,
    )?;
    Ok(DisplayFace {
        schema: "holonic-engine.exact-aperture-refusal.v1".to_owned(),
        width,
        height,
        pixels: vec![
            Rgb8 {
                red: 18,
                green: 6,
                blue: 6,
            };
            member_count
        ],
    })
}

#[derive(Clone, Debug)]
struct ApertureRenderReceipt {
    backend: String,
    traced_addresses: BigUint,
    exact_support_queries: BigUint,
    trace_workers_used: BigUint,
    wall_nanoseconds: u128,
    selected_primitives: BigUint,
    device_primitives: BigUint,
    host_primitives: BigUint,
    device_output_bytes: BigUint,
    selection_pack_nanoseconds: u128,
    device_prepare_nanoseconds: u128,
    device_execute_nanoseconds: u128,
    device_download_nanoseconds: u128,
    device_decode_nanoseconds: u128,
    host_trace_nanoseconds: u128,
    host_merge_nanoseconds: u128,
    host_parity: bool,
    intermediate_bits: BigUint,
    device_arithmetic: String,
}

fn retained_aperture_receipt(tubes: &TerminalTubeReceipt) -> ApertureRenderReceipt {
    ApertureRenderReceipt {
        backend: "retained exact tube atlas".to_owned(),
        traced_addresses: BigUint::from(0_u8),
        exact_support_queries: BigUint::from(0_u8),
        trace_workers_used: BigUint::from(0_u8),
        wall_nanoseconds: 0,
        selected_primitives: BigUint::from(0_u8),
        device_primitives: BigUint::from(0_u8),
        host_primitives: BigUint::from(0_u8),
        device_output_bytes: BigUint::from(0_u8),
        selection_pack_nanoseconds: 0,
        device_prepare_nanoseconds: 0,
        device_execute_nanoseconds: 0,
        device_download_nanoseconds: 0,
        device_decode_nanoseconds: 0,
        host_trace_nanoseconds: 0,
        host_merge_nanoseconds: 0,
        host_parity: true,
        intermediate_bits: BigUint::from(0_u8),
        device_arithmetic: format!(
            "exact carried support; reused-receivers={} avoided-queries={}",
            tubes.reused_receivers, tubes.avoided_support_queries
        ),
    }
}

#[cfg(test)]
type ApertureRenderResult = Result<
    (
        BTreeMap<ReceiverId, ReceiverApertureTrace>,
        ApertureRenderReceipt,
    ),
    Box<dyn std::error::Error>,
>;

#[cfg(test)]
fn render_receiver_traces(
    presentation: &ContinuousPresentation,
    specification: &TerminalMatrixSpec,
    receivers: &BTreeSet<ReceiverId>,
    executor: &CpuExecutor,
) -> ApertureRenderResult {
    let started = std::time::Instant::now();
    let (traces, trace_execution) = holonic_engine::trace_receivers_aperture_with_cpu(
        presentation,
        specification,
        receivers,
        executor,
    )?;
    let wall_nanoseconds = started.elapsed().as_nanos();
    let traced_addresses = traces.values().fold(BigUint::zero(), |sum, trace| {
        sum + BigUint::from(trace.addresses.len())
    });
    let exact_support_queries = traces.values().fold(BigUint::zero(), |sum, trace| {
        sum + &trace.exact_support_queries
    });
    Ok((
        traces,
        ApertureRenderReceipt {
            backend: "exact host".to_owned(),
            traced_addresses,
            exact_support_queries,
            trace_workers_used: trace_execution.workers_used,
            wall_nanoseconds,
            selected_primitives: BigUint::from(presentation.primitives.len()),
            device_primitives: BigUint::from(0_u8),
            host_primitives: BigUint::from(presentation.primitives.len()),
            device_output_bytes: BigUint::from(0_u8),
            selection_pack_nanoseconds: 0,
            device_prepare_nanoseconds: 0,
            device_execute_nanoseconds: 0,
            device_download_nanoseconds: 0,
            device_decode_nanoseconds: 0,
            host_trace_nanoseconds: wall_nanoseconds,
            host_merge_nanoseconds: 0,
            host_parity: true,
            intermediate_bits: BigUint::from(0_u8),
            device_arithmetic: "exact host integer-projective".to_owned(),
        },
    ))
}

fn trace_tube_plan(
    cuda: &AdmittedCudaApertureExecutor,
    specification: &TerminalMatrixSpec,
    plan: &TerminalTubePlan,
    executor: &CpuExecutor,
) -> TubeTraceResult {
    if plan.trace_primitive_keys().is_empty() {
        return Ok((BTreeMap::new(), None));
    }
    let presentation = plan.trace_presentation();
    let (traces, receipt) = cuda.trace_primitives(
        &presentation,
        specification,
        plan.trace_primitive_keys(),
        executor,
    )?;
    Ok((traces, Some(receipt)))
}

fn receipt_from_cuda_traces(
    traces: &BTreeMap<ReceiverId, ReceiverApertureTrace>,
    receipt: CudaApertureReceipt,
) -> ApertureRenderReceipt {
    let traced_addresses = traces.values().fold(BigUint::from(0_u8), |sum, trace| {
        sum + BigUint::from(trace.addresses.len())
    });
    let exact_support_queries = traces.values().fold(BigUint::from(0_u8), |sum, trace| {
        sum + &trace.exact_support_queries
    });
    ApertureRenderReceipt {
        backend: if receipt.device_primitives.is_zero() {
            receipt.execution_backend.clone()
        } else {
            format!("{} {}", receipt.execution_backend, receipt.device)
        },
        traced_addresses,
        exact_support_queries,
        trace_workers_used: receipt.host_workers,
        wall_nanoseconds: receipt.wall_nanoseconds,
        selected_primitives: receipt.selected_primitives,
        device_primitives: receipt.device_primitives,
        host_primitives: receipt.host_primitives,
        device_output_bytes: receipt.device_output_bytes,
        selection_pack_nanoseconds: receipt.selection_pack_nanoseconds,
        device_prepare_nanoseconds: receipt.device_prepare_nanoseconds,
        device_execute_nanoseconds: receipt.device_execute_nanoseconds,
        device_download_nanoseconds: receipt.device_download_nanoseconds,
        device_decode_nanoseconds: receipt.device_decode_nanoseconds,
        host_trace_nanoseconds: receipt.host_trace_nanoseconds,
        host_merge_nanoseconds: receipt.host_merge_nanoseconds,
        host_parity: receipt.host_parity,
        intermediate_bits: receipt.intermediate_bits,
        device_arithmetic: receipt.device_arithmetic,
    }
}

#[allow(clippy::too_many_arguments)]
fn reconcile_tubes(
    cuda: &AdmittedCudaApertureExecutor,
    event: EventId,
    assembly: &PluralReceiverAssembly,
    specification: &TerminalMatrixSpec,
    topologies: &BTreeMap<ReceiverId, VertexStarLink>,
    source_sections: &BTreeMap<ReceiverId, ReceiverSourceSection>,
    formations: &BTreeMap<ReceiverId, ReceiverFaceFormationReceipt>,
    atlas: &mut TerminalTubeAtlas,
    executor: &CpuExecutor,
) -> Result<(TerminalTubeRadiation, ApertureRenderReceipt), Box<dyn std::error::Error>> {
    let plan = atlas.plan(
        event,
        assembly,
        specification,
        topologies,
        source_sections,
        formations,
    )?;
    let (traces, cuda_receipt) = trace_tube_plan(cuda, specification, &plan, executor)?;
    let render = cuda_receipt.map(|receipt| receipt_from_cuda_traces(&traces, receipt));
    let radiation = atlas.commit(plan, traces)?;
    let render = render.unwrap_or_else(|| retained_aperture_receipt(&radiation.receipt));
    Ok((radiation, render))
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let available = thread::available_parallelism().unwrap_or(NonZeroUsize::MIN);
    let worker_count = if available.get() > 1 {
        available.get().saturating_sub(1).min(12)
    } else {
        1
    };
    let workers = NonZeroUsize::new(worker_count).expect("one CPU worker always exists");
    let executor = CpuExecutor::multicore(workers);
    let DesktopEcology {
        mut construction,
        face_entities,
        face_vertices,
        mut physical,
        frame,
        radiation,
    } = build_ecology(executor)?;
    let mut event = 2_u64;
    let mut research_trace = ResearchTrace::create()?;
    let mut dragging = false;
    let mut pending_drag = None::<(PresentationAddress, i64, i64)>;
    let mut pending_actions = VecDeque::<PendingAction>::new();
    let mut specification = terminal(640, 400);
    let mut current_cut = support_assembly(
        &construction,
        frame,
        &physical,
        &face_entities,
        TERMINAL_RECEIVER,
        None,
        &executor,
    )?;
    let (continuous, assembly_receipt) =
        assemble_support_presentation_with_cpu(&current_cut.assembly, &executor)?;
    let mut all_receivers = current_cut
        .assembly
        .faces
        .keys()
        .copied()
        .collect::<BTreeSet<_>>();
    let mut phases = receiver_phases(physical.standing());
    phases.retain(|receiver, _| all_receivers.contains(receiver));
    let (cuda, initial_traces, cuda_admission) = CudaApertureExecutor::new()?.admit(
        &continuous,
        &specification,
        &all_receivers,
        &executor,
    )?;
    let mut tube_atlas = TerminalTubeAtlas::new();
    let initial_tube_plan = tube_atlas.plan(
        physical.standing().event,
        &current_cut.assembly,
        &specification,
        &current_cut.topologies,
        &current_cut.source_sections,
        &current_cut.formations,
    )?;
    let initial_render = receipt_from_cuda_traces(&initial_traces, cuda_admission);
    let initial_tube_radiation = tube_atlas.commit(initial_tube_plan, initial_traces)?;
    let mut display = compose_display(&specification, &tube_atlas, &phases)?;
    let mut refused_presentation = None::<DisplayFace>;
    let mut platform = X11Platform::new(
        specification.width,
        specification.height,
        "Holonic receiver — exact causal phase transport",
    )?;
    platform.present(&display)?;
    println!(
        "live window={}x{} aperture={}x{} backend={} arithmetic={} intermediate-bits={} host-parity={} wall-ns={} CPU-workers={} assembly-workers={} physics-workers={} source-projected={} source-reused={} source-rebased={} primitives={} local-relations={} presentation-relations={} traced-addresses={} support-queries={} tube-founded={} tube-rebased={} tube-retained={} tube-delta-addresses={} linear-workers={} causal-layers={} active-stars={} pending-frontier={} propagation-boundary={:?} hinges-changed={} faces-changed={} conics-changed={} trace={} — each supplied event closes its locally parallel causal front to exact rest, return, or open cyclic support; receiver bodies move in the field; drag transports; arrows precess; W/S or wheel supply depth current; Esc closes",
        display.width,
        display.height,
        specification.width,
        specification.height,
        initial_render.backend,
        initial_render.device_arithmetic,
        initial_render.intermediate_bits,
        initial_render.host_parity,
        initial_render.wall_nanoseconds,
        workers,
        assembly_receipt.workers_used,
        radiation.cpu_execution.workers_used,
        current_cut.projected_faces,
        current_cut.reused_faces,
        current_cut.rebased_faces,
        continuous.primitives.len(),
        current_cut
            .assembly
            .faces
            .values()
            .map(|face| face.arrangement.relations.len())
            .sum::<usize>(),
        continuous.relations.len(),
        initial_render.traced_addresses,
        initial_render.exact_support_queries,
        initial_tube_radiation.receipt.founded,
        initial_tube_radiation.receipt.rebased,
        initial_tube_radiation.receipt.retained,
        initial_tube_radiation.receipt.changed_addresses,
        initial_render.trace_workers_used,
        radiation.causal_layers.len(),
        radiation.active_hinges.len(),
        radiation.open_frontier.len(),
        radiation.propagation_boundary,
        radiation.kinematic.changed_hinges.len(),
        radiation.kinematic.changed_faces.len(),
        radiation.kinematic.changed_conics.len(),
        research_trace.path.display(),
    );

    loop {
        let primary_receiver = TERMINAL_RECEIVER;
        while let Some(input) = platform.next_input()? {
            match input {
                RawPlatformInput::CloseRequested
                | RawPlatformInput::Key {
                    physical_code: 9,
                    pressed: true,
                    ..
                } => return Ok(()),
                RawPlatformInput::PointerButton {
                    at,
                    button: 1,
                    pressed,
                } => {
                    if refused_presentation.is_some() {
                        dragging = false;
                        pending_drag = None;
                        continue;
                    }
                    dragging = pressed;
                    if pressed {
                        pending_drag = Some((at, 0, 0));
                        let current_support = tube_atlas.support_presentation(
                            "star-local receiver sections in the terminal overlap component",
                        );
                        let member =
                            classify_presentation_address(&current_support, &specification, at)?;
                        println!(
                            "selected ({},{}) supported-faces={} linear-phases={} quadratic-phases={} depth-phases={}",
                            at.column,
                            at.row,
                            member.primitives.len(),
                            member.coordinate_fields.len(),
                            member.quadratic_phases.len(),
                            member.depth_phases.len(),
                        );
                    } else if let Some((origin, horizontal, vertical)) = pending_drag.take()
                        && (horizontal != 0 || vertical != 0)
                    {
                        let (width, height) = platform.extent();
                        let coordinates =
                            relative_pointer_chord(horizontal, vertical, width, height);
                        enqueue_traversal(
                            &mut pending_actions,
                            physical.standing(),
                            primary_receiver,
                            vec![ReceiverTraversalStep::Translate { coordinates }],
                        )?;
                        let _ = origin;
                    }
                }
                RawPlatformInput::PointerCounts {
                    horizontal,
                    vertical,
                    ..
                } if dragging => {
                    if let Some(accumulated) = &mut pending_drag {
                        accumulated.1 += horizontal;
                        accumulated.2 += vertical;
                    }
                }
                RawPlatformInput::Key {
                    physical_code,
                    pressed: true,
                    ..
                } if matches!(physical_code, 111 | 113 | 114 | 116) => {
                    let (axis, hand) = match physical_code {
                        111 => (ReceiverRotationAxis::X, -1),
                        113 => (ReceiverRotationAxis::Y, -1),
                        114 => (ReceiverRotationAxis::Y, 1),
                        116 => (ReceiverRotationAxis::X, 1),
                        _ => unreachable!(),
                    };
                    enqueue_traversal(
                        &mut pending_actions,
                        physical.standing(),
                        primary_receiver,
                        vec![ReceiverTraversalStep::Rotate {
                            axis,
                            ratio: ProjectiveRatio::from_rat(&(integer(hand) / integer(16))),
                        }],
                    )?;
                }
                RawPlatformInput::Key {
                    physical_code,
                    pressed: true,
                    ..
                } if matches!(physical_code, 25 | 39) => {
                    let hand = if physical_code == 25 { 1 } else { -1 };
                    enqueue_traversal(
                        &mut pending_actions,
                        physical.standing(),
                        primary_receiver,
                        vec![ReceiverTraversalStep::Translate {
                            coordinates: RatVec3::new(
                                Rat::zero(),
                                Rat::zero(),
                                integer(hand) / integer(16),
                            ),
                        }],
                    )?;
                }
                RawPlatformInput::ScrollCounts { vertical, .. } if vertical != 0 => {
                    enqueue_traversal(
                        &mut pending_actions,
                        physical.standing(),
                        primary_receiver,
                        vec![ReceiverTraversalStep::Translate {
                            coordinates: RatVec3::new(
                                Rat::zero(),
                                Rat::zero(),
                                Rat::from_integer(vertical.into()) / integer(32),
                            ),
                        }],
                    )?;
                }
                RawPlatformInput::Resize { width, height } if width > 0 && height > 0 => {
                    let proposed_specification = terminal(width, height);
                    let proposed: Result<_, Box<dyn std::error::Error>> = (|| {
                        let plan = tube_atlas.plan(
                            physical.standing().event,
                            &current_cut.assembly,
                            &proposed_specification,
                            &current_cut.topologies,
                            &current_cut.source_sections,
                            &current_cut.formations,
                        )?;
                        let (traces, receipt) =
                            trace_tube_plan(&cuda, &proposed_specification, &plan, &executor)?;
                        Ok((plan, traces, receipt))
                    })();
                    match proposed {
                        Ok((plan, traces, cuda_receipt)) => {
                            let render = cuda_receipt
                                .map(|receipt| receipt_from_cuda_traces(&traces, receipt));
                            let tube_radiation = tube_atlas.commit(plan, traces)?;
                            let render = render.unwrap_or_else(|| {
                                retained_aperture_receipt(&tube_radiation.receipt)
                            });
                            specification = proposed_specification;
                            display = compose_display(&specification, &tube_atlas, &phases)?;
                            refused_presentation = None;
                            platform.present(&display)?;
                            println!(
                                "resize event={event} aperture={}x{} backend={} arithmetic={} intermediate-bits={} wall-ns={} traced-addresses={} support-queries={} tube-retraced={} tube-delta-addresses={} linear-workers={}",
                                specification.width,
                                specification.height,
                                render.backend,
                                render.device_arithmetic,
                                render.intermediate_bits,
                                render.wall_nanoseconds,
                                render.traced_addresses,
                                render.exact_support_queries,
                                tube_radiation.receipt.traced_receivers,
                                tube_radiation.receipt.changed_addresses,
                                render.trace_workers_used,
                            );
                        }
                        Err(error) => {
                            let refusal = refusal_display(width, height)?;
                            platform.present(&refusal)?;
                            refused_presentation = Some(refusal);
                            eprintln!(
                                "resize-refused event={event} requested-aperture={}x{} error={error}; exact standing and its last valid face remain retained behind an explicit outer refusal carrier",
                                proposed_specification.width, proposed_specification.height,
                            );
                        }
                    }
                }
                RawPlatformInput::RedrawRequested => {
                    platform.present(refused_presentation.as_ref().unwrap_or(&display))?
                }
                _ => {}
            }
        }

        if let Some(action) = pending_actions.pop_front() {
            let event_id = EventId(event + 1);
            let received = physical.receive(&LocalStarEvent {
                event: event_id,
                source_currents: BTreeMap::new(),
                receiver_deeds: vec![action.deed],
                receiver_population: Vec::new(),
                topology_deeds: Vec::new(),
            });
            let receipt = match received {
                Ok(receipt) => receipt,
                Err(error @ LocalStarError::StaleReceiverTraversalChart { .. }) => {
                    eprintln!(
                        "input-refused source-receiver={} error={error}",
                        action.source.0
                    );
                    continue;
                }
                Err(error) => return Err(Box::new(error)),
            };
            event += 1;
            let physical_radiation = Some(
                receipt
                    .radiation
                    .into_iter()
                    .next()
                    .expect("one local-star event emits one complete radiation"),
            );
            sync_construction(
                &mut construction,
                &face_entities,
                physical.standing(),
                &face_vertices,
            )?;
            current_cut = support_assembly(
                &construction,
                frame,
                &physical,
                &face_entities,
                TERMINAL_RECEIVER,
                Some(&tube_atlas),
                &executor,
            )?;
            all_receivers = current_cut.assembly.faces.keys().copied().collect();
            let previous_phases = phases.clone();
            phases = receiver_phases(physical.standing());
            phases.retain(|receiver, _| all_receivers.contains(receiver));
            let rendered = reconcile_tubes(
                &cuda,
                physical.standing().event,
                &current_cut.assembly,
                &specification,
                &current_cut.topologies,
                &current_cut.source_sections,
                &current_cut.formations,
                &mut tube_atlas,
                &executor,
            );
            match rendered {
                Ok((tube_radiation, render)) => {
                    let affected = affected_terminal_addresses(
                        &tube_atlas,
                        &tube_radiation,
                        &previous_phases,
                        &phases,
                    );
                    let patches = update_display_patches(
                        &mut display,
                        &specification,
                        &tube_atlas,
                        &phases,
                        &affected,
                    )?;
                    if refused_presentation.is_none() {
                        platform.present_patches(&patches)?;
                    }
                    research_trace.record(ResearchTraceEvent {
                        event,
                        kind: "boundary",
                        physical: &physical,
                        radiation: physical_radiation.as_ref(),
                        atlas: &tube_atlas,
                        render: &render,
                        tubes: &tube_radiation.receipt,
                        specification: &specification,
                    })?;
                    let physical_statement = physical_radiation.as_ref().map_or_else(
                        || "physical=rest".to_owned(),
                        |radiation| {
                            let stressed_faces = radiation
                                .face_fields
                                .values()
                                .filter(|field| !field.stress.is_zero())
                                .count();
                            format!(
                                "causal-layers={} propagation-boundary={:?} active-stars={} branches={} next-frontier={} stressed-faces={} moved-receivers={} rewrites={} changed-conics={} physics-workers={}",
                                radiation.causal_layers.len(),
                                radiation.propagation_boundary,
                                radiation.active_hinges.len(),
                                radiation
                                    .current_balances
                                    .iter()
                                    .map(|balance| balance.emitted.len())
                                    .sum::<usize>(),
                                radiation.open_frontier.len(),
                                stressed_faces,
                                radiation
                                    .receiver_worldlines
                                    .iter()
                                    .filter(|step| {
                                        step.position_before != step.position_after
                                            || step.orientation_before != step.orientation_after
                                    })
                                    .count(),
                                radiation.rewrite_candidates.len(),
                                radiation.kinematic.changed_conics.len(),
                                radiation.cpu_execution.workers_used,
                            )
                        },
                    );
                    println!(
                        "event {event}: source-receiver={} {physical_statement} backend={} arithmetic={} intermediate-bits={} wall-ns={} presentation-materialized-receivers={} presentation-materialized-primitives={} source-projected={} source-reused={} source-rebased={} traced-addresses={} support-queries={} tube-founded={} tube-deformed={} tube-transported={} tube-rebased={} tube-retained={} tube-departed={} tube-reused-addresses={} tube-avoided-queries={} tube-delta-addresses={} linear-workers={}",
                        action.source.0,
                        render.backend,
                        render.device_arithmetic,
                        render.intermediate_bits,
                        render.wall_nanoseconds,
                        tube_radiation.receipt.materialized_receivers,
                        tube_radiation.receipt.materialized_primitives,
                        current_cut.projected_faces,
                        current_cut.reused_faces,
                        current_cut.rebased_faces,
                        render.traced_addresses,
                        render.exact_support_queries,
                        tube_radiation.receipt.founded,
                        tube_radiation.receipt.deformed,
                        tube_radiation.receipt.transported,
                        tube_radiation.receipt.rebased,
                        tube_radiation.receipt.retained,
                        tube_radiation.receipt.departed,
                        tube_radiation.receipt.reused_addresses,
                        tube_radiation.receipt.avoided_support_queries,
                        tube_radiation.receipt.changed_addresses,
                        render.trace_workers_used,
                    );
                }
                Err(error) => {
                    eprintln!(
                        "presentation-refused event={event} error={error}; physical and receiver standing remain exact and the last valid presentation remains"
                    );
                }
            }
        }
        thread::sleep(Duration::from_millis(2));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_same_relative_device_chord_is_resolution_independent() {
        assert_eq!(
            relative_pointer_chord(64, -40, 640, 400),
            relative_pointer_chord(128, -80, 1280, 800)
        );
    }

    #[test]
    fn one_chart_collects_an_ordered_word_and_compresses_only_identical_runs() {
        let ecology = build_ecology(CpuExecutor::serial()).unwrap();
        let x = ReceiverTraversalStep::Rotate {
            axis: ReceiverRotationAxis::X,
            ratio: ProjectiveRatio::from_rat(&(integer(1) / integer(16))),
        };
        let y = ReceiverTraversalStep::Rotate {
            axis: ReceiverRotationAxis::Y,
            ratio: ProjectiveRatio::from_rat(&(integer(1) / integer(16))),
        };
        let mut pending = VecDeque::new();
        enqueue_traversal(
            &mut pending,
            ecology.physical.standing(),
            TERMINAL_RECEIVER,
            vec![x.clone()],
        )
        .unwrap();
        enqueue_traversal(
            &mut pending,
            ecology.physical.standing(),
            TERMINAL_RECEIVER,
            vec![x.clone(), y.clone(), x.clone()],
        )
        .unwrap();
        assert_eq!(pending.len(), 1);
        assert_eq!(
            pending[0].deed.traversal.steps,
            vec![
                ReceiverTraversalStep::Repeat {
                    generator: Box::new(x.clone()),
                    repetitions: BigUint::from(2_u8),
                },
                y,
                x,
            ]
        );
    }

    #[test]
    fn native_aperture_and_sparse_patch_have_complete_exact_authority() {
        let executor = CpuExecutor::serial();
        let ecology = build_ecology(executor).unwrap();
        let cut = support_assembly(
            &ecology.construction,
            ecology.frame,
            &ecology.physical,
            &ecology.face_entities,
            TERMINAL_RECEIVER,
            None,
            &executor,
        )
        .unwrap();
        let presentation = assemble_support_presentation_with_cpu(&cut.assembly, &executor)
            .unwrap()
            .0;
        // The former production quotient stopped at width 640. This exact
        // aperture crosses that boundary while remaining shallow enough to be
        // a fast deterministic correctness grade.
        let specification = terminal(641, 4);
        let receivers = cut.assembly.faces.keys().copied().collect::<BTreeSet<_>>();
        let authority = holonic_engine::trace_receivers_aperture_with_cpu(
            &presentation,
            &specification,
            &receivers,
            &executor,
        )
        .unwrap()
        .0;
        let mut atlas = TerminalTubeAtlas::new();
        let plan = atlas
            .plan(
                ecology.physical.standing().event,
                &cut.assembly,
                &specification,
                &cut.topologies,
                &cut.source_sections,
                &cut.formations,
            )
            .unwrap();
        assert_eq!(
            plan.trace_presentation().primitives,
            presentation.primitives
        );
        assert_eq!(plan.materialized_receivers(), receivers.len());
        let radiation = atlas.commit(plan, authority.clone()).unwrap();
        assert_eq!(atlas.specification.as_ref(), Some(&specification));
        assert_eq!(atlas.traces(), authority);

        let phases = receiver_phases(ecology.physical.standing());
        let mut changed_phases = phases.clone();
        changed_phases.insert(TERMINAL_RECEIVER, RatVec3::from_i64(17, -5, 2));
        let initial = compose_display(&specification, &atlas, &phases).unwrap();
        assert_eq!((initial.width, initial.height), (641, 4));
        let affected = affected_terminal_addresses(&atlas, &radiation, &phases, &changed_phases);
        let mut patched = initial;
        let patches = update_display_patches(
            &mut patched,
            &specification,
            &atlas,
            &changed_phases,
            &affected,
        )
        .unwrap();
        assert!(!patches.is_empty());
        assert_eq!(
            patched,
            compose_display(&specification, &atlas, &changed_phases).unwrap()
        );
        let heights = trace_arithmetic_heights(ecology.physical.standing(), &atlas);
        assert!(heights.trajectory > 0);
        assert!(heights.receiver_spin > 0);
        assert!(heights.presentation_factor > 0);
        assert!(heights.presented_support > 0);
        eprintln!(
            "native-exact-receiver aperture={}x{} tubes={} support-addresses={} changed-addresses={} patches={} trajectory-bits={} translation-bits={} spin-bits={} phase-bits={} presentation-factor-bits={} presented-support-bits={}",
            specification.width,
            specification.height,
            atlas.tubes.len(),
            atlas
                .traces()
                .values()
                .map(|trace| trace.addresses.len())
                .sum::<usize>(),
            radiation.receipt.changed_addresses,
            patches.len(),
            heights.trajectory,
            heights.receiver_translation,
            heights.receiver_spin,
            heights.receiver_phase,
            heights.presentation_factor,
            heights.presented_support,
        );
    }

    #[test]
    fn desktop_shapes_are_emitted_by_one_propagating_local_star_ecology() {
        let mut ecology = build_ecology(CpuExecutor::serial()).unwrap();
        assert_eq!(
            ecology
                .construction
                .entities
                .values()
                .filter(|entity| matches!(entity.geometry, Geometry::Triangle { .. }))
                .count(),
            8
        );
        assert_eq!(ecology.physical.standing().kinematic.conics.cells.len(), 3);
        assert_eq!(ecology.radiation.causal_layers[0].active_hinges.len(), 1);
        assert!(ecology.radiation.causal_layers.len() > 1);
        assert!(ecology.radiation.open_frontier.is_empty());
        assert!(matches!(
            ecology.radiation.propagation_boundary,
            holonic_engine::LocalPropagationBoundary::Rest { .. }
        ));
        assert!(ecology.radiation.kinematic.changed_hinges.len() > 1);
        assert!(ecology.radiation.kinematic.changed_faces.len() > 2);
        assert!(
            ecology
                .radiation
                .current_balances
                .iter()
                .all(|balance| balance.exact_residual.is_zero())
        );
        assert!(ecology.radiation.cpu_execution.tasks > BigUint::from(1_u8));
        sync_construction(
            &mut ecology.construction,
            &ecology.face_entities,
            ecology.physical.standing(),
            &ecology.face_vertices,
        )
        .unwrap();

        let cut = support_assembly(
            &ecology.construction,
            ecology.frame,
            &ecology.physical,
            &ecology.face_entities,
            TERMINAL_RECEIVER,
            None,
            &CpuExecutor::serial(),
        )
        .unwrap();
        let continuous = assemble_presentation_with_cpu(&cut.assembly, &CpuExecutor::serial())
            .unwrap()
            .0;
        let specification = terminal(640, 400);
        let executor = CpuExecutor::multicore(NonZeroUsize::new(12).unwrap());
        let phases = receiver_phases(ecology.physical.standing());
        assert_ne!(phases[&ReceiverId(1)], phases[&ReceiverId(2)]);
        assert_ne!(
            phase_color(&phases[&ReceiverId(1)], &BigUint::from(1_u8)),
            phase_color(&phases[&ReceiverId(2)], &BigUint::from(1_u8)),
        );
        let (traces, receipt) = render_receiver_traces(
            &continuous,
            &specification,
            &BTreeSet::from([ReceiverId(1), ReceiverId(2)]),
            &executor,
        )
        .unwrap();
        assert!(traces.values().all(|trace| !trace.addresses.is_empty()));
        assert!(
            receipt.traced_addresses
                < BigUint::from(
                    usize::try_from(specification.width * specification.height)
                        .expect("the bounded test aperture fits memory")
                        * 2
                        / 4
                )
        );
        assert!(receipt.trace_workers_used > BigUint::from(1_u8));
    }

    #[test]
    fn terminal_receiver_relation_is_explicit_not_container_order() {
        let ecology = build_ecology(CpuExecutor::serial()).unwrap();
        let specifications = [ReceiverId(2), ReceiverId(1)]
            .into_iter()
            .map(|receiver| {
                receiver_specification(ecology.frame, receiver, ecology.physical.standing())
            })
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let relations = receiver_relations(
            &specifications,
            ecology.physical.standing(),
            TERMINAL_RECEIVER,
        )
        .unwrap()
        .into_iter()
        .map(|relation| (relation.receiver, relation))
        .collect::<BTreeMap<_, _>>();
        assert_eq!(
            relations[&TERMINAL_RECEIVER].into_presentation,
            RatMat3::identity()
        );
    }

    #[test]
    fn receiver_faces_compute_every_oriented_organ_and_overlap_seam() {
        let executor = CpuExecutor::serial();
        let ecology = build_ecology(executor.clone()).unwrap();
        let cut = support_assembly(
            &ecology.construction,
            ecology.frame,
            &ecology.physical,
            &ecology.face_entities,
            TERMINAL_RECEIVER,
            None,
            &executor,
        )
        .unwrap();
        for face in cut.assembly.faces.values() {
            let cover = face
                .acceptance
                .as_ref()
                .expect("a local-star face retains its caused directional cover");
            assert_eq!(cover.organs.len(), 4);
            assert_eq!(cover.seams.len(), 4);
            let section = face.receive_acceptance_section().unwrap();
            assert_eq!(section.event, ecology.physical.standing().event);
            assert_eq!(section.organs.len(), cover.organs.len());
            assert_eq!(section.seams.len(), cover.seams.len());
        }
    }

    #[test]
    fn exact_standing_source_faces_are_reused_before_projection() {
        let executor = CpuExecutor::serial();
        let mut ecology = build_ecology(executor).unwrap();
        let specification = terminal(32, 24);
        let initial = support_assembly(
            &ecology.construction,
            ecology.frame,
            &ecology.physical,
            &ecology.face_entities,
            TERMINAL_RECEIVER,
            None,
            &executor,
        )
        .unwrap();
        assert_eq!(initial.projected_faces, 2);
        assert_eq!(initial.reused_faces, 0);
        let presentation = assemble_support_presentation_with_cpu(&initial.assembly, &executor)
            .unwrap()
            .0;
        let mut atlas = TerminalTubeAtlas::new();
        let plan = atlas
            .plan(
                ecology.physical.standing().event,
                &initial.assembly,
                &specification,
                &initial.topologies,
                &initial.source_sections,
                &initial.formations,
            )
            .unwrap();
        let traces = holonic_engine::trace_receivers_aperture_with_cpu(
            &presentation,
            &specification,
            plan.trace_receivers(),
            &executor,
        )
        .unwrap()
        .0;
        atlas.commit(plan, traces).unwrap();

        let repeated = support_assembly(
            &ecology.construction,
            ecology.frame,
            &ecology.physical,
            &ecology.face_entities,
            TERMINAL_RECEIVER,
            Some(&atlas),
            &executor,
        )
        .unwrap();
        assert_eq!(repeated.projected_faces, 0);
        assert_eq!(repeated.reused_faces, 2);
        assert_eq!(repeated.assembly, initial.assembly);

        let next_event = EventId(ecology.physical.standing().event.0 + 1);
        ecology
            .physical
            .receive(&LocalStarEvent::continuation(next_event))
            .unwrap();
        let carried = support_assembly(
            &ecology.construction,
            ecology.frame,
            &ecology.physical,
            &ecology.face_entities,
            TERMINAL_RECEIVER,
            Some(&atlas),
            &executor,
        )
        .unwrap();
        assert_eq!(carried.projected_faces, 0);
        assert_eq!(carried.reused_faces, 2);
        assert!(carried.formations.values().all(|formation| matches!(
            formation.cause(),
            ReceiverFaceFormationCause::Retained { .. }
        )));
        let plan = atlas
            .plan(
                next_event,
                &carried.assembly,
                &specification,
                &carried.topologies,
                &carried.source_sections,
                &carried.formations,
            )
            .unwrap();
        assert!(plan.trace_primitive_keys().is_empty());
        let radiation = atlas.commit(plan, BTreeMap::new()).unwrap();
        assert_eq!(radiation.transitions.len(), 2);
        assert!(
            radiation
                .transitions
                .iter()
                .all(|transition| transition.event == next_event
                    && transition.terminal_trace_carried)
        );

        let previous_phases = receiver_phases(ecology.physical.standing());
        let mut changed_phases = previous_phases.clone();
        changed_phases.insert(ReceiverId(1), RatVec3::from_i64(101, 7, -3));
        let initial_display = compose_display(&specification, &atlas, &previous_phases).unwrap();
        assert_eq!(
            (initial_display.width, initial_display.height),
            (specification.width, specification.height)
        );
        let affected =
            affected_terminal_addresses(&atlas, &radiation, &previous_phases, &changed_phases);
        let mut patched = initial_display.clone();
        let patches = update_display_patches(
            &mut patched,
            &specification,
            &atlas,
            &changed_phases,
            &affected,
        )
        .unwrap();
        assert!(!patches.is_empty());
        assert_eq!(
            patched,
            compose_display(&specification, &atlas, &changed_phases).unwrap()
        );
        let mut platform = MemoryPlatform::new(specification.width, specification.height).unwrap();
        platform.present(&initial_display).unwrap();
        platform.present_patches(&patches).unwrap();
        assert_eq!(platform.presented(), Some(&patched));

        let no_change =
            affected_terminal_addresses(&atlas, &radiation, &changed_phases, &changed_phases);
        let no_patches = update_display_patches(
            &mut patched,
            &specification,
            &atlas,
            &changed_phases,
            &no_change,
        )
        .unwrap();
        assert!(no_patches.is_empty());
    }

    #[test]
    fn a_discriminant_opening_does_not_fabricate_a_receiver() {
        let executor = CpuExecutor::multicore(NonZeroUsize::new(4).unwrap());
        let mut ecology = build_ecology(executor).unwrap();
        let driven = ecology.radiation.active_hinges[0];
        let radiation = ecology
            .physical
            .receive(&LocalStarEvent {
                event: EventId(3),
                source_currents: BTreeMap::from([(driven, integer(-100))]),
                receiver_deeds: Vec::new(),
                receiver_population: Vec::new(),
                topology_deeds: Vec::new(),
            })
            .unwrap()
            .radiation
            .remove(0);
        assert!(!radiation.rewrite_candidates.is_empty());
        assert_eq!(ecology.physical.standing().receivers.len(), 2);
        ecology
            .physical
            .receive(&LocalStarEvent {
                event: EventId(4),
                source_currents: BTreeMap::new(),
                receiver_deeds: Vec::new(),
                receiver_population: Vec::new(),
                topology_deeds: Vec::new(),
            })
            .unwrap();
        assert_eq!(ecology.physical.standing().receivers.len(), 2);
        sync_construction(
            &mut ecology.construction,
            &ecology.face_entities,
            ecology.physical.standing(),
            &ecology.face_vertices,
        )
        .unwrap();
        let cut = support_assembly(
            &ecology.construction,
            ecology.frame,
            &ecology.physical,
            &ecology.face_entities,
            TERMINAL_RECEIVER,
            None,
            &executor,
        )
        .unwrap();
        assert_eq!(cut.assembly.faces.len(), 2);
        assert_eq!(cut.assembly.relations.len(), 2);
        assert!(!cut.assembly.faces.contains_key(&ReceiverId(3)));
        assert!(
            cut.source_sections
                .values()
                .all(|section| section.entities.len() == 4)
        );
        let whole_source_carriers = ecology.physical.standing().receivers.len()
            * (ecology.construction.entities.len()
                + ecology.physical.standing().kinematic.conics.cells.len());
        let intrinsic_source_carriers = cut
            .source_sections
            .values()
            .map(|section| section.entities.len() + section.conics.len())
            .sum::<usize>();
        assert!(intrinsic_source_carriers < whole_source_carriers);
        eprintln!(
            "receiver-source-cut receivers={} whole-cartesian-carriers={} intrinsic-carriers={} local-crossings={}",
            cut.source_sections.len(),
            whole_source_carriers,
            intrinsic_source_carriers,
            cut.assembly
                .faces
                .values()
                .map(|face| face.arrangement.relations.len())
                .sum::<usize>(),
        );
        assert!(
            cut.assembly
                .faces
                .values()
                .any(|face| !face.arrangement.relations.is_empty())
        );
    }

    #[test]
    #[ignore = "requires a visible CUDA device"]
    fn cuda_packed_support_is_exact_and_wide_input_falls_back_without_loss() {
        let receivers = BTreeSet::from([ReceiverId(1), ReceiverId(2)]);
        let initial_specification = terminal(640, 400);
        let executor = CpuExecutor::multicore(NonZeroUsize::new(12).unwrap());
        let mut ecology = build_ecology(executor).unwrap();

        let initial_assembly = support_assembly(
            &ecology.construction,
            ecology.frame,
            &ecology.physical,
            &ecology.face_entities,
            TERMINAL_RECEIVER,
            None,
            &executor,
        )
        .unwrap();
        let rat_bits = |value: &Rat| {
            value
                .numer()
                .magnitude()
                .bits()
                .max(value.denom().magnitude().bits())
        };
        for (receiver, relation) in &initial_assembly.assembly.relations {
            let relation_bits = relation
                .into_presentation
                .rows
                .iter()
                .flatten()
                .map(&rat_bits)
                .max()
                .unwrap_or(0);
            let local_bits = initial_assembly.assembly.faces[receiver]
                .arrangement
                .primitives
                .iter()
                .flat_map(|primitive| match primitive {
                    holonic_engine::ReceiverPrimitive::Triangle(triangle) => triangle
                        .vertices
                        .iter()
                        .flat_map(|point| [&point.x, &point.y, &point.w])
                        .map(&rat_bits)
                        .collect::<Vec<_>>(),
                    holonic_engine::ReceiverPrimitive::Thread(thread) => thread
                        .vertices
                        .iter()
                        .flat_map(|point| [&point.x, &point.y, &point.w])
                        .map(&rat_bits)
                        .collect::<Vec<_>>(),
                    holonic_engine::ReceiverPrimitive::Conic(conic) => [
                        &conic.form.xx,
                        &conic.form.xy,
                        &conic.form.yy,
                        &conic.form.xw,
                        &conic.form.yw,
                        &conic.form.ww,
                    ]
                    .into_iter()
                    .map(&rat_bits)
                    .collect::<Vec<_>>(),
                })
                .max()
                .unwrap_or(0);
            let intrinsic_support_bits = initial_assembly.assembly.faces[receiver]
                .arrangement
                .primitives
                .iter()
                .flat_map(|primitive| match primitive {
                    holonic_engine::ReceiverPrimitive::Triangle(triangle) => [
                        triangle.vertices[0].cross(&triangle.vertices[1]),
                        triangle.vertices[1].cross(&triangle.vertices[2]),
                        triangle.vertices[2].cross(&triangle.vertices[0]),
                    ]
                    .into_iter()
                    .flat_map(|line| [line.a, line.b, line.c])
                    .map(|value| value.numer().magnitude().bits())
                    .collect::<Vec<_>>(),
                    holonic_engine::ReceiverPrimitive::Thread(thread) => thread
                        .vertices
                        .windows(2)
                        .flat_map(|edge| {
                            let line = edge[0].cross(&edge[1]);
                            [line.a, line.b, line.c]
                        })
                        .map(|value| value.numer().magnitude().bits())
                        .collect::<Vec<_>>(),
                    holonic_engine::ReceiverPrimitive::Conic(conic) => conic
                        .form
                        .coefficients()
                        .into_iter()
                        .map(|value| value.numer().magnitude().bits())
                        .collect::<Vec<_>>(),
                })
                .max()
                .unwrap_or(0);
            eprintln!(
                "local-carrier receiver={} relation-bits={} primitive-bits={} intrinsic-support-bits={}",
                receiver.0, relation_bits, local_bits, intrinsic_support_bits
            );
        }
        let initial = assemble_support_presentation_with_cpu(&initial_assembly.assembly, &executor)
            .unwrap()
            .0;
        let admission_started = Instant::now();
        let (cuda, initial_trace, initial_receipt) = CudaApertureExecutor::new()
            .unwrap()
            .admit(&initial, &initial_specification, &receivers, &executor)
            .unwrap();
        let admission_nanoseconds = admission_started.elapsed().as_nanos();
        assert_eq!(
            cuda.preferred_backend(),
            ApertureExecutionBackend::ExactHost
        );
        assert!(initial_receipt.host_parity);
        assert!(initial_receipt.intermediate_bits > BigUint::from(384_u16));
        assert!(initial_receipt.host_primitives > BigUint::from(0_u8));
        assert!(
            initial_receipt
                .device_arithmetic
                .contains("exact host integer-projective")
        );
        let packed_specification = terminal(32, 24);
        let packed_receivers = BTreeSet::from([ReceiverId(1)]);
        let packed_form = holonic_engine::HomogeneousConic::new([
            integer(1),
            integer(0),
            integer(1),
            integer(0),
            integer(0),
            integer(-1),
        ])
        .unwrap();
        let packed_presentation = ContinuousPresentation {
            schema: "holonic-engine.cuda-packed-support-grade.v1".to_owned(),
            boundary_name: "small exact card carrier".to_owned(),
            primitives: vec![holonic_engine::PresentedPrimitive {
                receiver: ReceiverId(1),
                primitive: ReceiverPrimitive::Conic(holonic_engine::ProjectedConic {
                    source: holonic_engine::ReceiverPrimitiveId::NativeConic(
                        holonic_engine::ConicCellId(999),
                    ),
                    class_in_receiver_chart: packed_form.classify(),
                    form: packed_form,
                    receiver_depth: holonic_engine::ProjectiveDepthLaw {
                        numerator: holonic_engine::ProjectiveLine2::homogeneous(
                            integer(0),
                            integer(0),
                            integer(1),
                        ),
                        denominator: holonic_engine::ProjectiveLine2::homogeneous(
                            integer(0),
                            integer(0),
                            integer(1),
                        ),
                    },
                }),
            }],
            coordinate_fields: Vec::new(),
            relations: Vec::new(),
            seams: Vec::new(),
        };
        let packed_authority = holonic_engine::trace_receivers_aperture_with_cpu(
            &packed_presentation,
            &packed_specification,
            &packed_receivers,
            &executor,
        )
        .unwrap()
        .0;
        let (packed_initial_trace, packed_initial_receipt) = cuda
            .trace_hybrid(
                &packed_presentation,
                &packed_specification,
                &packed_receivers,
                &executor,
            )
            .unwrap();
        assert!(packed_initial_receipt.device_primitives > BigUint::from(0_u8));
        assert!(
            packed_initial_receipt
                .execution_backend
                .contains("hybrid CUDA")
        );
        assert!(
            packed_initial_trace
                .iter()
                .all(|(receiver, trace)| trace.has_same_exact_support(&packed_authority[receiver]))
        );
        let support_words = packed_specification
            .width
            .checked_mul(packed_specification.height)
            .unwrap()
            .div_ceil(u32::BITS);
        assert_eq!(
            packed_initial_receipt.device_output_bytes,
            &packed_initial_receipt.device_primitives
                * BigUint::from(support_words)
                * BigUint::from(std::mem::size_of::<u32>())
        );

        let input_started = Instant::now();
        let deed = pending_traversal(
            ecology.physical.standing(),
            ReceiverId(1),
            vec![ReceiverTraversalStep::Rotate {
                axis: ReceiverRotationAxis::X,
                ratio: ProjectiveRatio::from_rat(&(integer(1) / integer(16))),
            }],
        )
        .unwrap()
        .deed;
        let input_nanoseconds = input_started.elapsed().as_nanos();
        let physics_started = Instant::now();
        ecology
            .physical
            .receive(&LocalStarEvent {
                event: EventId(3),
                source_currents: BTreeMap::new(),
                receiver_deeds: vec![deed],
                receiver_population: Vec::new(),
                topology_deeds: Vec::new(),
            })
            .unwrap();
        let physics_nanoseconds = physics_started.elapsed().as_nanos();
        let sync_started = Instant::now();
        sync_construction(
            &mut ecology.construction,
            &ecology.face_entities,
            ecology.physical.standing(),
            &ecology.face_vertices,
        )
        .unwrap();
        let sync_nanoseconds = sync_started.elapsed().as_nanos();
        let assembly_started = Instant::now();
        let successor_assembly = support_assembly(
            &ecology.construction,
            ecology.frame,
            &ecology.physical,
            &ecology.face_entities,
            TERMINAL_RECEIVER,
            None,
            &executor,
        )
        .unwrap();
        let assembly_nanoseconds = assembly_started.elapsed().as_nanos();
        let presentation_started = Instant::now();
        let successor =
            assemble_support_presentation_with_cpu(&successor_assembly.assembly, &executor)
                .unwrap()
                .0;
        let presentation_nanoseconds = presentation_started.elapsed().as_nanos();
        let resized_specification = terminal(640, 720);
        let (card_trace, card_receipt) = cuda
            .trace_hybrid(&successor, &resized_specification, &receivers, &executor)
            .unwrap();
        let selected_started = Instant::now();
        let (selected_trace, selected_receipt) = cuda
            .trace(&successor, &resized_specification, &receivers, &executor)
            .unwrap();
        let selected_nanoseconds = selected_started.elapsed().as_nanos();
        let host_trace = holonic_engine::trace_receivers_aperture_with_rational_conic_authority(
            &successor,
            &resized_specification,
            &receivers,
            &executor,
        )
        .unwrap()
        .0;
        eprintln!(
            "successor-carriers device={} host={} conics={} linear={} bits={} arithmetic={}",
            card_receipt.device_primitives,
            card_receipt.host_primitives,
            card_receipt.host_conics,
            card_receipt.host_linear_primitives,
            card_receipt.intermediate_bits,
            card_receipt.device_arithmetic,
        );

        assert_ne!(initial_trace, card_trace);
        assert!(card_receipt.intermediate_bits > BigUint::from(127_u8));
        assert_eq!(
            &card_receipt.device_primitives + &card_receipt.host_primitives,
            card_receipt.selected_primitives
        );
        if card_receipt.device_primitives.is_zero() {
            assert!(
                card_receipt
                    .device_arithmetic
                    .contains("exact host integer-projective")
            );
        } else {
            assert!(card_receipt.device_arithmetic.contains("CUDA"));
        }
        for receiver in &receivers {
            let card = &card_trace[receiver];
            let host = &host_trace[receiver];
            let selected = &selected_trace[receiver];
            assert_eq!(card.addresses, selected.addresses);
            assert_eq!(card.support_multiplicity, selected.support_multiplicity);
            assert_eq!(card.primitive_traces, selected.primitive_traces);
            assert_eq!(card.addresses, host.addresses);
            assert_eq!(card.support_multiplicity, host.support_multiplicity);
            assert_eq!(card.primitive_traces, host.primitive_traces);
            assert!(card.has_same_exact_support(host));
        }
        let layering_started = Instant::now();
        let mut display_atlas = TerminalTubeAtlas::new();
        let display_plan = display_atlas
            .plan(
                ecology.physical.standing().event,
                &successor_assembly.assembly,
                &resized_specification,
                &successor_assembly.topologies,
                &successor_assembly.source_sections,
                &successor_assembly.formations,
            )
            .unwrap();
        let _render = receipt_from_cuda_traces(&selected_trace, selected_receipt.clone());
        display_atlas.commit(display_plan, selected_trace).unwrap();
        let layering_nanoseconds = layering_started.elapsed().as_nanos();
        let composition_started = Instant::now();
        let display = compose_display(
            &resized_specification,
            &display_atlas,
            &receiver_phases(ecology.physical.standing()),
        )
        .unwrap();
        let composition_nanoseconds = composition_started.elapsed().as_nanos();
        assert_eq!(display.width, resized_specification.width);
        eprintln!(
            "causal-stage\tinput-return-ns\tphysics-ns\tsync-ns\tassembly-ns\tpresentation-ns\tlayering-ns\tcomposition-ns\tinitial-admission-ns\n\
             causal-stage\tsuccessor\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            input_nanoseconds,
            physics_nanoseconds,
            sync_nanoseconds,
            assembly_nanoseconds,
            presentation_nanoseconds,
            layering_nanoseconds,
            composition_nanoseconds,
            admission_nanoseconds,
        );
        eprintln!(
            "profile\tframe\taperture\tselected\tdevice-primitives\thost-primitives\thost-conics\thost-linear\tdevice-output-bytes\tpack-ns\tdevice-prepare-ns\tdevice-execute-ns\tdevice-download-ns\tdevice-decode-ns\thost-trace-ns\thost-merge-ns\ttotal-ns\tdevice-threads\tdevice-queries\thost-queries\n\
             profile\tinitial\t640x400\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n\
             profile\tsuccessor\t640x720\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n\
             selected\tbackend={}\ttotal-ns={}\thost-queries={}\n\
             device={} arithmetic={} intermediate-bits={}",
            initial_receipt.selected_primitives,
            initial_receipt.device_primitives,
            initial_receipt.host_primitives,
            initial_receipt.host_conics,
            initial_receipt.host_linear_primitives,
            initial_receipt.device_output_bytes,
            initial_receipt.selection_pack_nanoseconds,
            initial_receipt.device_prepare_nanoseconds,
            initial_receipt.device_execute_nanoseconds,
            initial_receipt.device_download_nanoseconds,
            initial_receipt.device_decode_nanoseconds,
            initial_receipt.host_trace_nanoseconds,
            initial_receipt.host_merge_nanoseconds,
            initial_receipt.wall_nanoseconds,
            initial_receipt.device_threads,
            initial_receipt.device_exact_support_evaluations,
            initial_receipt.host_exact_support_evaluations,
            card_receipt.selected_primitives,
            card_receipt.device_primitives,
            card_receipt.host_primitives,
            card_receipt.host_conics,
            card_receipt.host_linear_primitives,
            card_receipt.device_output_bytes,
            card_receipt.selection_pack_nanoseconds,
            card_receipt.device_prepare_nanoseconds,
            card_receipt.device_execute_nanoseconds,
            card_receipt.device_download_nanoseconds,
            card_receipt.device_decode_nanoseconds,
            card_receipt.host_trace_nanoseconds,
            card_receipt.host_merge_nanoseconds,
            card_receipt.wall_nanoseconds,
            card_receipt.device_threads,
            card_receipt.device_exact_support_evaluations,
            card_receipt.host_exact_support_evaluations,
            selected_receipt.execution_backend,
            selected_nanoseconds,
            selected_receipt.host_exact_support_evaluations,
            initial_receipt.device,
            card_receipt.device_arithmetic,
            card_receipt.intermediate_bits,
        );

        for (name, specification) in [
            ("successor-quarter", terminal(160, 180)),
            ("successor-half", terminal(320, 360)),
        ] {
            let (_, receipt) = cuda
                .trace_hybrid(&successor, &specification, &receivers, &executor)
                .unwrap();
            eprintln!(
                "scale\t{name}\t{}x{}\tpack-ns={}\tdevice-total-ns={}\thost-trace-ns={}\ttotal-ns={}\tdevice-queries={}\thost-queries={}\tdevice-output-bytes={}",
                specification.width,
                specification.height,
                receipt.selection_pack_nanoseconds,
                receipt.device_prepare_nanoseconds
                    + receipt.device_execute_nanoseconds
                    + receipt.device_download_nanoseconds
                    + receipt.device_decode_nanoseconds,
                receipt.host_trace_nanoseconds,
                receipt.wall_nanoseconds,
                receipt.device_exact_support_evaluations,
                receipt.host_exact_support_evaluations,
                receipt.device_output_bytes,
            );
        }
    }

    #[test]
    #[ignore = "exact cost profile, not a correctness gate"]
    fn exact_host_species_cost_profile() {
        let receivers = BTreeSet::from([ReceiverId(1), ReceiverId(2)]);
        let specification = terminal(640, 720);
        let executor = CpuExecutor::multicore(NonZeroUsize::new(12).unwrap());
        let mut ecology = build_ecology(executor).unwrap();
        let deed = pending_traversal(
            ecology.physical.standing(),
            ReceiverId(1),
            vec![ReceiverTraversalStep::Rotate {
                axis: ReceiverRotationAxis::X,
                ratio: ProjectiveRatio::from_rat(&(integer(1) / integer(16))),
            }],
        )
        .unwrap()
        .deed;
        ecology
            .physical
            .receive(&LocalStarEvent {
                event: EventId(3),
                source_currents: BTreeMap::new(),
                receiver_deeds: vec![deed],
                receiver_population: Vec::new(),
                topology_deeds: Vec::new(),
            })
            .unwrap();
        sync_construction(
            &mut ecology.construction,
            &ecology.face_entities,
            ecology.physical.standing(),
            &ecology.face_vertices,
        )
        .unwrap();
        let successor_assembly = support_assembly(
            &ecology.construction,
            ecology.frame,
            &ecology.physical,
            &ecology.face_entities,
            TERMINAL_RECEIVER,
            None,
            &executor,
        )
        .unwrap();
        let successor =
            assemble_support_presentation_with_cpu(&successor_assembly.assembly, &executor)
                .unwrap()
                .0;
        for (name, species_filter) in [
            ("conics", Some(true)),
            ("linear", Some(false)),
            ("all", None),
        ] {
            let mut species = successor.clone();
            if let Some(conics) = species_filter {
                species.primitives.retain(|presented| {
                    matches!(
                        &presented.primitive,
                        holonic_engine::ReceiverPrimitive::Conic(_)
                    ) == conics
                });
            }
            let started = Instant::now();
            let (traces, execution) = holonic_engine::trace_receivers_aperture_with_cpu(
                &species,
                &specification,
                &receivers,
                &executor,
            )
            .unwrap();
            let nanoseconds = started.elapsed().as_nanos();
            let queries = traces.values().fold(BigUint::from(0_u8), |sum, trace| {
                sum + &trace.exact_support_queries
            });
            eprintln!(
                "species\t{name}\tprimitives={}\tworkers={}\tqueries={queries}\twall-ns={nanoseconds}",
                species.primitives.len(),
                execution.workers_used,
            );
        }
    }
}
