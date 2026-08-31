//! Render a small exact 2D/3D surface scene through cell coverage, not point sampling.
//!
//! The JSON sidecar is the primary artifact. The PNG/PPM are downstream display gauges over the
//! exact `ExactSurfacePresentation`; open occlusion cells are colored as open rather than assigned
//! an invented frontmost surface.

use std::error::Error;
use std::fs;
use std::num::NonZeroUsize;
use std::path::PathBuf;
use std::time::Instant;

use holonic_engine::{
    CpuExecutor, ExactRaster, ExactRgb, ExactSurfacePresentation, ImageExtent, OcclusionFace,
    PluralReceiverAssembly, PresentationBoundary, RayFamily, ReceiverFaceExtent, ReceiverFaceSpec,
    ReceiverPrimitiveId, ReceiverStandingRelation, SurfaceCoverage, SurfaceMemberId,
    assemble_support_presentation_with_cpu, exact_surface_presentation_with_executor, receive_face,
};
use image::{Rgb, RgbImage};
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use relational_geometry::{
    ConicSpecies, Construction, FrameId, Geometry, ProjectionLaw, ProjectiveConic, RatVec3,
    Receiver, ReceiverId, integer,
};

const DEFAULT_OUTPUT: &str = "target/holonic-engine/exact-perspective-surface";
const DEFAULT_WIDTH: u32 = 640;
const DEFAULT_HEIGHT: u32 = 480;

fn parse_arguments() -> Result<(PathBuf, u32, u32), Box<dyn Error>> {
    let mut output = PathBuf::from(DEFAULT_OUTPUT);
    let mut width = DEFAULT_WIDTH;
    let mut height = DEFAULT_HEIGHT;
    let mut arguments = std::env::args().skip(1);
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--output" => output = PathBuf::from(arguments.next().ok_or("--output needs a path")?),
            "--width" => width = arguments.next().ok_or("--width needs a value")?.parse()?,
            "--height" => height = arguments.next().ok_or("--height needs a value")?.parse()?,
            "--help" | "-h" => {
                println!("exact_perspective_surface [--output DIR] [--width N] [--height N]");
                std::process::exit(0);
            }
            unknown => return Err(format!("unknown argument {unknown}").into()),
        }
    }
    if width == 0 || height == 0 {
        return Err("terminal receiver extent must be positive".into());
    }
    Ok((output, width, height))
}

fn source_scene() -> Result<(Construction, FrameId), Box<dyn Error>> {
    let (mut construction, frame) = Construction::new("exact perspective source");
    construction.add_entity(
        "near triangle",
        frame,
        Geometry::Triangle {
            vertices: [
                RatVec3::from_i64(-2, -2, 3),
                RatVec3::from_i64(2, -2, 3),
                RatVec3::from_i64(0, 2, 3),
            ],
        },
    )?;
    construction.add_entity(
        "far triangle",
        frame,
        Geometry::Triangle {
            vertices: [
                RatVec3::from_i64(-4, -4, 5),
                RatVec3::from_i64(4, -4, 5),
                RatVec3::from_i64(0, 4, 5),
            ],
        },
    )?;
    construction.add_entity(
        "declared graph thread",
        frame,
        Geometry::Thread {
            vertices: vec![RatVec3::from_i64(-3, 0, 4), RatVec3::from_i64(3, 0, 4)],
            closed: false,
        },
    )?;
    construction.add_entity(
        "implicit conic",
        frame,
        Geometry::Conic(ProjectiveConic {
            center: RatVec3::from_i64(0, 0, 4),
            axis_u: RatVec3::from_i64(2, 0, 0),
            axis_v: RatVec3::from_i64(0, 2, 0),
            species: ConicSpecies::Circle,
        }),
    )?;
    Ok((construction, frame))
}

fn receiver_spec(frame: FrameId) -> ReceiverFaceSpec {
    ReceiverFaceSpec {
        receiver: Receiver::new(
            ReceiverId(1),
            "central exact perspective",
            frame,
            ProjectionLaw::PerspectiveRay {
                focal_distance: integer(2),
            },
        ),
        extent: ReceiverFaceExtent {
            horizontal_span: integer(4),
            vertical_span: integer(4),
        },
        rays: RayFamily::Central {
            center: RatVec3::zero(),
            forward: RatVec3::from_i64(0, 0, 1),
            horizontal: RatVec3::from_i64(1, 0, 0),
            vertical: RatVec3::from_i64(0, 1, 0),
        },
        acceptance: None,
    }
}

fn terminal(width: u32, height: u32) -> holonic_engine::TerminalMatrixSpec {
    holonic_engine::TerminalMatrixSpec {
        width,
        height,
        boundary: PresentationBoundary {
            horizontal_span: integer(4),
            vertical_span: integer(4),
        },
    }
}

fn member_color(member: &SurfaceMemberId) -> [u8; 3] {
    match member.key.primitive {
        ReceiverPrimitiveId::Entity(entity) => match entity.0 {
            1 => [30, 170, 255],
            2 => [145, 70, 220],
            3 => [245, 120, 30],
            _ => [50, 220, 130],
        },
        ReceiverPrimitiveId::NativeConic(_) => [50, 220, 130],
    }
}

fn coverage_intensity(coverage: &SurfaceCoverage) -> u8 {
    match coverage {
        SurfaceCoverage::AreaFraction(value) => {
            let scaled: BigInt = value.numer() * BigInt::from(220_u8) / value.denom();
            20_u8.saturating_add(scaled.to_u8().unwrap_or(220))
        }
        SurfaceCoverage::SourceParameterInterval { .. } => 220,
        SurfaceCoverage::SupportOnly => 140,
    }
}

fn add_color(target: &mut [u8; 3], color: [u8; 3], intensity: u8) {
    for channel in 0..3 {
        target[channel] = target[channel].saturating_add(
            u8::try_from(u16::from(color[channel]) * u16::from(intensity) / 255)
                .expect("scaled color fits in one channel"),
        );
    }
}

fn display_samples(surface: &ExactSurfacePresentation) -> Result<Vec<ExactRgb>, Box<dyn Error>> {
    let extent = ImageExtent {
        width: surface.specification.width,
        height: surface.specification.height,
    };
    let mut samples = vec![
        ExactRgb {
            red: 4,
            green: 8,
            blue: 14,
        };
        extent.sample_count()?
    ];
    for cell in surface.cells.values() {
        let ordinal = usize::try_from(
            u64::from(cell.address.row) * u64::from(extent.width) + u64::from(cell.address.column),
        )?;
        let mut sample = [4_u8, 8_u8, 14_u8];
        match &cell.occlusion {
            OcclusionFace::Empty => {}
            OcclusionFace::Ordered { front_to_back } => {
                if let Some(member) = front_to_back.first() {
                    if let Some(contribution) = cell
                        .contributions
                        .iter()
                        .find(|contribution| contribution.member == *member)
                    {
                        add_color(
                            &mut sample,
                            member_color(member),
                            coverage_intensity(&contribution.coverage),
                        );
                    }
                }
            }
            OcclusionFace::Open { .. } => {
                // Amber is an exterior display gauge for an unresolved
                // receiver face; it does not select a source member.
                sample = [170, 105, 20];
                for contribution in &cell.contributions {
                    add_color(
                        &mut sample,
                        member_color(&contribution.member),
                        coverage_intensity(&contribution.coverage) / 4,
                    );
                }
            }
        }
        samples[ordinal] = ExactRgb {
            red: sample[0],
            green: sample[1],
            blue: sample[2],
        };
    }
    Ok(samples)
}

fn write_png(path: &std::path::Path, raster: &ExactRaster) -> Result<(), Box<dyn Error>> {
    let mut image = RgbImage::new(raster.extent.width, raster.extent.height);
    for row in 0..raster.extent.height {
        for column in 0..raster.extent.width {
            let sample = raster.sample(column, row).expect("raster sample exists");
            image.put_pixel(column, row, Rgb(sample.channels()));
        }
    }
    image.save(path)?;
    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let total_started = Instant::now();
    let (output, width, height) = parse_arguments()?;
    fs::create_dir_all(&output)?;

    let source_started = Instant::now();
    let (construction, frame) = source_scene()?;
    eprintln!(
        "profile stage=source_scene elapsed_ms={}",
        source_started.elapsed().as_millis()
    );

    let face_started = Instant::now();
    let specification = receiver_spec(frame);
    let face = receive_face(&construction, &specification)?;
    eprintln!(
        "profile stage=continuous_receiver_face elapsed_ms={}",
        face_started.elapsed().as_millis()
    );

    let assembly_started = Instant::now();
    let assembly = PluralReceiverAssembly::new(
        "exact perspective prototype",
        vec![face],
        vec![ReceiverStandingRelation::identity(
            ReceiverId(1),
            holonic_engine::EventId(1),
        )],
    )?;
    let workers = std::thread::available_parallelism()
        .unwrap_or_else(|_| NonZeroUsize::new(1).expect("one is nonzero"));
    let receiver_executor = CpuExecutor::multicore(workers);
    let (continuous, support_execution) =
        assemble_support_presentation_with_cpu(&assembly, &receiver_executor)?;
    eprintln!(
        "profile stage=support_presentation mode={} tasks={} worker_limit={} workers_used={} batches={} joins={} elapsed_ms={}",
        support_execution.mode,
        support_execution.tasks,
        support_execution.worker_limit,
        support_execution.workers_used,
        support_execution.batches,
        support_execution.joins,
        assembly_started.elapsed().as_millis()
    );

    let surface_started = Instant::now();
    let (surface, execution) = exact_surface_presentation_with_executor(
        &continuous,
        &terminal(width, height),
        &receiver_executor,
    )?;
    eprintln!(
        "profile stage=exact_surface mode={} tasks={} worker_limit={} workers_used={} batches={} joins={} elapsed_ms={}",
        execution.mode,
        execution.tasks,
        execution.worker_limit,
        execution.workers_used,
        execution.batches,
        execution.joins,
        surface_started.elapsed().as_millis()
    );

    let raster_started = Instant::now();
    let samples = display_samples(&surface)?;
    let raster = ExactRaster::new(ImageExtent { width, height }, samples)?;
    eprintln!(
        "profile stage=display_raster elapsed_ms={}",
        raster_started.elapsed().as_millis()
    );

    let json_build_started = Instant::now();
    let occupied_cells = surface
        .cells
        .values()
        .filter(|cell| !cell.contributions.is_empty())
        .map(|cell| {
            serde_json::json!({
                // The exact cell bounds are reconstructed from this address
                // and the recorded TerminalMatrixSpec.
                "address": &cell.address,
                "contributions": &cell.contributions,
                "occlusion": &cell.occlusion,
            })
        })
        .collect::<Vec<_>>();
    let json_surface = serde_json::json!({
        "schema": surface.schema,
        "specification": surface.specification,
        "candidate_cells": surface.candidate_cells,
        "primitive_evaluations": surface.primitive_evaluations,
        "occupied_cells": surface.occupied_cells,
        "open_occlusion_cells": surface.open_occlusion_cells,
        "support_execution": support_execution,
        "execution": execution,
        "cells": &occupied_cells,
        "empty_cells_omitted": true,
    });
    eprintln!(
        "profile stage=json_value_build elapsed_ms={}",
        json_build_started.elapsed().as_millis()
    );

    let json_encode_started = Instant::now();
    let json_bytes = serde_json::to_vec_pretty(&json_surface)?;
    eprintln!(
        "profile stage=json_encode bytes={} elapsed_ms={}",
        json_bytes.len(),
        json_encode_started.elapsed().as_millis()
    );

    let json_write_started = Instant::now();
    fs::write(output.join("surface.json"), json_bytes)?;
    eprintln!(
        "profile stage=json_write elapsed_ms={}",
        json_write_started.elapsed().as_millis()
    );

    let ppm_write_started = Instant::now();
    fs::write(output.join("surface.ppm"), raster.ppm_bytes())?;
    eprintln!(
        "profile stage=ppm_write elapsed_ms={}",
        ppm_write_started.elapsed().as_millis()
    );

    let png_write_started = Instant::now();
    write_png(&output.join("surface.png"), &raster)?;
    eprintln!(
        "profile stage=png_write elapsed_ms={}",
        png_write_started.elapsed().as_millis()
    );

    let contribution_count: usize = surface
        .cells
        .values()
        .map(|cell| cell.contributions.len())
        .sum();
    println!(
        "exact_surface schema={} extent={}x{} candidate_cells={} primitive_evaluations={} occupied_cells={} sparse_cells={} contributions={} open_occlusion_cells={} total_ms={} output={}",
        surface.schema,
        width,
        height,
        surface.candidate_cells,
        surface.primitive_evaluations,
        surface.occupied_cells,
        occupied_cells.len(),
        contribution_count,
        surface.open_occlusion_cells,
        total_started.elapsed().as_millis(),
        output.display(),
    );
    Ok(())
}
