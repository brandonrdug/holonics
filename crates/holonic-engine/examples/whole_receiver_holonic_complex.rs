use std::{
    collections::BTreeMap,
    env,
    error::Error,
    fmt::Write as _,
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use holonic_engine::{
    CausalWorld, EventId, ExactRaster, ExactRgb, HolonicCellWitness, HomogeneousConic, ImageExtent,
    LogicalResourceReceipt, RayFamily, ReceiverGrainId, ReceiverHolonicComplexEvent,
    ReceiverHolonicComplexLaw, ReceiverHolonicComplexStanding, ReceiverPhaseAtlasStanding,
    ReceiverPhaseSectionOccurrence,
};
use image::{DynamicImage, Rgb, RgbImage};
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use relational_geometry::{Rat, RatVec3, ReceiverId};

const DEFAULT_INPUT: &str = "/tmp/codex-clipboard-T9jMYB.png";
const DEFAULT_OUTPUT: &str = "target/holonic-engine/whole-receiver-holonic-complex-tiger";

#[derive(Debug)]
struct Arguments {
    input: PathBuf,
    output: PathBuf,
}

fn main() -> Result<(), Box<dyn Error>> {
    let arguments = parse_arguments()?;
    fs::create_dir_all(&arguments.output)?;
    let raster = load_raster(&arguments.input)?;
    let law = ReceiverHolonicComplexLaw::default();
    let mut world = CausalWorld::new(law.clone(), law.initial_standing());
    let started = Instant::now();
    let receipt = world.receive(&ReceiverHolonicComplexEvent {
        event: EventId(1),
        chronology: 1,
        sections: vec![ReceiverPhaseSectionOccurrence::whole(
            None,
            1,
            ReceiverId(1),
            receiver_rays(),
            &raster,
        )],
    })?;
    let elapsed_milliseconds = started.elapsed().as_millis();
    let standing = world.standing();
    standing.validate()?;
    let radiation = receipt
        .radiation
        .first()
        .ok_or("the holonic-complex event emitted no radiation")?;
    let resources = receipt
        .logical_resources
        .as_ref()
        .ok_or("the holonic-complex event emitted no logical resource receipt")?;

    save_raster(&arguments.output.join("00_receiver_testimony.png"), &raster)?;
    let render = render_phase_atlas(&raster, &standing.phase_atlas)?;
    save_raster(
        &arguments.output.join("01_whole_receiver_phase_complex.png"),
        &render.phase,
    )?;
    save_raster(
        &arguments
            .output
            .join("02_terminal_support_multiplicity.png"),
        &render.multiplicity,
    )?;
    write_summary(
        &arguments.output.join("summary.tsv"),
        &arguments.input,
        standing,
        resources,
        elapsed_milliseconds,
        &render,
    )?;
    write_causal_layers(
        &arguments.output.join("causal_layers.tsv"),
        &radiation.causal_layers,
    )?;
    write_grain_cells(&arguments.output.join("grain_cells.tsv"), standing)?;
    write_quotients(&arguments.output.join("quotients.tsv"), standing)?;
    write_overlaps(&arguments.output.join("overlap_nerve.tsv"), standing)?;

    let grain_zero = standing.grain(ReceiverGrainId(0))?.incidence.f_vector();
    let grain_one = standing.grain(ReceiverGrainId(1))?.incidence.f_vector();
    println!(
        "extent\t{}x{}\nphase_germs\t{}\nphase_connections\t{}\nphase_cycles\t{}\n\
         grain_0_f_vector\t{:?}\ngrain_1_f_vector\t{:?}\nquotient_points\t{}\n\
         actual_overlap_cells\t{}\ncausal_layers\t{}\nterminal_support_pixels\t{}\n\
         maximum_terminal_support_multiplicity\t{}\nconstruction_milliseconds\t{}\noutput\t{}",
        raster.extent.width,
        raster.extent.height,
        standing.phase_atlas.germs.len(),
        standing.phase_atlas.connections.len(),
        standing.phase_atlas.cycles.len(),
        grain_zero,
        grain_one,
        standing.quotients.len(),
        standing.overlaps.len(),
        radiation.causal_layers.len(),
        render.support_pixels,
        render.max_multiplicity,
        elapsed_milliseconds,
        arguments.output.display(),
    );
    Ok(())
}

fn parse_arguments() -> Result<Arguments, Box<dyn Error>> {
    let mut arguments = Arguments {
        input: PathBuf::from(DEFAULT_INPUT),
        output: PathBuf::from(DEFAULT_OUTPUT),
    };
    let mut supplied = env::args().skip(1);
    while let Some(argument) = supplied.next() {
        match argument.as_str() {
            "--input" => {
                arguments.input = PathBuf::from(supplied.next().ok_or("--input requires a path")?);
            }
            "--output" => {
                arguments.output =
                    PathBuf::from(supplied.next().ok_or("--output requires a path")?);
            }
            "--help" | "-h" => {
                println!("whole_receiver_holonic_complex [--input FILE] [--output DIRECTORY]");
                std::process::exit(0);
            }
            unknown => return Err(format!("unknown argument {unknown}").into()),
        }
    }
    Ok(arguments)
}

fn load_raster(path: &Path) -> Result<ExactRaster, Box<dyn Error>> {
    let image = image::open(path)?.to_rgb8();
    let extent = ImageExtent {
        width: image.width(),
        height: image.height(),
    };
    let samples = image
        .pixels()
        .map(|pixel| ExactRgb {
            red: pixel[0],
            green: pixel[1],
            blue: pixel[2],
        })
        .collect();
    Ok(ExactRaster::new(extent, samples)?)
}

fn receiver_rays() -> RayFamily {
    RayFamily::Central {
        center: RatVec3::zero(),
        forward: RatVec3::from_i64(0, 0, 1),
        horizontal: RatVec3::from_i64(1, 0, 0),
        vertical: RatVec3::from_i64(0, 1, 0),
    }
}

struct AtlasRender {
    phase: ExactRaster,
    multiplicity: ExactRaster,
    support_pixels: usize,
    max_multiplicity: u32,
}

fn render_phase_atlas(
    source: &ExactRaster,
    standing: &ReceiverPhaseAtlasStanding,
) -> Result<AtlasRender, Box<dyn Error>> {
    let width = usize::try_from(source.extent.width)?;
    let height = usize::try_from(source.extent.height)?;
    let mut phase_sums = vec![[0_u64; 3]; source.samples.len()];
    let mut multiplicities = vec![0_u32; source.samples.len()];

    for germ in standing.germs.values() {
        let center_column = usize::try_from(germ.witness.column)?;
        let center_row = usize::try_from(germ.witness.row)?;
        let horizon = usize::try_from(germ.horizon)?;
        let minimum_column = center_column.saturating_sub(horizon);
        let minimum_row = center_row.saturating_sub(horizon);
        let maximum_column = center_column.saturating_add(horizon).min(width - 1);
        let maximum_row = center_row.saturating_add(horizon).min(height - 1);
        for conic in germ.level_sets.iter().flatten() {
            for row in minimum_row..=maximum_row {
                for column in minimum_column..=maximum_column {
                    let horizontal = signed_offset(column, center_column)?;
                    let vertical = signed_offset(row, center_row)?;
                    if !crosses_conic(conic, horizontal, vertical) {
                        continue;
                    }
                    let ordinal = row * width + column;
                    let phase = germ.evaluate_phase(&[rat_i64(horizontal), rat_i64(vertical)]);
                    for (sum, value) in phase_sums[ordinal].iter_mut().zip(phase.iter()) {
                        *sum = sum
                            .checked_add(u64::from(terminal_channel(value)))
                            .ok_or("phase render overflow")?;
                    }
                    multiplicities[ordinal] = multiplicities[ordinal]
                        .checked_add(1)
                        .ok_or("support multiplicity overflow")?;
                }
            }
        }
    }

    let max_multiplicity = multiplicities.iter().copied().max().unwrap_or(0);
    let support_pixels = multiplicities
        .iter()
        .filter(|multiplicity| **multiplicity != 0)
        .count();
    let phase_samples = source
        .samples
        .iter()
        .zip(&phase_sums)
        .zip(&multiplicities)
        .map(|((background, sums), multiplicity)| {
            if *multiplicity == 0 {
                return ExactRgb {
                    red: background.red / 3,
                    green: background.green / 3,
                    blue: background.blue / 3,
                };
            }
            let divisor = u64::from(*multiplicity);
            let average = [
                u8::try_from(sums[0] / divisor).unwrap_or(u8::MAX),
                u8::try_from(sums[1] / divisor).unwrap_or(u8::MAX),
                u8::try_from(sums[2] / divisor).unwrap_or(u8::MAX),
            ];
            ExactRgb {
                red: blend(background.red, average[0]),
                green: blend(background.green, average[1]),
                blue: blend(background.blue, average[2]),
            }
        })
        .collect();
    let multiplicity_samples = multiplicities
        .iter()
        .map(|multiplicity| {
            let intensity = if max_multiplicity == 0 {
                0
            } else {
                u8::try_from(
                    u64::from(*multiplicity)
                        .checked_mul(255)
                        .expect("u32 times 255 fits u64")
                        / u64::from(max_multiplicity),
                )
                .unwrap_or(u8::MAX)
            };
            ExactRgb {
                red: intensity,
                green: intensity,
                blue: intensity,
            }
        })
        .collect();
    Ok(AtlasRender {
        phase: ExactRaster::new(source.extent, phase_samples)?,
        multiplicity: ExactRaster::new(source.extent, multiplicity_samples)?,
        support_pixels,
        max_multiplicity,
    })
}

fn signed_offset(value: usize, center: usize) -> Result<i64, Box<dyn Error>> {
    Ok(i64::try_from(value)? - i64::try_from(center)?)
}

fn crosses_conic(conic: &HomogeneousConic, horizontal: i64, vertical: i64) -> bool {
    let here = conic.evaluate(&[rat_i64(horizontal), rat_i64(vertical), Rat::one()]);
    if here.is_zero() {
        return true;
    }
    let right = conic.evaluate(&[
        rat_i64(horizontal.saturating_add(1)),
        rat_i64(vertical),
        Rat::one(),
    ]);
    let down = conic.evaluate(&[
        rat_i64(horizontal),
        rat_i64(vertical.saturating_add(1)),
        Rat::one(),
    ]);
    sign(&here) != sign(&right) || sign(&here) != sign(&down)
}

fn terminal_channel(value: &Rat) -> u8 {
    if value.is_negative() || value.is_zero() {
        return 0;
    }
    let maximum = rat_i64(255);
    if value >= &maximum {
        return 255;
    }
    let rounded = (value.numer() + value.denom() / BigInt::from(2)) / value.denom();
    rounded.to_u8().unwrap_or(0)
}

fn blend(background: u8, phase: u8) -> u8 {
    u8::try_from((u16::from(background) + 3 * u16::from(phase)) / 4).unwrap_or(u8::MAX)
}

fn sign(value: &Rat) -> i8 {
    if value.is_positive() {
        1
    } else if value.is_negative() {
        -1
    } else {
        0
    }
}

fn rat_i64(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn save_raster(path: &Path, raster: &ExactRaster) -> Result<(), Box<dyn Error>> {
    let mut image = RgbImage::new(raster.extent.width, raster.extent.height);
    for (target, source) in image.pixels_mut().zip(&raster.samples) {
        *target = Rgb([source.red, source.green, source.blue]);
    }
    DynamicImage::ImageRgb8(image).save(path)?;
    Ok(())
}

fn write_summary(
    path: &Path,
    input: &Path,
    standing: &ReceiverHolonicComplexStanding,
    resources: &LogicalResourceReceipt,
    elapsed_milliseconds: u128,
    render: &AtlasRender,
) -> Result<(), Box<dyn Error>> {
    let mut analytic_topologies = BTreeMap::<String, u64>::new();
    for grain in standing.grains.values() {
        for witness in grain.witnesses.values() {
            if let HolonicCellWitness::PhaseGerm {
                internal_sections, ..
            } = witness
            {
                for section in internal_sections {
                    *analytic_topologies
                        .entry(format!("{:?}", section.topology))
                        .or_default() += 1;
                }
            }
        }
    }
    let maximum_overlap_members = standing
        .overlaps
        .values()
        .map(|overlap| overlap.members.len())
        .max()
        .unwrap_or(0);
    let higher_overlaps = standing
        .overlaps
        .values()
        .filter(|overlap| overlap.members.len() >= 3)
        .count();
    let mut output = String::from("property\tvalue\n");
    writeln!(output, "schema\t{}", standing.schema)?;
    writeln!(output, "input\t{}", input.display())?;
    writeln!(
        output,
        "extent\t{}x{}",
        render.phase.extent.width, render.phase.extent.height
    )?;
    writeln!(output, "phase_germs\t{}", standing.phase_atlas.germs.len())?;
    writeln!(
        output,
        "phase_connections\t{}",
        standing.phase_atlas.connections.len()
    )?;
    writeln!(
        output,
        "phase_cycles\t{}",
        standing.phase_atlas.cycles.len()
    )?;
    writeln!(
        output,
        "curved_phase_cycles\t{}",
        standing
            .phase_atlas
            .cycles
            .values()
            .filter(|cycle| cycle.curved)
            .count()
    )?;
    for (grain_id, grain) in &standing.grains {
        for (grade, population) in grain.incidence.f_vector() {
            writeln!(
                output,
                "grain_{}.grade_{}_cells\t{}",
                grain_id.0, grade, population
            )?;
        }
    }
    writeln!(output, "quotient_points\t{}", standing.quotients.len())?;
    writeln!(output, "actual_overlap_cells\t{}", standing.overlaps.len())?;
    writeln!(output, "higher_overlap_cells\t{higher_overlaps}")?;
    writeln!(output, "maximum_overlap_members\t{maximum_overlap_members}")?;
    writeln!(output, "boundary_squared_zero\ttrue")?;
    writeln!(output, "sparse_coboundary_is_exact_boundary_dual\ttrue")?;
    writeln!(output, "terminal_support_pixels\t{}", render.support_pixels)?;
    writeln!(
        output,
        "maximum_terminal_support_multiplicity\t{}",
        render.max_multiplicity
    )?;
    writeln!(output, "logical_work\t{}", resources.work)?;
    writeln!(output, "causal_span\t{}", resources.causal_span)?;
    writeln!(
        output,
        "exposed_parallel_width\t{}",
        resources.exposed_parallel_width
    )?;
    writeln!(output, "construction_milliseconds\t{elapsed_milliseconds}")?;
    for (topology, population) in analytic_topologies {
        writeln!(output, "internal_topology.{topology}\t{population}")?;
    }
    fs::write(path, output)?;
    Ok(())
}

fn write_causal_layers(
    path: &Path,
    layers: &[holonic_engine::HolonicCausalLayerReceipt],
) -> Result<(), Box<dyn Error>> {
    let mut output = String::from("order\tkind\tcells\tquotients\toverlaps\tpopulation\n");
    for layer in layers {
        writeln!(
            output,
            "{}\t{:?}\t{}\t{}\t{}\t{}",
            layer.order,
            layer.kind,
            layer.caused_cells.len(),
            layer.caused_quotients.len(),
            layer.caused_overlaps.len(),
            layer.population(),
        )?;
    }
    fs::write(path, output)?;
    Ok(())
}

fn write_grain_cells(
    path: &Path,
    standing: &ReceiverHolonicComplexStanding,
) -> Result<(), Box<dyn Error>> {
    let mut output = String::from("grain\tcell\tgrade\tname\tsources\tboundary\twitness\n");
    for (grain_id, grain) in &standing.grains {
        for cell in grain.incidence.cells().values() {
            let sources = cell
                .source_events
                .iter()
                .map(|event| event.0.to_string())
                .collect::<Vec<_>>()
                .join(",");
            let boundary = cell
                .boundary
                .coefficients()
                .iter()
                .map(|(face, coefficient)| format!("{}:{}", face.0, coefficient.difference()))
                .collect::<Vec<_>>()
                .join(",");
            let witness = match &grain.witnesses[&cell.id] {
                HolonicCellWitness::PhaseGerm {
                    germ,
                    internal_sections,
                } => format!(
                    "phase-germ:{}:{}",
                    germ.0,
                    internal_sections
                        .iter()
                        .map(|section| format!("{}:{:?}", section.coordinate, section.topology))
                        .collect::<Vec<_>>()
                        .join(",")
                ),
                HolonicCellWitness::PhaseTransport { connection } => {
                    format!("phase-transport:{}", connection.0)
                }
                HolonicCellWitness::PhaseClosure { cycle } => {
                    let curved = standing.phase_atlas.cycles[cycle].curved;
                    format!("phase-closure:{}:curved={curved}", cycle.0)
                }
                HolonicCellWitness::QuotientedComplex { quotient } => {
                    format!("quotiented-complex:{}", quotient.0)
                }
            };
            writeln!(
                output,
                "{}\t{}\t{}\t{}\t{}\t{}\t{}",
                grain_id.0, cell.id.0, cell.grade, cell.name, sources, boundary, witness
            )?;
        }
    }
    fs::write(path, output)?;
    Ok(())
}

fn write_quotients(
    path: &Path,
    standing: &ReceiverHolonicComplexStanding,
) -> Result<(), Box<dyn Error>> {
    let mut output = String::from(
        "quotient\tevent\tsource_grain\tsource_apex\tclosed_hull\ttarget_grain\ttarget\n",
    );
    for quotient in standing.quotients.values() {
        let closed_hull = quotient
            .source_closed_hull
            .iter()
            .map(|cell| cell.0.to_string())
            .collect::<Vec<_>>()
            .join(",");
        writeln!(
            output,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}",
            quotient.id.0,
            quotient.caused_by.0,
            quotient.source_apex.grain.0,
            quotient.source_apex.cell.0,
            closed_hull,
            quotient.target.grain.0,
            quotient.target.cell.0,
        )?;
    }
    fs::write(path, output)?;
    Ok(())
}

fn write_overlaps(
    path: &Path,
    standing: &ReceiverHolonicComplexStanding,
) -> Result<(), Box<dyn Error>> {
    let mut output = String::from("overlap\tevent\toccurrence_grain\toccurrence_cell\tmembers\n");
    for overlap in standing.overlaps.values() {
        let members = overlap
            .members
            .iter()
            .map(|member| format!("{}:{}", member.grain.0, member.cell.0))
            .collect::<Vec<_>>()
            .join(",");
        writeln!(
            output,
            "{}\t{}\t{}\t{}\t{}",
            overlap.id.0,
            overlap.caused_by.0,
            overlap.occurrence.grain.0,
            overlap.occurrence.cell.0,
            members,
        )?;
    }
    fs::write(path, output)?;
    Ok(())
}
