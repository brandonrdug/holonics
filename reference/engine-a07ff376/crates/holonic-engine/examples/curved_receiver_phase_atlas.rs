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
    CausalWorld, EventId, ExactRaster, ExactReceiverPhaseJet, ExactRgb, HomogeneousConic,
    ImageExtent, RayFamily, ReceiverPhaseAtlasEvent, ReceiverPhaseAtlasLaw,
    ReceiverPhaseAtlasStanding, ReceiverPhaseSectionOccurrence,
};
use image::{DynamicImage, Rgb, RgbImage};
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use relational_geometry::{Rat, RatVec3, ReceiverId};

const DEFAULT_INPUT: &str = "/tmp/codex-clipboard-T9jMYB.png";
const DEFAULT_OUTPUT: &str = "target/holonic-engine/curved-receiver-phase-atlas-tiger";

#[derive(Debug)]
struct Arguments {
    input: PathBuf,
    output: PathBuf,
}

fn main() -> Result<(), Box<dyn Error>> {
    let arguments = parse_arguments()?;
    fs::create_dir_all(&arguments.output)?;
    let raster = load_raster(&arguments.input)?;
    let law = ReceiverPhaseAtlasLaw;
    let mut world = CausalWorld::new(law.clone(), law.initial_standing());
    let started = Instant::now();
    let successor = world.receive(&ReceiverPhaseAtlasEvent {
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

    save_raster(&arguments.output.join("00_receiver_testimony.png"), &raster)?;
    let render = render_phase_atlas(&raster, standing)?;
    save_raster(
        &arguments.output.join("01_curved_phase_atlas.png"),
        &render.phase,
    )?;
    save_raster(
        &arguments.output.join("02_support_multiplicity.png"),
        &render.multiplicity,
    )?;
    write_summary(
        &arguments.output.join("atlas_summary.tsv"),
        &arguments.input,
        standing,
        elapsed_milliseconds,
        render.max_multiplicity,
        successor
            .logical_resources
            .as_ref()
            .ok_or("the phase-atlas event did not report logical resources")?,
    )?;
    write_germs(&arguments.output.join("germs.tsv"), standing)?;
    write_connections(&arguments.output.join("connections.tsv"), standing)?;
    write_cycles(&arguments.output.join("cycles.tsv"), standing)?;

    println!(
        "extent\t{}x{}\ngerms\t{}\nconnections\t{}\ncycles\t{}\ncurved_cycles\t{}\n\
         conic_support_pixels\t{}\nmaximum_support_multiplicity\t{}\n\
         construction_milliseconds\t{}\noutput\t{}",
        raster.extent.width,
        raster.extent.height,
        standing.germs.len(),
        standing.connections.len(),
        standing.cycles.len(),
        standing
            .cycles
            .values()
            .filter(|cycle| cycle.curved)
            .count(),
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
                println!("curved_receiver_phase_atlas [--input FILE] [--output DIRECTORY]");
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
        for channel in 0..3 {
            let Some(conic) = &germ.level_sets[channel] else {
                continue;
            };
            for row in minimum_row..=maximum_row {
                for column in minimum_column..=maximum_column {
                    let horizontal = signed_offset(column, center_column)?;
                    let vertical = signed_offset(row, center_row)?;
                    if !crosses_conic(conic, horizontal, vertical) {
                        continue;
                    }
                    let ordinal = row * width + column;
                    let phase = taylor_phase(&germ.jet, horizontal, vertical);
                    for (sum, value) in phase_sums[ordinal].iter_mut().zip(phase) {
                        *sum = sum
                            .checked_add(u64::from(value))
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

fn taylor_phase(jet: &ExactReceiverPhaseJet, horizontal: i64, vertical: i64) -> [u8; 3] {
    let x = rat_i64(horizontal);
    let y = rat_i64(vertical);
    let two = rat_i64(2);
    std::array::from_fn(|channel| {
        let value = &jet.values[channel]
            + &jet.gradients[channel][0] * &x
            + &jet.gradients[channel][1] * &y
            + &jet.hessians[channel][0][0] * &x * &x / &two
            + &jet.hessians[channel][0][1] * &x * &y
            + &jet.hessians[channel][1][1] * &y * &y / &two;
        terminal_channel(&value)
    })
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
    standing: &ReceiverPhaseAtlasStanding,
    elapsed_milliseconds: u128,
    max_multiplicity: u32,
    resources: &holonic_engine::LogicalResourceReceipt,
) -> Result<(), Box<dyn Error>> {
    let mut conic_species = BTreeMap::<String, u64>::new();
    let mut persistence = BTreeMap::<u32, u64>::new();
    for germ in standing.germs.values() {
        *persistence.entry(germ.horizon).or_default() += 1;
        for conic in germ.level_sets.iter().flatten() {
            *conic_species
                .entry(format!("{:?}", conic.classify()))
                .or_default() += 1;
        }
    }
    let mut output = String::from("property\tvalue\n");
    writeln!(output, "schema\t{}", standing.schema)?;
    writeln!(output, "input\t{}", input.display())?;
    writeln!(output, "sections\t{}", standing.sections.len())?;
    writeln!(output, "germs\t{}", standing.germs.len())?;
    writeln!(output, "connections\t{}", standing.connections.len())?;
    writeln!(output, "cycles\t{}", standing.cycles.len())?;
    writeln!(
        output,
        "curved_cycles\t{}",
        standing
            .cycles
            .values()
            .filter(|cycle| cycle.curved)
            .count()
    )?;
    writeln!(output, "maximum_support_multiplicity\t{max_multiplicity}")?;
    writeln!(output, "logical_work\t{}", resources.work)?;
    writeln!(output, "causal_span\t{}", resources.causal_span)?;
    writeln!(
        output,
        "exposed_parallel_width\t{}",
        resources.exposed_parallel_width
    )?;
    writeln!(output, "construction_milliseconds\t{elapsed_milliseconds}")?;
    for (species, count) in conic_species {
        writeln!(output, "conic_species.{species}\t{count}")?;
    }
    for (horizon, count) in persistence {
        writeln!(output, "horizon.{horizon}\t{count}")?;
    }
    fs::write(path, output)?;
    Ok(())
}

fn write_germs(path: &Path, standing: &ReceiverPhaseAtlasStanding) -> Result<(), Box<dyn Error>> {
    let mut output = String::from(
        "germ\tsection\tlineage\tcolumn\trow\tred\tgreen\tblue\tenergy\t\
         radii\thorizon\tdominant\tconic_species\n",
    );
    for germ in standing.germs.values() {
        let radii = germ
            .persistence_radii
            .iter()
            .map(u32::to_string)
            .collect::<Vec<_>>()
            .join(",");
        let species = germ
            .level_sets
            .iter()
            .map(|conic| {
                conic.as_ref().map_or_else(
                    || "None".to_owned(),
                    |conic| format!("{:?}", conic.classify()),
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        writeln!(
            output,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            germ.id.0,
            germ.section.0,
            germ.source_lineage,
            germ.witness.column,
            germ.witness.row,
            germ.jet.values[0],
            germ.jet.values[1],
            germ.jet.values[2],
            germ.exact_energy,
            radii,
            germ.horizon,
            germ.dominant_coordinate,
            species,
        )?;
    }
    fs::write(path, output)?;
    Ok(())
}

fn write_connections(
    path: &Path,
    standing: &ReceiverPhaseAtlasStanding,
) -> Result<(), Box<dyn Error>> {
    let mut output = String::from(
        "connection\tsection\tsource\ttarget\tpredicted_x\tpredicted_y\t\
         target_x\ttarget_y\tc00\tc01\tc10\tc11\n",
    );
    for connection in standing.connections.values() {
        writeln!(
            output,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            connection.id.0,
            connection.section.0,
            connection.source.0,
            connection.target.0,
            connection.predicted_normal[0],
            connection.predicted_normal[1],
            connection.target_normal[0],
            connection.target_normal[1],
            connection.correction[0][0],
            connection.correction[0][1],
            connection.correction[1][0],
            connection.correction[1][1],
        )?;
    }
    fs::write(path, output)?;
    Ok(())
}

fn write_cycles(path: &Path, standing: &ReceiverPhaseAtlasStanding) -> Result<(), Box<dyn Error>> {
    let mut output =
        String::from("cycle\tsection\tleft\tmiddle\tright\th00\th01\th10\th11\tcurved\n");
    for cycle in standing.cycles.values() {
        writeln!(
            output,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            cycle.id.0,
            cycle.section.0,
            cycle.boundary[0].0,
            cycle.boundary[1].0,
            cycle.boundary[2].0,
            cycle.holonomy[0][0],
            cycle.holonomy[0][1],
            cycle.holonomy[1][0],
            cycle.holonomy[1][1],
            cycle.curved,
        )?;
    }
    fs::write(path, output)?;
    Ok(())
}
