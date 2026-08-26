//! The emitted native geometry crosses a later raw optical boundary before cultivation.

use std::path::Path;

use holonic_engine::{
    cuda_refine::CudaRefineExecutor,
    image::{ExactRaster, ExactRgb, ImageExtent},
};
use image::{ImageReader, Rgb, RgbImage};
use life::{
    mathematical_particle::NativeMathematicalConsequence,
    mathematical_source::{recover_optical_passage, OpticalPassage},
};
use serde::Serialize;

use super::artifact;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EmittedGeometryReceipt {
    pub schema: &'static str,
    pub native_consequence_occurrence: String,
    pub raw_optical_occurrence: String,
    pub png_sha256: String,
    pub primitive_population: u64,
    pub every_primitive_is_derived_from_native_geometry: bool,
    pub text_or_checker_face_present: bool,
}

pub fn emit_geometry(
    consequence: &NativeMathematicalConsequence,
    path: &Path,
) -> Result<EmittedGeometryReceipt, String> {
    let mut raster = RgbImage::from_pixel(384, 192, Rgb([255, 255, 255]));
    let mut primitive_population = 0_u64;
    for (family, cell) in consequence.complex.geometry_cells.iter().enumerate() {
        let row = 36_u32 + family as u32 * 82;
        for vertex in &cell.vertices {
            let x = 34 + vertex.coordinate * 22;
            let entered_y = offset(row, vertex.entered);
            let returned_y = offset(row, vertex.returned);
            draw_grain(&mut raster, x, entered_y, Rgb([16, 42, 96]));
            // A two-pixel open boundary keeps the occurrences distinct while placing their
            // doubled centres inside the material-founded contact aperture.
            draw_grain(&mut raster, x + 7, returned_y, Rgb([112, 20, 52]));
            primitive_population += 2;
        }
        for (coordinate, incidence) in cell.constraint_incidence.iter().enumerate() {
            if *incidence != 0 {
                let x = 188 + coordinate as u32 * 20;
                let y = row + if *incidence < 0 { 8 } else { 0 };
                draw_grain(&mut raster, x, y, Rgb([24, 104, 48]));
                primitive_population += 1;
            }
        }
        for (coordinate, incidence) in cell.transport_incidence.iter().enumerate() {
            if *incidence != 0 {
                let x = 284 + coordinate as u32 * 18;
                let y = row + 20 + if *incidence < 0 { 7 } else { 0 };
                draw_grain(&mut raster, x, y, Rgb([116, 70, 12]));
                primitive_population += 1;
            }
        }
    }
    raster.save(path).map_err(|error| error.to_string())?;
    let bytes = artifact::read(path)?;
    let png_sha256 = artifact::digest(&bytes);
    Ok(EmittedGeometryReceipt {
        schema: "holonics.n3.emitted-native-geometry.v1",
        native_consequence_occurrence: consequence.occurrence.clone(),
        raw_optical_occurrence: format!("n3/world/raw-optical/{png_sha256}"),
        png_sha256,
        primitive_population,
        every_primitive_is_derived_from_native_geometry: true,
        text_or_checker_face_present: false,
    })
}

pub fn recover(input: &Path, output: &Path) -> Result<(), String> {
    let encoded = artifact::read(input)?;
    let visible = ImageReader::new(std::io::Cursor::new(&encoded))
        .with_guessed_format()
        .map_err(|error| error.to_string())?
        .decode()
        .map_err(|error| error.to_string())?
        .to_rgb8();
    let exact = ExactRaster::new(
        ImageExtent {
            width: visible.width(),
            height: visible.height(),
        },
        visible
            .pixels()
            .map(|pixel| ExactRgb {
                red: pixel[0],
                green: pixel[1],
                blue: pixel[2],
            })
            .collect(),
    )
    .map_err(|error| error.to_string())?;
    let background = exact.sample(0, 0).ok_or("the optical boundary is empty")?;
    let source_sha256 = artifact::digest(&encoded);
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let passage = recover_optical_passage(
        &mut card,
        format!("n3/world/raw-optical/{source_sha256}"),
        "content-addressed-emitted-native-geometry",
        &encoded,
        &exact,
        background,
    )
    .map_err(|error| error.to_string())?;
    if passage.components.len() < 6
        || passage.relations.is_empty()
        || passage.device.launches != 1
        || passage.device.synchronizations != 1
        || passage.device.cpu_semantic_fallback
    {
        return Err(
            "the emitted geometry did not return a resident optical consequence".to_owned(),
        );
    }
    artifact::write_json(output, &passage)?;
    Ok(())
}

pub fn read_passage(path: &Path) -> Result<OpticalPassage, String> {
    serde_json::from_slice(&artifact::read(path)?).map_err(|error| error.to_string())
}

fn offset(base: u32, value: i64) -> u32 {
    let magnitude = value.unsigned_abs().min(9) as u32;
    if value < 0 {
        base + magnitude
    } else {
        base.saturating_sub(magnitude)
    }
}

fn draw_grain(image: &mut RgbImage, left: u32, top: u32, color: Rgb<u8>) {
    for y in top..top + 8 {
        for x in left..left + 5 {
            if x < image.width() && y < image.height() {
                image.put_pixel(x, y, color);
            }
        }
    }
}
