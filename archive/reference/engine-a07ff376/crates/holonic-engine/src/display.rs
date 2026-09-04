//! An explicit display membrane for a completed plural presentation quotient.
//!
//! The core crossing geometry and receiver assembly do not own color or
//! occlusion. A world supplies a `PresentationTransducer` which interprets
//! every plural presentation member. This module only packs those returned
//! consequences into a platform carrier.

use serde::{Deserialize, Serialize};

use crate::{PresentationMatrix, PresentationMember};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Rgb8 {
    pub red: u8,
    pub green: u8,
    pub blue: u8,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DisplayFace {
    pub schema: String,
    pub width: u32,
    pub height: u32,
    pub pixels: Vec<Rgb8>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DisplayPatch {
    pub left: u32,
    pub top: u32,
    pub face: DisplayFace,
}

pub trait PresentationTransducer {
    /// Interpret all receiver contributions at one finite address. The
    /// transducer, not the geometric core, owns any decision to select,
    /// combine, or refuse contributions and crossing layers.
    fn transduce(&self, member: &PresentationMember) -> Rgb8;
}

pub fn transduce_display(
    presentation: &PresentationMatrix,
    law: &impl PresentationTransducer,
) -> DisplayFace {
    DisplayFace {
        schema: "holonic-engine.display-face.v1".to_owned(),
        width: presentation.specification.width,
        height: presentation.specification.height,
        pixels: presentation
            .members
            .iter()
            .map(|member| law.transduce(member))
            .collect(),
    }
}

/// Encode one exact discrete display face as binary PPM (P6).
///
/// PPM is only an outer carrier. Decoding it cannot feed approximated geometry
/// back into the causal construction.
pub fn encode_ppm(face: &DisplayFace) -> Vec<u8> {
    let mut encoded = format!("P6\n{} {}\n255\n", face.width, face.height).into_bytes();
    encoded.reserve(face.pixels.len() * 3);
    for pixel in &face.pixels {
        encoded.extend([pixel.red, pixel.green, pixel.blue]);
    }
    encoded
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;
    use relational_geometry::integer;

    use super::*;
    use crate::{
        ExactCell, PresentationAddress, PresentationBoundary, PresentationWork, TerminalMatrixSpec,
    };

    struct EmptyIsBlack;

    impl PresentationTransducer for EmptyIsBlack {
        fn transduce(&self, member: &PresentationMember) -> Rgb8 {
            if member.primitives.is_empty() {
                Rgb8 {
                    red: 0,
                    green: 0,
                    blue: 0,
                }
            } else {
                Rgb8 {
                    red: 255,
                    green: 255,
                    blue: 255,
                }
            }
        }
    }

    #[test]
    fn display_packing_is_an_explicit_outer_transduction() {
        let presentation = PresentationMatrix {
            schema: "test".to_owned(),
            assembly_name: "empty bounded assembly".to_owned(),
            specification: TerminalMatrixSpec {
                width: 1,
                height: 1,
                boundary: PresentationBoundary {
                    horizontal_span: integer(1),
                    vertical_span: integer(1),
                },
            },
            members: vec![PresentationMember {
                address: PresentationAddress { column: 0, row: 0 },
                cell: ExactCell {
                    lower: [integer(-1), integer(-1)],
                    upper: [integer(1), integer(1)],
                },
                primitives: Vec::new(),
                coordinate_fields: Vec::new(),
                quadratic_phases: Vec::new(),
                depth_phases: Vec::new(),
            }],
            work: PresentationWork {
                addresses: BigUint::from(1_u8),
                primitive_cell_classifications: BigUint::from(0_u8),
                coordinate_field_restrictions: BigUint::from(0_u8),
            },
        };
        let display = transduce_display(&presentation, &EmptyIsBlack);
        assert_eq!(encode_ppm(&display), b"P6\n1 1\n255\n\0\0\0".to_vec());
    }
}
