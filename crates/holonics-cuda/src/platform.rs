//! Minimal platform membrane for exact presentation and raw control.
//!
//! Window systems expose finite integer extents and ordered integer device
//! counts.  This membrane carries those facts without allowing a platform
//! graphics pipeline to own geometry or physics.

use std::collections::VecDeque;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{DisplayFace, DisplayPatch, PresentationAddress};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RawPlatformInput {
    Key {
        physical_code: u32,
        pressed: bool,
        repeat: bool,
    },
    PointerCounts {
        at: PresentationAddress,
        horizontal: i64,
        vertical: i64,
    },
    PointerButton {
        at: PresentationAddress,
        button: u8,
        pressed: bool,
    },
    ScrollCounts {
        horizontal: i64,
        vertical: i64,
    },
    Resize {
        width: u32,
        height: u32,
    },
    RedrawRequested,
    CloseRequested,
}

pub trait PlatformMembrane {
    fn extent(&self) -> (u32, u32);
    fn next_input(&mut self) -> Result<Option<RawPlatformInput>, PlatformError>;
    fn present(&mut self, face: &DisplayFace) -> Result<(), PlatformError>;
    fn present_patch(&mut self, patch: &DisplayPatch) -> Result<(), PlatformError>;
    fn present_patches(&mut self, patches: &[DisplayPatch]) -> Result<(), PlatformError> {
        for patch in patches {
            self.present_patch(patch)?;
        }
        Ok(())
    }
}

/// Deterministic platform foil suitable for the engine and for a future
/// native window adapter.  It retains the last complete terminal carrier and
/// never feeds it back as construction geometry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemoryPlatform {
    width: u32,
    height: u32,
    pending: VecDeque<RawPlatformInput>,
    presented: Option<DisplayFace>,
}

impl MemoryPlatform {
    pub fn new(width: u32, height: u32) -> Result<Self, PlatformError> {
        if width == 0 || height == 0 {
            return Err(PlatformError::EmptyExtent);
        }
        Ok(Self {
            width,
            height,
            pending: VecDeque::new(),
            presented: None,
        })
    }

    pub fn supply(&mut self, input: RawPlatformInput) {
        self.pending.push_back(input);
    }

    pub fn presented(&self) -> Option<&DisplayFace> {
        self.presented.as_ref()
    }
}

impl PlatformMembrane for MemoryPlatform {
    fn extent(&self) -> (u32, u32) {
        (self.width, self.height)
    }

    fn next_input(&mut self) -> Result<Option<RawPlatformInput>, PlatformError> {
        let Some(input) = self.pending.pop_front() else {
            return Ok(None);
        };
        if let RawPlatformInput::Resize { width, height } = input {
            if width > 0 && height > 0 {
                self.width = width;
                self.height = height;
            }
            return Ok(Some(RawPlatformInput::Resize { width, height }));
        }
        Ok(Some(input))
    }

    fn present(&mut self, face: &DisplayFace) -> Result<(), PlatformError> {
        if face.width != self.width || face.height != self.height {
            return Err(PlatformError::ExtentMismatch {
                platform: (self.width, self.height),
                face: (face.width, face.height),
            });
        }
        self.presented = Some(face.clone());
        Ok(())
    }

    fn present_patch(&mut self, patch: &DisplayPatch) -> Result<(), PlatformError> {
        self.present_patches(std::slice::from_ref(patch))
    }

    fn present_patches(&mut self, patches: &[DisplayPatch]) -> Result<(), PlatformError> {
        let Some(presented) = &self.presented else {
            return Err(PlatformError::MissingPresentedFace);
        };
        let mut next = presented.clone();
        for patch in patches {
            apply_patch(&mut next, patch)?;
        }
        self.presented = Some(next);
        Ok(())
    }
}

pub(crate) fn apply_patch(
    target: &mut DisplayFace,
    patch: &DisplayPatch,
) -> Result<(), PlatformError> {
    let right = patch
        .left
        .checked_add(patch.face.width)
        .ok_or(PlatformError::PatchOutsideFace)?;
    let bottom = patch
        .top
        .checked_add(patch.face.height)
        .ok_or(PlatformError::PatchOutsideFace)?;
    if right > target.width || bottom > target.height {
        return Err(PlatformError::PatchOutsideFace);
    }
    let expected = usize::try_from(patch.face.width)
        .ok()
        .and_then(|width| {
            usize::try_from(patch.face.height)
                .ok()
                .and_then(|height| width.checked_mul(height))
        })
        .ok_or(PlatformError::PatchOutsideFace)?;
    if patch.face.pixels.len() != expected {
        return Err(PlatformError::MalformedFace {
            expected,
            actual: patch.face.pixels.len(),
        });
    }
    for row in 0..patch.face.height {
        let target_start = usize::try_from((patch.top + row) * target.width + patch.left)
            .expect("validated display address fits memory addressing");
        let source_start = usize::try_from(row * patch.face.width)
            .expect("validated patch address fits memory addressing");
        let count = usize::try_from(patch.face.width)
            .expect("validated patch width fits memory addressing");
        target.pixels[target_start..target_start + count]
            .copy_from_slice(&patch.face.pixels[source_start..source_start + count]);
    }
    Ok(())
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum PlatformError {
    #[error("a platform presentation extent must be nonzero")]
    EmptyExtent,
    #[error("platform extent {platform:?} differs from returned face {face:?}")]
    ExtentMismatch {
        platform: (u32, u32),
        face: (u32, u32),
    },
    #[error("platform transport refused: {0}")]
    Transport(String),
    #[error("platform extent {width}x{height} cannot be represented by this membrane")]
    UnsupportedExtent { width: u32, height: u32 },
    #[error("display face carries {actual} members for an expected {expected}")]
    MalformedFace { expected: usize, actual: usize },
    #[error("a display patch extends outside the presented face")]
    PatchOutsideFace,
    #[error("a display patch arrived before a complete presentation face")]
    MissingPresentedFace,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Rgb8;

    #[test]
    fn raw_counts_and_complete_faces_cross_without_geometry_ownership() {
        let mut platform = MemoryPlatform::new(2, 1).unwrap();
        platform.supply(RawPlatformInput::PointerCounts {
            at: PresentationAddress { column: 0, row: 0 },
            horizontal: 7,
            vertical: -3,
        });
        assert!(matches!(
            platform.next_input().unwrap(),
            Some(RawPlatformInput::PointerCounts { .. })
        ));
        platform
            .present(&DisplayFace {
                schema: "test".to_owned(),
                width: 2,
                height: 1,
                pixels: vec![
                    Rgb8 {
                        red: 0,
                        green: 0,
                        blue: 0,
                    },
                    Rgb8 {
                        red: 255,
                        green: 255,
                        blue: 255,
                    },
                ],
            })
            .unwrap();
        assert!(platform.presented().is_some());
    }

    #[test]
    fn a_patch_batch_is_validated_before_it_changes_the_retained_face() {
        let mut platform = MemoryPlatform::new(2, 1).unwrap();
        let original = DisplayFace {
            schema: "test".to_owned(),
            width: 2,
            height: 1,
            pixels: vec![
                Rgb8 {
                    red: 0,
                    green: 0,
                    blue: 0,
                },
                Rgb8 {
                    red: 1,
                    green: 1,
                    blue: 1,
                },
            ],
        };
        platform.present(&original).unwrap();
        let patches = [
            DisplayPatch {
                left: 0,
                top: 0,
                face: DisplayFace {
                    schema: "patch".to_owned(),
                    width: 1,
                    height: 1,
                    pixels: vec![Rgb8 {
                        red: 8,
                        green: 8,
                        blue: 8,
                    }],
                },
            },
            DisplayPatch {
                left: 2,
                top: 0,
                face: DisplayFace {
                    schema: "invalid".to_owned(),
                    width: 1,
                    height: 1,
                    pixels: vec![Rgb8 {
                        red: 9,
                        green: 9,
                        blue: 9,
                    }],
                },
            },
        ];
        assert_eq!(
            platform.present_patches(&patches),
            Err(PlatformError::PatchOutsideFace)
        );
        assert_eq!(platform.presented(), Some(&original));
    }
}
