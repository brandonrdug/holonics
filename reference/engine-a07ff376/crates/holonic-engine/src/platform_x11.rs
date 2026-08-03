//! Direct X11 platform membrane for the exact CPU presentation.
//!
//! X11 is used only as an operating-system transport. It receives a completed
//! [`DisplayFace`] and returns integer device events. It never owns receiver
//! geometry, crossing formation, physical law, or chronology.

use x11rb::connection::Connection;
use x11rb::image::Image;
use x11rb::protocol::Event;
use x11rb::protocol::xproto::{
    Atom, AtomEnum, ConnectionExt, CreateGCAux, CreateWindowAux, EventMask, Gcontext, PropMode,
    VisualClass, Window, WindowClass,
};
use x11rb::rust_connection::RustConnection;
use x11rb::wrapper::ConnectionExt as _;

use crate::{
    DisplayFace, DisplayPatch, PlatformError, PlatformMembrane, PresentationAddress,
    RawPlatformInput, Rgb8,
};

pub struct X11Platform {
    connection: RustConnection,
    window: Window,
    graphics: Gcontext,
    width: u32,
    height: u32,
    depth: u8,
    red_mask: u32,
    green_mask: u32,
    blue_mask: u32,
    wm_delete_window: Atom,
    pointer: Option<(i16, i16)>,
    presented: Option<DisplayFace>,
}

impl X11Platform {
    pub fn new(width: u32, height: u32, title: &str) -> Result<Self, PlatformError> {
        let width16 =
            u16::try_from(width).map_err(|_| PlatformError::UnsupportedExtent { width, height })?;
        let height16 = u16::try_from(height)
            .map_err(|_| PlatformError::UnsupportedExtent { width, height })?;
        if width16 == 0 || height16 == 0 {
            return Err(PlatformError::EmptyExtent);
        }
        let (connection, screen_index) =
            x11rb::connect(None).map_err(|error| transport(error.to_string()))?;
        let screen = &connection.setup().roots[screen_index];
        let visual = screen
            .allowed_depths
            .iter()
            .flat_map(|depth| depth.visuals.iter())
            .find(|visual| visual.visual_id == screen.root_visual)
            .ok_or_else(|| transport("the X11 root visual has no declared description"))?;
        if !matches!(
            visual.class,
            VisualClass::TRUE_COLOR | VisualClass::DIRECT_COLOR
        ) {
            return Err(transport(
                "the X11 root visual does not expose direct color masks",
            ));
        }
        let window = connection
            .generate_id()
            .map_err(|error| transport(error.to_string()))?;
        let graphics = connection
            .generate_id()
            .map_err(|error| transport(error.to_string()))?;
        connection
            .create_gc(
                graphics,
                screen.root,
                &CreateGCAux::new().graphics_exposures(0),
            )
            .map_err(|error| transport(error.to_string()))?;
        connection
            .create_window(
                screen.root_depth,
                window,
                screen.root,
                0,
                0,
                width16,
                height16,
                0,
                WindowClass::INPUT_OUTPUT,
                screen.root_visual,
                &CreateWindowAux::new()
                    .background_pixel(screen.black_pixel)
                    .event_mask(
                        EventMask::EXPOSURE
                            | EventMask::KEY_PRESS
                            | EventMask::KEY_RELEASE
                            | EventMask::BUTTON_PRESS
                            | EventMask::BUTTON_RELEASE
                            | EventMask::POINTER_MOTION
                            | EventMask::STRUCTURE_NOTIFY,
                    ),
            )
            .map_err(|error| transport(error.to_string()))?;
        connection
            .change_property8(
                PropMode::REPLACE,
                window,
                AtomEnum::WM_NAME,
                AtomEnum::STRING,
                title.as_bytes(),
            )
            .map_err(|error| transport(error.to_string()))?;
        let wm_protocols = connection
            .intern_atom(false, b"WM_PROTOCOLS")
            .map_err(|error| transport(error.to_string()))?
            .reply()
            .map_err(|error| transport(error.to_string()))?
            .atom;
        let wm_delete_window = connection
            .intern_atom(false, b"WM_DELETE_WINDOW")
            .map_err(|error| transport(error.to_string()))?
            .reply()
            .map_err(|error| transport(error.to_string()))?
            .atom;
        connection
            .change_property32(
                PropMode::REPLACE,
                window,
                wm_protocols,
                AtomEnum::ATOM,
                &[wm_delete_window],
            )
            .map_err(|error| transport(error.to_string()))?;
        connection
            .map_window(window)
            .map_err(|error| transport(error.to_string()))?;
        connection
            .flush()
            .map_err(|error| transport(error.to_string()))?;
        let depth = screen.root_depth;
        let red_mask = visual.red_mask;
        let green_mask = visual.green_mask;
        let blue_mask = visual.blue_mask;
        Ok(Self {
            connection,
            window,
            graphics,
            width,
            height,
            depth,
            red_mask,
            green_mask,
            blue_mask,
            wm_delete_window,
            pointer: None,
            presented: None,
        })
    }

    pub fn window(&self) -> Window {
        self.window
    }

    fn address(&self, x: i16, y: i16) -> PresentationAddress {
        let column = u32::try_from(x.max(0))
            .unwrap_or(0)
            .min(self.width.saturating_sub(1));
        let row = u32::try_from(y.max(0))
            .unwrap_or(0)
            .min(self.height.saturating_sub(1));
        PresentationAddress { column, row }
    }

    fn blit(&self, face: &DisplayFace, left: u32, top: u32) -> Result<(), PlatformError> {
        let width = u16::try_from(face.width).map_err(|_| PlatformError::UnsupportedExtent {
            width: face.width,
            height: face.height,
        })?;
        let height = u16::try_from(face.height).map_err(|_| PlatformError::UnsupportedExtent {
            width: face.width,
            height: face.height,
        })?;
        let expected = usize::try_from(face.width)
            .ok()
            .and_then(|width| {
                usize::try_from(face.height)
                    .ok()
                    .and_then(|height| width.checked_mul(height))
            })
            .ok_or(PlatformError::MalformedFace {
                expected: usize::MAX,
                actual: face.pixels.len(),
            })?;
        if face.pixels.len() != expected {
            return Err(PlatformError::MalformedFace {
                expected,
                actual: face.pixels.len(),
            });
        }
        let mut image = Image::allocate_native(width, height, self.depth, self.connection.setup())
            .map_err(|error| transport(error.to_string()))?;
        for (ordinal, color) in face.pixels.iter().enumerate() {
            let x = u16::try_from(ordinal % usize::from(width))
                .expect("an image column is bounded by its u16 width");
            let y = u16::try_from(ordinal / usize::from(width))
                .expect("an image row is bounded by its u16 height");
            image.put_pixel(x, y, self.pack(*color));
        }
        image
            .put(
                &self.connection,
                self.window,
                self.graphics,
                i16::try_from(left).map_err(|_| PlatformError::PatchOutsideFace)?,
                i16::try_from(top).map_err(|_| PlatformError::PatchOutsideFace)?,
            )
            .map_err(|error| transport(error.to_string()))?;
        Ok(())
    }

    fn pack(&self, color: Rgb8) -> u32 {
        pack_component(color.red, self.red_mask)
            | pack_component(color.green, self.green_mask)
            | pack_component(color.blue, self.blue_mask)
    }
}

impl PlatformMembrane for X11Platform {
    fn extent(&self) -> (u32, u32) {
        (self.width, self.height)
    }

    fn next_input(&mut self) -> Result<Option<RawPlatformInput>, PlatformError> {
        loop {
            let Some(event) = self
                .connection
                .poll_for_event()
                .map_err(|error| transport(error.to_string()))?
            else {
                return Ok(None);
            };
            match event {
                Event::KeyPress(event) => {
                    return Ok(Some(RawPlatformInput::Key {
                        physical_code: u32::from(event.detail),
                        pressed: true,
                        repeat: false,
                    }));
                }
                Event::KeyRelease(event) => {
                    return Ok(Some(RawPlatformInput::Key {
                        physical_code: u32::from(event.detail),
                        pressed: false,
                        repeat: false,
                    }));
                }
                Event::MotionNotify(event) => {
                    let previous = self.pointer.replace((event.event_x, event.event_y));
                    let Some((prior_x, prior_y)) = previous else {
                        continue;
                    };
                    let horizontal = i64::from(event.event_x) - i64::from(prior_x);
                    let vertical = i64::from(event.event_y) - i64::from(prior_y);
                    if horizontal == 0 && vertical == 0 {
                        continue;
                    }
                    return Ok(Some(RawPlatformInput::PointerCounts {
                        at: self.address(event.event_x, event.event_y),
                        horizontal,
                        vertical,
                    }));
                }
                Event::ButtonPress(event) if matches!(event.detail, 4..=7) => {
                    let (horizontal, vertical) = match event.detail {
                        4 => (0, 1),
                        5 => (0, -1),
                        6 => (-1, 0),
                        7 => (1, 0),
                        _ => unreachable!(),
                    };
                    return Ok(Some(RawPlatformInput::ScrollCounts {
                        horizontal,
                        vertical,
                    }));
                }
                Event::ButtonPress(event) => {
                    return Ok(Some(RawPlatformInput::PointerButton {
                        at: self.address(event.event_x, event.event_y),
                        button: event.detail,
                        pressed: true,
                    }));
                }
                Event::ButtonRelease(event) if !matches!(event.detail, 4..=7) => {
                    return Ok(Some(RawPlatformInput::PointerButton {
                        at: self.address(event.event_x, event.event_y),
                        button: event.detail,
                        pressed: false,
                    }));
                }
                Event::ConfigureNotify(event) => {
                    let width = u32::from(event.width);
                    let height = u32::from(event.height);
                    if width == 0 || height == 0 || (width, height) == (self.width, self.height) {
                        continue;
                    }
                    self.width = width;
                    self.height = height;
                    return Ok(Some(RawPlatformInput::Resize { width, height }));
                }
                Event::Expose(_) => return Ok(Some(RawPlatformInput::RedrawRequested)),
                Event::ClientMessage(event)
                    if event.format == 32
                        && event.window == self.window
                        && event.data.as_data32()[0] == self.wm_delete_window =>
                {
                    return Ok(Some(RawPlatformInput::CloseRequested));
                }
                Event::DestroyNotify(_) => {
                    return Ok(Some(RawPlatformInput::CloseRequested));
                }
                _ => {}
            }
        }
    }

    fn present(&mut self, face: &DisplayFace) -> Result<(), PlatformError> {
        if (face.width, face.height) != (self.width, self.height) {
            return Err(PlatformError::ExtentMismatch {
                platform: (self.width, self.height),
                face: (face.width, face.height),
            });
        }
        self.blit(face, 0, 0)?;
        self.connection
            .flush()
            .map_err(|error| transport(error.to_string()))?;
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
            crate::platform::apply_patch(&mut next, patch)?;
        }
        for patch in patches {
            self.blit(&patch.face, patch.left, patch.top)?;
        }
        self.connection
            .flush()
            .map_err(|error| transport(error.to_string()))?;
        self.presented = Some(next);
        Ok(())
    }
}

fn pack_component(value: u8, mask: u32) -> u32 {
    if mask == 0 {
        return 0;
    }
    let shift = mask.trailing_zeros();
    let maximum = mask >> shift;
    (((u32::from(value) * maximum + 127) / 255) << shift) & mask
}

fn transport(message: impl Into<String>) -> PlatformError {
    PlatformError::Transport(message.into())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn direct_color_packing_is_integer_and_mask_relative() {
        assert_eq!(pack_component(255, 0x00ff_0000), 0x00ff_0000);
        assert_eq!(pack_component(128, 0x0000_ff00), 0x0000_8000);
        assert_eq!(pack_component(0, 0x0000_00ff), 0);
    }
}
