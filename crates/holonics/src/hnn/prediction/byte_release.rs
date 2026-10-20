//! Exact byte boundary of the actual scored receiving release (Refs #73 #148 #386).
//!
//! [definition; agent-inferred] The exterior chart is four high-first base-four cells per octet:
//! `D(E(b)) = b`. No class is EOS: all four classes are data. Only complete groups are decoded;
//! the unfinished cells and incomplete/invalid UTF-8 remain explicit beside the exact bytes.
//! [`Base4Bytes::read_release`] consumes the existing [`CellRelease`], preserving its complete
//! decisions, scored faces, plural fibres and key/certificate refusals. It never selects a class,
//! opens another receiving window, ingests its output, creates a pump, or changes retained state.
//!
//! The actual consumer is `Reference::release_cells`: its current Word is read through retained
//! R and the native scored tree/population. That owner is conditional cell release over its
//! admitted receiving aperture. This decoder does not turn it into bank joint-field generation.
//! In particular, Alpha's receiver has aperture one: its single released base-four class is an
//! unfinished octet, not text. A complete finite aperture likewise supplies no variable-reply
//! stopping law. The missing actual-R/tree joint-field completion remains owed, rather than being
//! replaced by repeated picks, an authored receiving bank or an invented EOS.
//!
//! Of the winding guide's six objects this boundary reads faces and placement. Its helix,
//! helical pair contacts, cell holonomy, tube and tower thread remain with the producing native
//! receiver. The lessons' fixture-as-capability and recitation failures are avoided by reporting
//! the actual boundary and its unresolved remainder; no corpus enters this operator.

use thiserror::Error;

use crate::hnn::receiving::cells::CellRelease;

/// A malformed exterior chart or an exceeded caller-declared decoding workload.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum ByteBoundaryError {
    #[error("the byte boundary admits at most {limit} native cells, requested {requested}")]
    CellBudget { limit: usize, requested: usize },
    #[error("cell {at} has class {class}; the byte boundary has classes 0 through 3")]
    ClassOutside { at: usize, class: usize },
    #[error("the native release's cells are not a contiguous prefix of its declared aperture")]
    NoncontiguousRelease,
    #[error("the native release contains a decision after a held or refused cell")]
    DecisionAfterHold,
}

/// The UTF-8 face of the exact complete octets. Bytes are always retained in [`ByteBoundary`].
/// No replacement character or inferred completion enters this reading.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Utf8Boundary {
    Complete(String),
    Unfinished {
        valid_prefix: String,
        pending_bytes: Vec<u8>,
    },
    Invalid {
        valid_prefix: String,
        invalid_from: usize,
        invalid_length: usize,
    },
}

/// Exact octets, the uncompleted group of fewer than four cells, and their UTF-8 reading.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByteBoundary {
    pub bytes: Vec<u8>,
    pub unfinished_cells: Vec<usize>,
    pub utf8: Utf8Boundary,
}

impl ByteBoundary {
    /// Text only when every supplied cell belongs to a complete octet and the octets are UTF-8.
    /// This is completion of this supplied boundary, never a claim that a reply has ended.
    pub fn complete_boundary_text(&self) -> Option<&str> {
        match (&self.utf8, self.unfinished_cells.is_empty()) {
            (Utf8Boundary::Complete(text), true) => Some(text),
            _ => None,
        }
    }
}

/// The native release unchanged, with a byte reading of its actually emitted prefix.
/// If a later phase holds, complete earlier octets are observable prefix data; they do not
/// constitute a whole-section release. Inspect [`Self::section_released`] separately.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByteRelease {
    pub native: CellRelease,
    pub boundary: ByteBoundary,
}

impl ByteRelease {
    /// Whether every phase of this finite native receiving aperture emitted a class.
    pub fn section_released(&self) -> bool {
        self.native.classes().is_some()
    }

    /// Complete text only when the native finite section released and its bytes all decode.
    /// There is no inferred EOS or complete variable-length reply in this return.
    pub fn released_section_text(&self) -> Option<&str> {
        self.section_released()
            .then(|| self.boundary.complete_boundary_text())
            .flatten()
    }
}

/// Stateless exterior codec shared by input and output. The cell budget is supplied by the
/// caller for each decoding request; it bounds work, not native phase or release laws.
pub struct Base4Bytes;

impl Base4Bytes {
    /// Four high-first base-four cells for each octet, matching Alpha's admitted byte chart.
    pub fn encode(bytes: &[u8]) -> Vec<usize> {
        bytes
            .iter()
            .flat_map(|byte| {
                [
                    usize::from(byte >> 6),
                    usize::from((byte >> 4) & 3),
                    usize::from((byte >> 2) & 3),
                    usize::from(byte & 3),
                ]
            })
            .collect()
    }

    /// Decode complete byte groups exactly, preserving the uncompleted group and UTF-8 fibre.
    pub fn decode(cells: &[usize], max_cells: usize) -> Result<ByteBoundary, ByteBoundaryError> {
        if cells.len() > max_cells {
            return Err(ByteBoundaryError::CellBudget {
                limit: max_cells,
                requested: cells.len(),
            });
        }
        for (at, &class) in cells.iter().enumerate() {
            if class >= 4 {
                return Err(ByteBoundaryError::ClassOutside { at, class });
            }
        }
        let mut groups = cells.chunks_exact(4);
        let bytes: Vec<u8> = groups
            .by_ref()
            .map(|group| {
                // Every class was checked below four; the result is exactly one octet.
                ((group[0] << 6) | (group[1] << 4) | (group[2] << 2) | group[3]) as u8
            })
            .collect();
        let utf8 = match std::str::from_utf8(&bytes) {
            Ok(text) => Utf8Boundary::Complete(text.to_owned()),
            Err(error) => {
                // Utf8Error certifies this exact prefix; no lossy conversion is performed.
                let prefix = std::str::from_utf8(&bytes[..error.valid_up_to()])
                    .expect("the UTF-8 owner certified this prefix")
                    .to_owned();
                match error.error_len() {
                    Some(invalid_length) => Utf8Boundary::Invalid {
                        valid_prefix: prefix,
                        invalid_from: error.valid_up_to(),
                        invalid_length,
                    },
                    None => Utf8Boundary::Unfinished {
                        valid_prefix: prefix,
                        pending_bytes: bytes[error.valid_up_to()..].to_vec(),
                    },
                }
            }
        };
        Ok(ByteBoundary {
            bytes,
            unfinished_cells: groups.remainder().to_vec(),
            utf8,
        })
    }

    /// Read only the actual emitted native prefix, preserving every native decision unchanged.
    /// A held/plural/refused cell contributes no digit. No later cell is silently skipped.
    pub fn read_release(
        native: CellRelease,
        max_cells: usize,
    ) -> Result<ByteRelease, ByteBoundaryError> {
        if native.aperture > max_cells {
            return Err(ByteBoundaryError::CellBudget {
                limit: max_cells,
                requested: native.aperture,
            });
        }
        if native.cells.len() > native.aperture
            || native
                .cells
                .iter()
                .enumerate()
                .any(|(phase, cell)| cell.phase != phase)
        {
            return Err(ByteBoundaryError::NoncontiguousRelease);
        }
        let mut emitted = Vec::with_capacity(native.cells.len());
        let mut held = false;
        for cell in &native.cells {
            if held {
                return Err(ByteBoundaryError::DecisionAfterHold);
            }
            match cell.class() {
                Some(class) => emitted.push(class),
                None => held = true,
            }
        }
        let boundary = Self::decode(&emitted, max_cells)?;
        Ok(ByteRelease { native, boundary })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::receiving::cells::CellDecision;
    use crate::ratio::{Rat, algebraic::ExactInterval};
    use crate::receiver::release::{ReleaseReturn, commit};
    use num_traits::{One, Zero};

    fn decided(classes: &[usize], aperture: usize, plural: bool) -> CellRelease {
        let mut cells = classes
            .iter()
            .enumerate()
            .map(|(phase, &class)| {
                let face: Vec<_> = (0..4)
                    .map(|candidate| {
                        ExactInterval::point(if candidate == class {
                            Rat::one()
                        } else {
                            Rat::zero()
                        })
                    })
                    .collect();
                let decision = commit(&face).unwrap();
                CellDecision {
                    phase,
                    release: decision.release,
                    classes: decision.classes,
                    key: None,
                    bits: 1,
                    face,
                    scored_face: None,
                }
            })
            .collect::<Vec<_>>();
        if plural {
            let face = vec![ExactInterval::point(crate::ratio::rat(1, 4)); 4];
            let decision = commit(&face).unwrap();
            assert!(matches!(decision.release, ReleaseReturn::Hold));
            cells.push(CellDecision {
                phase: cells.len(),
                release: decision.release,
                classes: decision.classes,
                key: None,
                bits: 1,
                face,
                scored_face: None,
            });
        }
        CellRelease { cells, aperture }
    }

    #[test]
    fn byte_codec_round_trips_every_octet_without_an_eos_digit() {
        let bytes: Vec<u8> = (0..=255).collect();
        let cells = Base4Bytes::encode(&bytes);
        let boundary = Base4Bytes::decode(&cells, cells.len()).unwrap();
        assert_eq!(boundary.bytes, bytes);
        assert!(boundary.unfinished_cells.is_empty());
        assert_eq!(Base4Bytes::decode(&[0, 0, 0, 0], 4).unwrap().bytes, vec![0]);
    }

    #[test]
    fn a_native_single_cell_is_an_unfinished_octet_never_empty_text() {
        let native = decided(&[2], 1, false);
        let reading = Base4Bytes::read_release(native.clone(), 1).unwrap();
        assert_eq!(reading.native, native);
        assert!(reading.section_released());
        assert_eq!(reading.boundary.unfinished_cells, vec![2]);
        assert_eq!(reading.released_section_text(), None);
    }

    #[test]
    fn a_complete_native_section_decodes_multiple_bytes_without_changing_its_decisions() {
        let cells = Base4Bytes::encode("Aé".as_bytes());
        let native = decided(&cells, cells.len(), false);
        let reading = Base4Bytes::read_release(native.clone(), cells.len()).unwrap();
        assert_eq!(reading.native, native);
        assert_eq!(reading.boundary.bytes, "Aé".as_bytes());
        assert_eq!(reading.released_section_text(), Some("Aé"));
    }

    #[test]
    fn an_actual_continuation_refusal_survives_the_byte_read_unchanged() {
        let native = CellRelease {
            aperture: 4,
            cells: vec![CellDecision {
                phase: 0,
                release: ReleaseReturn::NoContinuationBridges {
                    reason: "the declared key stream has no key left".to_owned(),
                },
                classes: Vec::new(),
                key: None,
                bits: 1,
                face: Vec::new(),
                scored_face: None,
            }],
        };
        let reading = Base4Bytes::read_release(native.clone(), 4).unwrap();
        assert_eq!(reading.native, native);
        assert!(!reading.section_released());
        assert_eq!(reading.released_section_text(), None);
    }

    #[test]
    fn plural_native_cell_keeps_its_fibre_and_does_not_emit_a_digit() {
        let cells = Base4Bytes::encode(b"A");
        let native = decided(&cells, 5, true);
        let reading = Base4Bytes::read_release(native.clone(), 5).unwrap();
        assert_eq!(reading.native, native);
        assert_eq!(reading.boundary.bytes, b"A");
        assert!(!reading.section_released());
        assert_eq!(reading.released_section_text(), None);
        assert_eq!(reading.native.cells[4].classes.len(), 4);
    }

    #[test]
    fn utf8_tails_and_invalid_octets_are_preserved_without_replacement() {
        let cells = Base4Bytes::encode("é".as_bytes());
        let unfinished = Base4Bytes::decode(&cells[..4], 8).unwrap();
        assert_eq!(
            unfinished.utf8,
            Utf8Boundary::Unfinished {
                valid_prefix: String::new(),
                pending_bytes: vec![0xc3],
            }
        );
        assert_eq!(
            Base4Bytes::decode(&cells, 8)
                .unwrap()
                .complete_boundary_text(),
            Some("é")
        );
        let invalid = Base4Bytes::decode(&Base4Bytes::encode(&[b'A', 0xff]), 8).unwrap();
        assert_eq!(invalid.bytes, vec![b'A', 0xff]);
        assert_eq!(
            invalid.utf8,
            Utf8Boundary::Invalid {
                valid_prefix: "A".to_owned(),
                invalid_from: 1,
                invalid_length: 1,
            }
        );
    }

    #[test]
    fn boundary_work_and_foreign_classes_are_refused_explicitly() {
        assert_eq!(
            Base4Bytes::decode(&[0, 1], 1),
            Err(ByteBoundaryError::CellBudget {
                limit: 1,
                requested: 2
            })
        );
        assert_eq!(
            Base4Bytes::decode(&[4], 1),
            Err(ByteBoundaryError::ClassOutside { at: 0, class: 4 })
        );
    }
}
