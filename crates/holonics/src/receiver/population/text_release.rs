//! Exterior UTF-8 chart for a complete population response and checked scalar continuation.
//!
//! This codec checks the byte/text squares and the *whole emitted cell path*: one score-identical
//! face from the population before every byte and before the stopping section. It does not locate
//! the producing keys or causal ancestry; those remain explicit missing producer terms. A caller
//! must collect the path at its actual successive standings, not reconstruct it after the fact.

use crate::compression::landmark::context::SectionChart;
use crate::receiver::population::releasing::PopulationRelease;
use crate::receiver::population::{Population, PopulationError};

/// Decoder for the identity UTF-8 byte chart followed by a declared section letter.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TextDecoder;

/// The append-scalar action `T`; its byte action `U` appends that scalar's UTF-8 encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TextAppend(pub char);

/// Exact operands identifying a failed text release square.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TextSeparator {
    InvalidUtf8 {
        bytes: Vec<u8>,
        valid_up_to: usize,
    },
    InvalidSection {
        section_class: usize,
        alphabet: usize,
    },
    ByteChartMismatch {
        declared_byte_classes: usize,
    },
    PathLength {
        expected: usize,
        actual: usize,
    },
    ClassMismatch {
        at: usize,
        expected: usize,
        actual: usize,
    },
    FaceShape {
        at: usize,
        expected_alphabet: usize,
        actual: usize,
    },
    ZeroSelectedFace {
        at: usize,
        class: usize,
    },
    DecodeEncode {
        source: String,
        encoded: Vec<u8>,
        decoded: Option<String>,
    },
    AppendSquare {
        source: String,
        action: char,
        left: Option<String>,
        right: Option<String>,
    },
    PopulationAlphabet {
        expected: usize,
        actual: usize,
    },
    Receive {
        tick: usize,
        cause: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TextReleaseError {
    Separator(TextSeparator),
}

/// Verify one actual scored path on a disposable, contemporary future branch.
///
/// Each face is captured immediately before its byte or stop cell is received. A receive
/// refusal can occur after earlier cells have moved the branch; the caller must discard that
/// branch on any error. The resulting trace checks this path's score and decoder square only; it
/// proves neither full distribution equality, the producing-key relation, a compatible-source
/// fibre, nor F5 health.
pub fn verify_scored_text_path(
    population: &mut Population,
    bytes: &[u8],
    section_class: usize,
    chart: SectionChart,
) -> Result<TextRelease, TextReleaseError> {
    if chart.bytes() != 256 {
        return Err(TextReleaseError::Separator(
            TextSeparator::ByteChartMismatch {
                declared_byte_classes: chart.bytes(),
            },
        ));
    }
    if chart.section(section_class).is_none() {
        return Err(TextReleaseError::Separator(TextSeparator::InvalidSection {
            section_class,
            alphabet: chart.alphabet(),
        }));
    }
    std::str::from_utf8(bytes).map_err(|error| {
        TextReleaseError::Separator(TextSeparator::InvalidUtf8 {
            bytes: bytes.to_vec(),
            valid_up_to: error.valid_up_to(),
        })
    })?;
    if population.alphabet() != chart.alphabet() {
        return Err(TextReleaseError::Separator(
            TextSeparator::PopulationAlphabet {
                expected: chart.alphabet(),
                actual: population.alphabet(),
            },
        ));
    }

    let mut trace = Vec::with_capacity(bytes.len() + 1);
    for (tick, cell) in bytes
        .iter()
        .map(|&byte| usize::from(byte))
        .chain([section_class])
        .enumerate()
    {
        trace.push(
            PopulationRelease::from_scored_face(population, cell).map_err(|error| {
                TextReleaseError::Separator(TextSeparator::Receive {
                    tick,
                    cause: error.to_string(),
                })
            })?,
        );
        population.receive(cell).map_err(|error: PopulationError| {
            TextReleaseError::Separator(TextSeparator::Receive {
                tick,
                cause: error.to_string(),
            })
        })?;
    }
    TextRelease::from_population_path(bytes.to_vec(), chart, section_class, &trace)
}

/// A checked response boundary with one score-identical enclosure face for every emitted cell.
/// The path does not yet carry the compatible-source fibre or producing-key provenance required
/// to publish an F4 text release.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TextRelease {
    decoder: TextDecoder,
    bytes: Vec<u8>,
    section_class: usize,
    decoded: String,
    face_trace: Vec<PopulationRelease>,
    /// Producer keys and causal egg provenance are not available from the current population API.
    producer_provenance: Option<String>,
}

impl TextRelease {
    /// Join the checked text chart to a population release view at every response byte and at
    /// its stopping section. The views must be collected before their respective receptions.
    pub fn from_population_path(
        bytes: Vec<u8>,
        chart: SectionChart,
        section_class: usize,
        path: &[PopulationRelease],
    ) -> Result<Self, TextReleaseError> {
        Self::checked(bytes, chart, section_class, path)
    }

    /// Check `D E = ρ`, `E_next T = U E`, and the score-identical face at every byte and stop.
    pub fn checked(
        bytes: Vec<u8>,
        chart: SectionChart,
        section_class: usize,
        path: &[PopulationRelease],
    ) -> Result<Self, TextReleaseError> {
        if chart.bytes() != 256 {
            return Err(TextReleaseError::Separator(
                TextSeparator::ByteChartMismatch {
                    declared_byte_classes: chart.bytes(),
                },
            ));
        }
        if chart.section(section_class).is_none() {
            return Err(TextReleaseError::Separator(TextSeparator::InvalidSection {
                section_class,
                alphabet: chart.alphabet(),
            }));
        }
        let source = std::str::from_utf8(&bytes).map_err(|error| {
            TextReleaseError::Separator(TextSeparator::InvalidUtf8 {
                bytes: bytes.clone(),
                valid_up_to: error.valid_up_to(),
            })
        })?;
        if path.len() != bytes.len() + 1 {
            return Err(TextReleaseError::Separator(TextSeparator::PathLength {
                expected: bytes.len() + 1,
                actual: path.len(),
            }));
        }
        for (at, view) in path.iter().enumerate() {
            let expected = bytes
                .get(at)
                .map_or(section_class, |&byte| usize::from(byte));
            if view.selected_class() != expected {
                return Err(TextReleaseError::Separator(TextSeparator::ClassMismatch {
                    at,
                    expected,
                    actual: view.selected_class(),
                }));
            }
            if view.face().len() != chart.alphabet() {
                return Err(TextReleaseError::Separator(TextSeparator::FaceShape {
                    at,
                    expected_alphabet: chart.alphabet(),
                    actual: view.face().len(),
                }));
            }
            if view.face()[expected].upper == crate::ratio::Rat::from_integer(0.into()) {
                return Err(TextReleaseError::Separator(
                    TextSeparator::ZeroSelectedFace {
                        at,
                        class: expected,
                    },
                ));
            }
        }
        // The section letter follows the bytes in the population stream. It is retained in the
        // scored face; only the preceding 0..255 cells enter the UTF-8 decoder.
        let response = source.to_owned();
        let encoded = response.as_bytes().to_vec();
        let decoded = String::from_utf8(encoded.clone()).ok();
        if decoded.as_deref() != Some(response.as_str()) {
            return Err(TextReleaseError::Separator(TextSeparator::DecodeEncode {
                source: response,
                encoded,
                decoded,
            }));
        }
        Ok(Self {
            decoder: TextDecoder,
            bytes: encoded,
            section_class,
            decoded: response,
            face_trace: path.to_vec(),
            producer_provenance: None,
        })
    }

    /// Check the consumer square `E_next T = U E` for one explicit Unicode scalar append.
    pub fn append(&self, action: TextAppend) -> Result<String, TextReleaseError> {
        let mut left = self.decoded.clone();
        left.push(action.0);
        let left_bytes = left.as_bytes().to_vec();

        let mut right_bytes = self.bytes.clone();
        let mut scalar = [0; 4];
        right_bytes.extend_from_slice(action.0.encode_utf8(&mut scalar).as_bytes());
        let right = String::from_utf8(right_bytes).ok();
        if right.as_deref() != Some(left.as_str()) {
            return Err(TextReleaseError::Separator(TextSeparator::AppendSquare {
                source: self.decoded.clone(),
                action: action.0,
                left: Some(left),
                right,
            }));
        }
        debug_assert_eq!(
            left_bytes,
            right.as_ref().expect("checked equality").as_bytes()
        );
        Ok(left)
    }

    pub fn decoder(&self) -> TextDecoder {
        self.decoder
    }
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }
    pub fn section_class(&self) -> usize {
        self.section_class
    }
    pub fn text(&self) -> &str {
        &self.decoded
    }
    pub fn face_trace(&self) -> &[PopulationRelease] {
        &self.face_trace
    }
    pub fn producer_provenance(&self) -> Option<&str> {
        self.producer_provenance.as_deref()
    }
}
