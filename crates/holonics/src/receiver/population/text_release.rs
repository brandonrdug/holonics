//! **The population's text-release consumer** (THE_REBUILD F4 and U3): the response drawn through
//! the one decision law, and the exterior UTF-8 chart it is checked by.
//!
//! [definition] **The response** ([`Population::release_response`]). From the request-conditioned
//! standing (the request planned and received, the response opened), each cell is one
//! `receiver::release::draw` of a declared key, under one of two laws ([`ResponseLaw`]): from the
//! population's scored face (`P_release = P_scored` at every cell), or, the ancestral law, from the
//! exact face of one family drawn once from the posterior enclosure (`Population::select_family`).
//! Its receipt ([`ResponseRelease`]) is the sequence of the law's returns:
//! - `Drawn` for every emitted cell, with its key and certified cell;
//! - **the stop law**: the response ends at the first drawn section letter, which is emitted and
//!   received; a byte drawn when the aperture keeps no room for the stop is not emitted, and the
//!   return is `NoContinuationBridges`, naming the byte and the aperture;
//! - `Unresolved` where the enclosure leaves a key plural (the family draw or a cell draw): nothing
//!   is emitted and the unresolved draw mass is kept, with its crossing bounds;
//! - typed refusals ([`ResponseRefusal`]) for operands that stop the response.
//!
//! Under the scored law each emitted cell also carries the score-identical face it was drawn from
//! (the F4 view) and its family provenance (`Population::face_contributors`: every family's enclosed
//! share of the drawn class, with the missing per-key and causal terms named). Under the ancestral
//! law the producer of every cell is the drawn family itself.
//!
//! [definition] **The chart.** This codec checks the byte/text squares and the *whole emitted cell
//! path*: one score-identical face from the population before every byte and before the stopping
//! section. It does not locate the producing keys or causal ancestry; those remain explicit missing
//! producer terms. A caller must collect the path at its actual successive standings, not
//! reconstruct it after the fact.

use crate::compression::landmark::context::SectionChart;
use crate::ratio::Rat;
use crate::ratio::algebraic::ExactInterval;
use crate::receiver::population::provenance::FaceContribution;
use crate::receiver::population::releasing::{FamilyReleaseError, PopulationRelease};
use crate::receiver::population::{Population, PopulationError};
use crate::receiver::release::{DrawRefusal, ReleaseReturn, draw, draw_exact};

/// **How a response draws its cells**: the population's two release laws.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResponseLaw {
    /// Every cell is drawn from the population's scored face.
    Scored,
    /// One family is drawn from the posterior enclosure, then every cell from that family's exact
    /// face (the mixture's ancestral reading, `Σ_f w_f P_f = P`).
    Ancestral,
}

/// A response's typed refusal: the operands that stopped it, returned as content.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResponseRefusal {
    /// The chart is not the text chart this population receives on.
    Chart {
        declared_byte_classes: usize,
        chart_alphabet: usize,
        population_alphabet: usize,
    },
    /// The aperture keeps no room for the stopping section.
    NoRoomForStop { capacity: usize, cells: usize },
    /// The drawn family is not a member.
    FamilyMissing { family: usize },
    /// The face at `tick` could not be read.
    Face { tick: usize, cause: String },
    /// The face at `tick` is not drawable.
    Draw { tick: usize, refusal: DrawRefusal },
    /// The drawn class's provenance could not be read.
    Provenance { tick: usize, cause: String },
    /// The population refused the drawn class.
    Receive {
        tick: usize,
        class: usize,
        cause: String,
    },
}

/// **One response released through the one decision law** (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResponseRelease {
    /// The law the cells were drawn under.
    pub law: ResponseLaw,
    /// The ancestral law: the posterior enclosure the family draw read.
    pub posterior: Option<Vec<ExactInterval>>,
    /// The ancestral law: the family draw (`Drawn` with the family as its class, or
    /// `Unresolved`), or why the posterior was not drawable.
    pub family: Option<Result<ReleaseReturn, FamilyReleaseError>>,
    /// One return per cell drawn, in order: `Drawn` for each emitted cell; a final `Unresolved` or
    /// `NoContinuationBridges` when the response ends there.
    pub decisions: Vec<ReleaseReturn>,
    /// The scored law: the score-identical face before each emitted cell.
    pub trace: Vec<PopulationRelease>,
    /// The scored law: each emitted cell's family provenance.
    pub provenance: Vec<Vec<FaceContribution>>,
    /// The emitted bytes (the stop letter is not a byte).
    pub bytes: Vec<u8>,
    /// The stopping section, when the stop law ended the response.
    pub stop: Option<usize>,
    /// The typed refusal that stopped the response, if any.
    pub refusal: Option<ResponseRefusal>,
}

impl ResponseRelease {
    /// The cells emitted and received, the stop included.
    pub fn emitted(&self) -> usize {
        self.decisions
            .iter()
            .filter(|decision| matches!(decision, ReleaseReturn::Drawn(_)))
            .count()
    }

    /// The drawn family, under the ancestral law.
    pub fn drawn_family(&self) -> Option<usize> {
        match &self.family {
            Some(Ok(decision)) => decision.drawn_class(),
            _ => None,
        }
    }

    /// The return the response ended on, when it ended on a decision.
    pub fn last(&self) -> Option<&ReleaseReturn> {
        self.decisions.last()
    }

    /// The scored law's checked text: `D E = ρ`, `E_next T = U E` and the score-identical face at
    /// every byte and the stop, or the separator. `None` when the response did not stop or was not
    /// drawn under the scored law.
    pub fn text(&self, chart: SectionChart) -> Option<Result<TextRelease, TextReleaseError>> {
        let section = self.stop?;
        (self.law == ResponseLaw::Scored).then(|| {
            TextRelease::from_population_path(self.bytes.clone(), chart, section, &self.trace)
        })
    }
}

impl Population {
    /// **Release one response through the one decision law** (module header), from the current
    /// request-conditioned standing, drawing each key from `keys` (one for the ancestral family
    /// draw, then one per cell). `capacity` is the aperture in cells: the response keeps room for
    /// its stopping section within it. The population is moved by every emitted cell; a caller
    /// releasing from a standing it must keep branches it first (`Population::branch_future`).
    pub fn release_response(
        &mut self,
        chart: SectionChart,
        capacity: usize,
        law: ResponseLaw,
        keys: &mut dyn FnMut() -> Rat,
    ) -> ResponseRelease {
        let mut release = ResponseRelease {
            law,
            posterior: None,
            family: None,
            decisions: Vec::new(),
            trace: Vec::new(),
            provenance: Vec::new(),
            bytes: Vec::new(),
            stop: None,
            refusal: None,
        };
        if chart.bytes() != 256 || self.alphabet() != chart.alphabet() {
            release.refusal = Some(ResponseRefusal::Chart {
                declared_byte_classes: chart.bytes(),
                chart_alphabet: chart.alphabet(),
                population_alphabet: self.alphabet(),
            });
            return release;
        }
        if law == ResponseLaw::Ancestral {
            let key = keys();
            let posterior = self.family_posterior_face();
            release.family = Some(match &posterior {
                Ok(posterior) => draw(posterior, &key).map_err(FamilyReleaseError::from),
                Err(error) => Err(error.clone()),
            });
            release.posterior = posterior.ok();
        }
        let Some(room) = capacity.checked_sub(self.cells() + 1) else {
            release.refusal = Some(ResponseRefusal::NoRoomForStop {
                capacity,
                cells: self.cells(),
            });
            return release;
        };
        let family = match (law, &release.family) {
            (ResponseLaw::Scored, _) => None,
            (ResponseLaw::Ancestral, Some(Ok(ReleaseReturn::Drawn(drawn)))) => Some(drawn.class),
            (ResponseLaw::Ancestral, _) => return release,
        };
        for tick in 0..=room {
            let key = keys();
            let (decision, scored) = match family {
                None => {
                    let face = match self.face() {
                        Ok(face) => face,
                        Err(error) => {
                            release.refusal = Some(ResponseRefusal::Face {
                                tick,
                                cause: error.to_string(),
                            });
                            break;
                        }
                    };
                    (draw(&face, &key), Some(face))
                }
                Some(index) => {
                    let Some(member) = self.families().nth(index) else {
                        release.refusal = Some(ResponseRefusal::FamilyMissing { family: index });
                        break;
                    };
                    match member.face() {
                        Ok(face) => (draw_exact(&face, &key), None),
                        Err(error) => {
                            release.refusal = Some(ResponseRefusal::Face {
                                tick,
                                cause: error.to_string(),
                            });
                            break;
                        }
                    }
                }
            };
            let decision = match decision {
                Ok(decision) => decision,
                Err(refusal) => {
                    release.refusal = Some(ResponseRefusal::Draw { tick, refusal });
                    break;
                }
            };
            let Some(class) = decision.drawn_class() else {
                release.decisions.push(decision);
                break;
            };
            if class < chart.bytes() && release.bytes.len() == room {
                release.decisions.push(ReleaseReturn::NoContinuationBridges {
                    reason: format!(
                        "the drawn byte {class} leaves no room for the stopping section within \
                         the aperture of {capacity} cells"
                    ),
                });
                break;
            }
            // The scored law's view and provenance are read at the standing the cell was drawn at,
            // and kept once the cell is received.
            let scored = match scored {
                None => None,
                Some(face) => {
                    let view = match PopulationRelease::of_face(face, class) {
                        Ok(view) => view,
                        Err(error) => {
                            release.refusal = Some(ResponseRefusal::Face {
                                tick,
                                cause: error.to_string(),
                            });
                            break;
                        }
                    };
                    match self.face_contributors(class) {
                        Ok(contributors) => Some((view, contributors)),
                        Err(error) => {
                            release.refusal = Some(ResponseRefusal::Provenance {
                                tick,
                                cause: error.to_string(),
                            });
                            break;
                        }
                    }
                }
            };
            if let Err(error) = self.receive(class) {
                release.refusal = Some(ResponseRefusal::Receive {
                    tick,
                    class,
                    cause: error.to_string(),
                });
                break;
            }
            if let Some((view, contributors)) = scored {
                release.trace.push(view);
                release.provenance.push(contributors);
            }
            release.decisions.push(decision);
            if chart.section(class).is_some() {
                release.stop = Some(class);
                break;
            }
            // A byte class of the 256-byte chart.
            release.bytes.push(class as u8);
        }
        release
    }
}

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
