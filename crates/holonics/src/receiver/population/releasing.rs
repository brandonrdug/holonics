//! A release view of the population's scored, request-conditioned next-cell face.
//!
//! `Population::plan_relation` declares request incidence before its target arrives; the caller
//! must then advance through that request and the response opening on the same admitted receiver
//! used for scoring. This consumer exposes that exact face with one caller-designated class; a
//! section letter is designated only when the response actually stops. The complete text path
//! is checked by `text_release`; this view does not sample or invent a continuation.

use crate::ratio::algebraic::ExactInterval;
use crate::receiver::population::{Population, PopulationError};
use thiserror::Error;

/// Why a population face could not be exposed as a release.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ReleaseRefusal {
    /// The designated class is outside the scored alphabet.
    #[error("class {class} is outside the scored alphabet of size {alphabet}")]
    ClassOutsideAlphabet { class: usize, alphabet: usize },
    /// The population could not supply its scored face.
    #[error("the population has no releasable scored face: {0}")]
    ScoredFace(String),
}

/// The next response face at the population's current receiver section.
///
/// The `face` is copied verbatim from [`Population::face`], so for every class `y`,
/// `P_release(y | request, Θ) = P_scored(y | request, Θ)` provided the caller has already
/// positioned the population at the same request-conditioned state. The designated class is an
/// ordinary member of that same alphabet; the eventual stop letter is one such class. Decoder,
/// key/family provenance and a grain/fibre witness are not represented by this byte population;
/// callers must not interpret this view as carrying them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PopulationRelease {
    face: Vec<ExactInterval>,
    selected_class: usize,
}

impl PopulationRelease {
    /// Expose the scored population face with one designated class before that class is received.
    pub fn from_scored_face(
        population: &Population,
        selected_class: usize,
    ) -> Result<Self, ReleaseRefusal> {
        let alphabet = population.alphabet();
        if selected_class >= alphabet {
            return Err(ReleaseRefusal::ClassOutsideAlphabet {
                class: selected_class,
                alphabet,
            });
        }
        let face = population
            .face()
            .map_err(|error: PopulationError| ReleaseRefusal::ScoredFace(error.to_string()))?;
        Ok(Self {
            face,
            selected_class,
        })
    }

    /// The exact enclosure face used by scoring, including the designated class.
    pub fn face(&self) -> &[ExactInterval] {
        &self.face
    }

    /// The class designated for this reception tick.
    pub fn selected_class(&self) -> usize {
        self.selected_class
    }
}
