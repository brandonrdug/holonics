//! A release view of the population's scored, request-conditioned next-cell face.
//!
//! `Population::plan_relation` declares request incidence before its target arrives; the caller
//! must then advance through that request and the response opening on the same admitted receiver
//! used for scoring. This consumer exposes that exact face, including the caller-declared stopping
//! cell. A text release still lacks its carried decoder, key provenance, grain/fibre and release
//! square. It does not sample or invent a continuation.

use crate::ratio::algebraic::ExactInterval;
use crate::receiver::population::{Population, PopulationError};
use thiserror::Error;

/// Why a population face could not be exposed as a release.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ReleaseRefusal {
    /// The declared stopping section is outside the scored alphabet.
    #[error("stopping class {class} is outside the scored alphabet of size {alphabet}")]
    StopOutsideAlphabet { class: usize, alphabet: usize },
    /// The population could not supply its scored face.
    #[error("the population has no releasable scored face: {0}")]
    ScoredFace(String),
}

/// A term the byte population does not yet supply for a text release.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MissingTextReleaseTerm {
    /// No carried decoder maps emitted byte classes to text.
    Decoder,
    /// No producing family and key provenance accompanies each face.
    ProducingFamilyAndKeyProvenance,
    /// No declared grain and compatible-fibre witness accompanies the face.
    GrainAndFibreWitness,
    /// The encoding/transport release square is not checked or separated.
    ReleaseSquare,
}

/// Why a text-release attempt was refused. The predictor face remains independently available.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
#[error("text release is missing required terms: {missing:?}")]
pub struct TextReleaseRefusal {
    /// Missing terms, in contract order.
    pub missing: Vec<MissingTextReleaseTerm>,
}

/// The next response face at the population's current receiver section.
///
/// The `face` is copied verbatim from [`Population::face`], so for every class `y`,
/// `P_release(y | request, Θ) = P_scored(y | request, Θ)` provided the caller has already
/// positioned the population at the same request-conditioned state. `stopping_class` is an
/// ordinary member of that same alphabet and therefore participates in the equality. Decoder,
/// key/family provenance and a grain/fibre witness are not represented by this byte population;
/// callers must not interpret this view as carrying them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PopulationRelease {
    face: Vec<ExactInterval>,
    stopping_class: usize,
}

impl PopulationRelease {
    /// Expose the scored population face as a release, designating its stopping-section class.
    pub fn from_scored_face(
        population: &Population,
        stopping_class: usize,
    ) -> Result<Self, ReleaseRefusal> {
        let alphabet = population.alphabet();
        if stopping_class >= alphabet {
            return Err(ReleaseRefusal::StopOutsideAlphabet {
                class: stopping_class,
                alphabet,
            });
        }
        let face = population
            .face()
            .map_err(|error: PopulationError| ReleaseRefusal::ScoredFace(error.to_string()))?;
        Ok(Self {
            face,
            stopping_class,
        })
    }

    /// The exact enclosure face used by scoring, including the stopping class.
    pub fn face(&self) -> &[ExactInterval] {
        &self.face
    }

    /// The class that closes the response at its declared section.
    pub fn stopping_class(&self) -> usize {
        self.stopping_class
    }
}

impl Population {
    /// Attempt a text release at the current receiver section.
    ///
    /// This byte population currently has no text decoder, per-face producing key provenance,
    /// grain/fibre witness, or checked release square. The typed refusal makes that boundary
    /// explicit and does not mutate or consume the population. Use [`Population::face`] or
    /// [`PopulationRelease::from_scored_face`] when a predictive face is wanted.
    pub fn attempt_text_release(
        &self,
        _stopping_class: usize,
    ) -> Result<String, TextReleaseRefusal> {
        Err(TextReleaseRefusal {
            missing: vec![
                MissingTextReleaseTerm::Decoder,
                MissingTextReleaseTerm::ProducingFamilyAndKeyProvenance,
                MissingTextReleaseTerm::GrainAndFibreWitness,
                MissingTextReleaseTerm::ReleaseSquare,
            ],
        })
    }
}
