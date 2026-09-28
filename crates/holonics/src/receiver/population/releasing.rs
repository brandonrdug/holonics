//! **The population's release pipeline, read through the one decision law** (`receiver::release`;
//! THE_REBUILD U3 and F4).
//!
//! [definition] Two readings of the population enter a release, and both return the one law's arms:
//! - **The scored face view** ([`PopulationRelease`]). `Population::plan_relation` declares request
//!   incidence before its target arrives; the caller then advances through the request and the
//!   response opening on the same admitted receiver used for scoring. The view copies that exact
//!   face with one class, so `P_release(y | request, Θ) = P_scored(y | request, Θ)` for every class
//!   `y`, the stopping section included. A class is designated by a declared path (the verifier,
//!   `text_release::verify_scored_text_path`) or drawn from the same face by the certified draw
//!   (`Population::release_response`).
//! - **The family draw** ([`Population::select_family`]). The Bayesian mixture is the marginal of a
//!   once-chosen family and its whole future path, `Σ_f w_f P_f(y) = P_population(y)` (Lean
//!   `Population.population_mixture`). The family is drawn once from the request-conditioned
//!   posterior enclosure ([`Population::family_posterior_face`]) by `receiver::release::draw`, and
//!   the response then follows that family's exact face. A key the posterior enclosure leaves plural
//!   is `Unresolved`: the family draw emits nothing, so the released submeasure does not by itself
//!   prove equality of the full distributions.
//!
//! Decoder, producing-key provenance and a grain/fibre witness are not carried by the view; the
//! response receipt (`text_release`) carries what the release contract owns of them.

use crate::ratio::Rat;
use crate::ratio::algebraic::{ExactInterval, ExactValueError};
use crate::receiver::population::{Population, PopulationError};
use crate::receiver::release::{DrawRefusal, ReleaseReturn, draw};
use num_traits::{One, Zero};
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
/// positioned the population at the same request-conditioned state. The class is an ordinary
/// member of that same alphabet; the eventual stop letter is one such class.
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
        Self::of_face(face, selected_class)
    }

    /// The view of a face already read from the population at its current standing (the draw
    /// reads the face once and releases from it).
    pub(crate) fn of_face(
        face: Vec<ExactInterval>,
        selected_class: usize,
    ) -> Result<Self, ReleaseRefusal> {
        if selected_class >= face.len() {
            return Err(ReleaseRefusal::ClassOutsideAlphabet {
                class: selected_class,
                alphabet: face.len(),
            });
        }
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

/// Errors while reading the family posterior or drawing a family.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum FamilyReleaseError {
    /// The posterior enclosure is not a drawable face.
    #[error("the family draw was refused: {0}")]
    Draw(DrawRefusal),
    /// The population refused its posterior (an extinct population).
    #[error("population face was refused: {0}")]
    Population(String),
    /// An interval bound was reversed.
    #[error("population posterior interval was invalid: {0}")]
    Exact(String),
}

impl From<DrawRefusal> for FamilyReleaseError {
    fn from(error: DrawRefusal) -> Self {
        Self::Draw(error)
    }
}

impl From<PopulationError> for FamilyReleaseError {
    fn from(error: PopulationError) -> Self {
        Self::Population(error.to_string())
    }
}

impl From<ExactValueError> for FamilyReleaseError {
    fn from(error: ExactValueError) -> Self {
        Self::Exact(error.to_string())
    }
}

impl Population {
    /// The request-conditioned posterior enclosure of each declared family.
    ///
    /// This uses the same charged likelihood bounds and normalized total as `face`. Dead
    /// families remain in declaration order with point-zero mass. Each living family's
    /// normalized charged-weight bounds are converted outward to an exact rational enclosure;
    /// its cell face is read separately when following that selected family.
    pub fn family_posterior_face(&self) -> Result<Vec<ExactInterval>, FamilyReleaseError> {
        let charged = self.charged_bounds();
        let (total_lower, total_upper) = Self::total(&charged, 0..charged.len());
        if total_lower.is_zero() {
            return Err(PopulationError::Extinct { cell: self.cells }.into());
        }

        self.members
            .iter()
            .zip(charged.iter())
            .map(|(member, (charged_lower, charged_upper))| {
                if member.died.is_some() {
                    return Ok(ExactInterval::point(Rat::zero()));
                }
                let weight_lower = charged_lower.over(&total_upper, false).to_rat(false);
                let weight_upper = charged_upper
                    .over(&total_lower, true)
                    .to_rat(true)
                    .min(Rat::one());
                Ok(ExactInterval::new(weight_lower, weight_upper)?)
            })
            .collect()
    }

    /// **The family draw**: the certified draw of `key` from the posterior enclosure,
    /// `Drawn` with the family index as its class, or `Unresolved` with the crossing families.
    pub fn select_family(&self, key: &Rat) -> Result<ReleaseReturn, FamilyReleaseError> {
        Ok(draw(&self.family_posterior_face()?, key)?)
    }
}
