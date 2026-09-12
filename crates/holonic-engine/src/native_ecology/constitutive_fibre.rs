//! One developing local linear constitutive relation, with its full open receiver fibre.
//!
//! Seed hypothesis: paired currents inhabit one declared rational-linear source/receiver chart.
//! This is NOT an assumption that HNA, language, or arbitrary contexts are globally linear.
//! The resident body forms the span of received pairs, not a selected total coefficient map.
//! The explicit bilinear contact composes two separately declared complex current ports and
//! their mixed products into this same relation. Its source law is bound at founding; a flattened
//! array cannot silently stand in for that contact. The condition must have its actual situated
//! channel/receiver meaning in the application, not merely a contextual name.
//! Source-only and paired occurrences use the same operation and continuing owner. Outside the
//! source projection there is no inferred response; a vertical fibre remains plural, not averaged.
//! Formal owner: `Computation/HolonicConstitutiveFibre.lean`. Native incidence, physical contact
//! and the wider ecology must still be composed: this local owner alone does not complete NCF1.

use relational_geometry::Rat;
use serde::Serialize;
use std::rc::Rc;
use thiserror::Error;

use crate::resident_section::{
    ResidentGrain, ResidentRefusal, ResidentSection, ResidentSectionRest, ResidentSurface,
    TransferCensus,
};

mod circulation;
pub use circulation::*;
mod field;
pub use field::*;
mod law_rest;
mod resident;
pub use law_rest::ConstitutiveFibreRest;
pub use resident::{
    AffineContactReading, ConditionContactMetric, ConditionContactReading, ConditionContactStatus,
    ConditionCoverage, ConditionCurrentRest, ConditionImageReading, ConditionPreimageReading,
    ConditionPreimageRest, ConstitutiveDifferentialReading, ConstitutiveImageReading,
    ConstitutiveImageReceiver, ConstitutiveReturnRest, ContextualSectionOrigin,
    GeneratorNeighborhoodRest, GeneratorNeighborhoodStep, NeighborhoodEvidence,
    NeighborhoodEvidenceRest, NormalWaveRelationRest, PreparedConditionContact,
    ResidentAffineContact, ResidentConditionContact, ResidentConditionCurrent,
    ResidentConditionImage, ResidentConditionPreimage, ResidentConditionStanding,
    ResidentConstitutiveCurrent, ResidentConstitutiveImage, ResidentConstitutiveRefinement,
    ResidentConstitutiveReturn, ResidentConstitutiveSection, ResidentContextualSection,
    ResidentDifferenceSection, ResidentGeneratorNeighborhood, ResidentSourcePairs,
    ResidentWavePullback, ResidentWaveRelation, ResidentWaveSourceContact, WaveSourceReceiver,
};

/// Declared local source law, bound at founding rather than inferred from an array's width.
/// These dimensions are the caller's interface chart, not learned semantic capacities.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum ConstitutiveSourceChart {
    Linear,
    /// Source, condition and their complete complex tensor product participate in one contact.
    BilinearContact {
        source_complex: usize,
        condition_complex: usize,
    },
}

#[derive(Debug, PartialEq, Eq, Serialize)]
pub enum ConstitutiveReading {
    Unique {
        current: Vec<Rat>,
    },
    /// No response is claimed at this source. The remainder is the exact source direction which
    /// the currently presented domain does not carry, in its retained elimination chart.
    OutsideDomain {
        source_remainder: Vec<Rat>,
    },
    /// Every `particular + span(directions)` is retained. None is selected as the answer.
    Plural {
        particular: Vec<Rat>,
        directions: Vec<Vec<Rat>>,
    },
}

#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct ConstitutiveFibreReturn {
    pub occurrence: u64,
    pub predecessor_reading: ConstitutiveReading,
    /// A pivot is a coordinate of the represented relation, not a semantic identity.
    pub formed_pivot: Option<usize>,
    pub successor_rank: usize,
}

#[derive(Debug, Error)]
pub enum ConstitutiveFibreError {
    #[error("source field passage {row}: {source}")]
    SourcePassage {
        row: usize,
        #[source]
        source: Box<ConstitutiveFibreError>,
    },
    #[error("native ecology rest: {0}")]
    Rest(String),
    #[error("the receiving edge does not carry an available emission from this ecology")]
    ForeignOccurrence,
    #[error(
        "local exact elimination requires {required} shared octets; the mounted apparatus admits {available}"
    )]
    ScratchAperture { required: usize, available: u32 },
    #[error("local constitutive chart shape or integer aperture is invalid")]
    Shape,
    #[error(
        "the last device operation/readout has uncertain completion; this owner cannot replay it"
    )]
    Uncertain,
    #[error("native constitutive arithmetic refused without depositing a row: {0}")]
    Arithmetic(String),
    #[error(transparent)]
    Resident(#[from] ResidentRefusal),
}

/// One move-owned local relation. Ordinary elimination stages a new row before its write.
/// A neighborhood transaction stages the affected member basis in a separate resident section;
/// this protects compound publication without copying a continuing ecology.
pub struct ResidentConstitutiveFibre<'chart> {
    basis: ResidentSection<'chart>,
    basis_owner: Rc<()>,
    surface: &'chart ResidentSurface<'chart>,
    source_width: usize,
    target_width: usize,
    source_chart: ConstitutiveSourceChart,
    occurrences: u64,
    usable: bool,
}

impl<'chart> ResidentConstitutiveFibre<'chart> {
    fn check_extent(
        surface: &'chart ResidentSurface<'chart>,
        source_width: usize,
        target_width: usize,
    ) -> Result<(usize, usize), ConstitutiveFibreError> {
        let width = source_width
            .checked_add(target_width)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let count = width
            .checked_mul(width)
            .ok_or(ConstitutiveFibreError::Shape)?;
        if source_width == 0 || target_width == 0 || width > u32::MAX as usize - 4 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let scratch = width.checked_mul(32).ok_or(ConstitutiveFibreError::Shape)?;
        let available = surface.declaration().max_sectiond_bytes;
        if scratch > available as usize {
            return Err(ConstitutiveFibreError::ScratchAperture {
                required: scratch,
                available,
            });
        }
        Ok((width, count))
    }

    pub fn found(
        surface: &'chart ResidentSurface<'chart>,
        source_width: usize,
        target_width: usize,
    ) -> Result<Self, ConstitutiveFibreError> {
        let (width, count) = Self::check_extent(surface, source_width, target_width)?;
        let mut zeros = Vec::new();
        zeros
            .try_reserve_exact(count)
            .map_err(|_| ConstitutiveFibreError::Shape)?;
        zeros.resize(count, (0, 0));
        let basis = surface.mount_section_rest(
            &ResidentSectionRest::found(width, width, ResidentGrain(0), 64, zeros)
                .map_err(|_| ConstitutiveFibreError::Shape)?,
        )?;
        Ok(Self {
            basis,
            basis_owner: Rc::new(()),
            surface,
            source_width,
            target_width,
            source_chart: ConstitutiveSourceChart::Linear,
            occurrences: 0,
            usable: true,
        })
    }

    pub fn occurrences(&self) -> u64 {
        self.occurrences
    }

    pub fn source_chart(&self) -> ConstitutiveSourceChart {
        self.source_chart
    }

    /// Found the existing local relation over an explicit two-current contact. No coefficient,
    /// class label or source-selection rule is supplied. Mixed action is learned from returns.
    pub fn found_bilinear_contact(
        surface: &'chart ResidentSurface<'chart>,
        source_complex: usize,
        condition_complex: usize,
        target_complex: usize,
    ) -> Result<Self, ConstitutiveFibreError> {
        if source_complex == 0 || condition_complex == 0 || target_complex == 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let width = source_complex
            .checked_mul(condition_complex)
            .and_then(|n| n.checked_add(source_complex))
            .and_then(|n| n.checked_add(condition_complex))
            .and_then(|n| n.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let target_width = target_complex
            .checked_mul(2)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let mut body = Self::found(surface, width, target_width)?;
        body.source_chart = ConstitutiveSourceChart::BilinearContact {
            source_complex,
            condition_complex,
        };
        Ok(body)
    }

    pub fn census(&self) -> TransferCensus {
        self.surface.census()
    }

    /// One occurrence in this local chart. `receiving` is an actual co-measured current at the
    /// paired receiver port, not a reward, admission Boolean or requested output. Its presence
    /// joins the paired relation after the same operation reads the predecessor domain.
    ///
    /// Integer currents are the first apparatus mouth; all derived responses remain rational.
    /// The kernel—not the caller—derives the pivot, rank change, response and open fibre.
    pub fn advance(
        &mut self,
        source: &[i64],
        receiving: Option<&[i64]>,
    ) -> Result<ConstitutiveFibreReturn, ConstitutiveFibreError> {
        if !self.usable {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        if self.source_chart != ConstitutiveSourceChart::Linear
            || source.len() != self.source_width
            || receiving.is_some_and(|v| v.len() != self.target_width)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let next = self
            .occurrences
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let width = self.source_width + self.target_width;
        let mut input = source.iter().map(|v| (*v, *v)).collect::<Vec<_>>();
        input.extend((0..self.target_width).map(|j| {
            let value = receiving.map_or(0, |v| v[j]);
            (value, value)
        }));
        let input = self.surface.mount_section_rest(
            &ResidentSectionRest::found(1, width, ResidentGrain(0), 64, input)
                .map_err(|_| ConstitutiveFibreError::Shape)?,
        )?;
        let output = self.surface.fresh_section(1, width + 4, ResidentGrain(0))?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface.record_constitutive_fibre(
                &lane,
                &mut self.basis,
                &input,
                self.source_width,
                receiving.is_some(),
                &output,
            )?;
        }
        passage.close(0, &output, 64)?;
        let passage = passage.finish()?;
        // A launch/readback failure cannot authorize silently repeating a possibly committed row.
        self.usable = false;
        let reading = passage.launch()?;
        if !reading.obstruction.is_empty() {
            self.usable = true; // the kernel refuses before its sole continuing write
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "{:?}",
                reading.obstruction
            )));
        }
        let returned = self.surface.read_out(&output)?;
        if returned.iter().any(|(lo, hi)| lo != hi) || returned[width].0 <= 0 {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let formed_pivot = match returned[width + 2].0 {
            -1 => None,
            p if p >= 0 && (p as usize) < width => Some(p as usize),
            _ => return Err(ConstitutiveFibreError::Uncertain),
        };
        let predecessor_reading = self.decode_reading(&returned, 0, formed_pivot)?;
        let rank = usize::try_from(returned[width + 3].0)
            .map_err(|_| ConstitutiveFibreError::Uncertain)?;
        if rank > width {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        self.occurrences = next;
        self.usable = true;
        Ok(ConstitutiveFibreReturn {
            occurrence: next,
            predecessor_reading,
            formed_pivot,
            successor_rank: rank,
        })
    }

    fn decode_reading(
        &self,
        returned: &[(i64, i64)],
        at: usize,
        exclude: Option<usize>,
    ) -> Result<ConstitutiveReading, ConstitutiveFibreError> {
        let width = self.source_width + self.target_width;
        let denominator = returned[at + width].0;
        if denominator <= 0 {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let rational = |j: usize| Rat::new(returned[at + j].0.into(), denominator.into());
        let particular = || (self.source_width..width).map(rational).collect();
        let reading = match returned[at + width + 1].0 {
            0 => ConstitutiveReading::Unique {
                current: particular(),
            },
            1 => ConstitutiveReading::OutsideDomain {
                source_remainder: (0..self.source_width).map(rational).collect(),
            },
            2 => {
                // This is an explicitly requested full receiver fibre, not a host numerical
                // decision used to conduct the operation. A predecessor reading excludes the
                // newly formed pivot; a successor reading excludes nothing.
                let standing = self.surface.read_out(&self.basis)?;
                let directions = (self.source_width..width)
                    .filter(|p| Some(*p) != exclude && standing[p * width + p].0 != 0)
                    .map(|p| {
                        (self.source_width..width)
                            .map(|j| Rat::from_integer(standing[p * width + j].0.into()))
                            .collect()
                    })
                    .collect();
                ConstitutiveReading::Plural {
                    particular: particular(),
                    directions,
                }
            }
            _ => return Err(ConstitutiveFibreError::Uncertain),
        };
        Ok(reading)
    }

    /// Exterior inspection of the represented relation. This is not yet a durable whole-HNA
    /// artifact or a source-independence claim. The native operation never reads this wire back.
    pub fn inspect_relation(&self) -> Result<ResidentSectionRest, ConstitutiveFibreError> {
        Ok(self.surface.detach_section(&self.basis, 64)?)
    }
}

#[cfg(test)]
mod tests;
