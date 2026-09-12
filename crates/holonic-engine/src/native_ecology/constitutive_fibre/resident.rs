//! Resident composition of the existing rational-linear constitutive relation.
//!
//! A returned rational current can enter another operation without a host numerical read.
//! The immutable return includes its original vertical fibre, even after later development.
//! A point-current consumer checks uniqueness on device; it never chooses from a plural fibre.

use super::*;
mod section;
pub use section::{ResidentConstitutiveSection, ResidentDifferenceSection, ResidentSourcePairs};
mod return_rest;
pub use return_rest::ConstitutiveReturnRest;

/// A member-law successor whose basis was formed in fresh resident material.  The predecessor
/// identity is checked again when the neighborhood publishes its joint successor.
pub(crate) struct PreparedConstitutiveFormation<'chart> {
    pub(crate) basis: ResidentSection<'chart>,
    predecessor_owner: Rc<()>,
    successor_owner: Rc<()>,
    predecessor_occurrences: u64,
    pub(crate) returned: ResidentConstitutiveReturn<'chart>,
}
impl<'c> PreparedConstitutiveFormation<'c> {
    /// Move staged material into one conditional realization; the continuing predecessor
    /// remains unchanged. No ecology is copied to make this executable material view.
    pub(crate) fn into_alternative(self)->(ResidentConstitutiveFibre<'c>,ResidentConstitutiveReturn<'c>){
        let material=ResidentConstitutiveFibre {
            surface:self.returned.surface,basis:self.basis,basis_owner:self.successor_owner,
            source_width:self.returned.source_width,target_width:self.returned.target_width,
            source_chart:self.returned.source_chart,occurrences:self.returned.occurrence,usable:true,
        };
        (material,self.returned)
    }
}

/// A local relation's receiver result. Only field-qualified queries have a field source;
/// a relation cut never stands in for an invented source occurrence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ConstitutiveDifferentialReading {
    pub field_source: Option<usize>,
    pub relation_cut: u64,
    pub status: NativeFieldReceiverStatus,
    pub first_complex: usize,
    pub pairs: usize,
    pub positive: u64,
    pub negative: u64,
    pub unresolved: u64,
    pub exact_zero: u64,
}

/// A borrowed exact current chart. Coordinates and the optional denominator remain on device.
#[derive(Clone, Copy)]
pub struct ResidentConstitutiveCurrent<'a, 'chart> {
    pub(crate) section: &'a ResidentSection<'chart>,
    pub(crate) offset: usize,
    pub(crate) width: usize,
    pub(crate) denominator: Option<usize>,
    pub(crate) disposition: Option<usize>,
}

impl<'a, 'chart> ResidentConstitutiveCurrent<'a, 'chart> {
    /// Exact numerator coordinates followed by one common denominator. Pointness and a positive
    /// denominator are checked on device when consumed; no numerical value is read here.
    pub fn rational(section: &'a ResidentSection<'chart>) -> Result<Self, ConstitutiveFibreError> {
        if section.rows() != 1 || section.width() < 2 || section.grain().0 != 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        Ok(Self {
            section,
            offset: 0,
            width: section.width() - 1,
            denominator: Some(section.width() - 1),
            disposition: None,
        })
    }
    /// A complete integer section, including a section produced by another native operation.
    /// The device checks pointness before admitting any source or receiving coordinate.
    pub fn integers(section: &'a ResidentSection<'chart>) -> Result<Self, ConstitutiveFibreError> {
        if section.rows() != 1 || section.width() == 0 || section.grain().0 != 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        Ok(Self {
            section,
            offset: 0,
            width: section.width(),
            denominator: None,
            disposition: None,
        })
    }
}

/// Immutable consequence of one operation, not a copy of the continuing relation.
pub struct ResidentConstitutiveReturn<'chart> {
    surface: &'chart ResidentSurface<'chart>,
    report: ResidentSection<'chart>,
    source_width: usize,
    target_width: usize,
    occurrence: u64,
    source_occurrence: Option<usize>,
    source_chart: ConstitutiveSourceChart,
}

impl<'chart> ResidentConstitutiveReturn<'chart> {
    pub(super) fn allocate(
        surface: &'chart ResidentSurface<'chart>,
        source_width: usize,
        target_width: usize,
        occurrence: u64,
        source_chart: ConstitutiveSourceChart,
    ) -> Result<Self, ConstitutiveFibreError> {
        let width = source_width
            .checked_add(target_width)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let report_width = target_width
            .checked_mul(target_width)
            .and_then(|n| n.checked_add(width.checked_add(4)?))
            .ok_or(ConstitutiveFibreError::Shape)?;
        Ok(Self {
            surface,
            report: surface.fresh_section(1, report_width, ResidentGrain(0))?,
            source_width,
            target_width,
            occurrence,
            source_occurrence: None,
            source_chart,
        })
    }
    pub(super) fn qualify_field_source(&mut self, source_occurrence: usize) {
        self.source_occurrence = Some(source_occurrence);
    }
    pub(crate) fn source_width(&self) -> usize {
        self.source_width
    }
    pub(super) fn report(&self) -> &ResidentSection<'chart> {
        &self.report
    }

    /// Supply this return to a point-current operation. Its unique-current hypothesis is checked
    /// on device at consumption, including the denominator and original receiver disposition.
    /// The return itself still carries the full plural/outside-domain face for inspection.
    pub fn current(&self) -> ResidentConstitutiveCurrent<'_, 'chart> {
        let width = self.source_width + self.target_width;
        ResidentConstitutiveCurrent {
            section: &self.report,
            offset: self.source_width,
            width: self.target_width,
            denominator: Some(width),
            disposition: Some(width + 1),
        }
    }

    pub fn occurrence(&self) -> u64 {
        self.occurrence
    }

    pub fn source_chart(&self) -> ConstitutiveSourceChart {
        self.source_chart
    }

    /// A receiver of the entire affine target fibre. A differential is fixed only when every
    /// vertical direction vanishes through it. This can return a sign even for a plural current;
    /// no particular member is selected. The receipt separates an actual field source from the
    /// contemporary relation cut; querying old standing never invents a new source occurrence.
    pub fn read_differential_pairs(
        &self,
        first_complex: usize,
        pairs: usize,
    ) -> Result<ConstitutiveDifferentialReading, ConstitutiveFibreError> {
        self.read_differential_pairs_guarded(first_complex, pairs, None)
    }

    pub(super) fn read_differential_pairs_guarded(
        &self,
        first_complex: usize,
        pairs: usize,
        coverage: Option<&ResidentSection<'chart>>,
    ) -> Result<ConstitutiveDifferentialReading, ConstitutiveFibreError> {
        let output = self.surface.fresh_section(1, 5, ResidentGrain(0))?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface.record_constitutive_differential(
                &lane,
                &self.report,
                self.source_width,
                self.target_width,
                first_complex,
                pairs,
                coverage,
                &output,
            )?;
        }
        passage.close(0, &output, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "{:?}",
                receipt.obstruction
            )));
        }
        let words = self.surface.read_out(&output)?;
        if words.iter().any(|(lo, hi)| lo != hi || *lo < 0) {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        Ok(ConstitutiveDifferentialReading {
            field_source: self.source_occurrence,
            relation_cut: self.occurrence,
            status: match words[4].0 {
                0 => NativeFieldReceiverStatus::Unique,
                1 => NativeFieldReceiverStatus::OutsideDomain,
                2 => NativeFieldReceiverStatus::Plural,
                _ => return Err(ConstitutiveFibreError::Uncertain),
            },
            first_complex,
            pairs,
            positive: words[0].0 as u64,
            negative: words[1].0 as u64,
            unresolved: words[2].0 as u64,
            exact_zero: words[3].0 as u64,
        })
    }

    /// Explicit cold observation of the original return. No live relation is consulted, so a
    /// later deposit cannot rewrite this earlier Preimage Fibre.
    pub fn inspect(&self) -> Result<ConstitutiveFibreReturn, ConstitutiveFibreError> {
        let words = self.surface.read_out(&self.report)?;
        let width = self.source_width + self.target_width;
        if words.iter().any(|(lo, hi)| lo != hi) || words[width].0 <= 0 {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let rational = |j: usize| Rat::new(words[j].0.into(), words[width].0.into());
        let particular = || (self.source_width..width).map(rational).collect();
        let predecessor_reading = match words[width + 1].0 {
            0 => ConstitutiveReading::Unique {
                current: particular(),
            },
            1 => ConstitutiveReading::OutsideDomain {
                source_remainder: (0..self.source_width).map(rational).collect(),
            },
            2 => ConstitutiveReading::Plural {
                particular: particular(),
                directions: words[width + 4..]
                    .chunks_exact(self.target_width)
                    .filter(|row| row.iter().any(|(v, _)| *v != 0))
                    .map(|row| {
                        row.iter()
                            .map(|(v, _)| Rat::from_integer((*v).into()))
                            .collect()
                    })
                    .collect(),
            },
            _ => return Err(ConstitutiveFibreError::Uncertain),
        };
        let formed_pivot = match words[width + 2].0 {
            -1 => None,
            p if p >= 0 && (p as usize) < width => Some(p as usize),
            _ => return Err(ConstitutiveFibreError::Uncertain),
        };
        let successor_rank =
            usize::try_from(words[width + 3].0).map_err(|_| ConstitutiveFibreError::Uncertain)?;
        if successor_rank > width {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        Ok(ConstitutiveFibreReturn {
            occurrence: self.occurrence,
            predecessor_reading,
            formed_pivot,
            successor_rank,
        })
    }
}

impl<'chart> ResidentConstitutiveFibre<'chart> {
    pub(crate) fn prepare_bilinear_contact(
        &mut self,
        source: ResidentConstitutiveCurrent<'_, 'chart>,
        condition: ResidentConstitutiveCurrent<'_, 'chart>,
        receiving: Option<ResidentConstitutiveCurrent<'_, 'chart>>,
    ) -> Result<PreparedConstitutiveFormation<'chart>, ConstitutiveFibreError> {
        if !self.usable {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let predecessor_owner = Rc::clone(&self.basis_owner);
        let predecessor_occurrences = self.occurrences;
        let staged_basis = self.surface.copy_section_device(&self.basis)?;
        let successor_owner = Rc::new(());
        let mut staged = Self {
            basis: staged_basis,
            basis_owner: Rc::clone(&successor_owner),
            surface: self.surface,
            source_width: self.source_width,
            target_width: self.target_width,
            source_chart: self.source_chart,
            occurrences: self.occurrences,
            usable: true,
        };
        match staged.advance_bilinear_contact(source, condition, receiving) {
            Ok(returned) => Ok(PreparedConstitutiveFormation {
                basis: staged.basis,
                predecessor_owner,
                successor_owner,
                predecessor_occurrences,
                returned,
            }),
            Err(error) => {
                // A device completion that cannot be classified leaves the live owner poisoned;
                // arithmetic refusal has already preserved the staged and live predecessors.
                if !staged.usable || matches!(error, ConstitutiveFibreError::Uncertain) {
                    self.usable = false;
                }
                Err(error)
            }
        }
    }

    pub(crate) fn can_commit_formation(
        &self,
        prepared: &PreparedConstitutiveFormation<'chart>,
    ) -> bool {
        self.usable
            && self.occurrences == prepared.predecessor_occurrences
            && Rc::ptr_eq(&self.basis_owner, &prepared.predecessor_owner)
    }

    pub(crate) fn publish_formation(
        &mut self,
        prepared: PreparedConstitutiveFormation<'chart>,
    ) -> ResidentConstitutiveReturn<'chart> {
        debug_assert!(self.can_commit_formation(&prepared));
        let old = std::mem::replace(&mut self.basis, prepared.basis);
        drop(old);
        self.basis_owner = prepared.successor_owner;
        self.occurrences = prepared.returned.occurrence;
        prepared.returned
    }

    pub(super) fn allocate_current_return(
        &self,
        occurrence: u64,
    ) -> Result<ResidentConstitutiveReturn<'chart>, ConstitutiveFibreError> {
        let width = self.source_width + self.target_width;
        let report_width = self
            .target_width
            .checked_mul(self.target_width)
            .and_then(|n| n.checked_add(width + 4))
            .ok_or(ConstitutiveFibreError::Shape)?;
        Ok(ResidentConstitutiveReturn {
            surface: self.surface,
            report: self
                .surface
                .fresh_section(1, report_width, ResidentGrain(0))?,
            source_width: self.source_width,
            target_width: self.target_width,
            occurrence,
            source_occurrence: None,
            source_chart: self.source_chart,
        })
    }
    /// Enact the existing relation law on resident rational operands. The receiving section is
    /// an actual observation, not a desired answer. Its absence reads the current local domain.
    /// Native arithmetic, disposition and the staged row all precede the continuing write.
    pub fn advance_resident(
        &mut self,
        source: ResidentConstitutiveCurrent<'_, 'chart>,
        receiving: Option<ResidentConstitutiveCurrent<'_, 'chart>>,
    ) -> Result<ResidentConstitutiveReturn<'chart>, ConstitutiveFibreError> {
        self.advance_contact(source, None, receiving)
    }

    /// One declared bilinear contact. The condition is a separately supplied current in its
    /// admitted chart, not an identifier or an answer-derived switch. Source, condition and all
    /// mixed complex products enter the same local relation on device. Its full returned fibre
    /// and the single continuing commit follow the ordinary relation law.
    pub fn advance_bilinear_contact(
        &mut self,
        source: ResidentConstitutiveCurrent<'_, 'chart>,
        condition: ResidentConstitutiveCurrent<'_, 'chart>,
        receiving: Option<ResidentConstitutiveCurrent<'_, 'chart>>,
    ) -> Result<ResidentConstitutiveReturn<'chart>, ConstitutiveFibreError> {
        self.advance_contact(source, Some(condition), receiving)
    }

    fn advance_contact(
        &mut self,
        source: ResidentConstitutiveCurrent<'_, 'chart>,
        condition: Option<ResidentConstitutiveCurrent<'_, 'chart>>,
        receiving: Option<ResidentConstitutiveCurrent<'_, 'chart>>,
    ) -> Result<ResidentConstitutiveReturn<'chart>, ConstitutiveFibreError> {
        if !self.usable {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let valid_source = match (self.source_chart, condition) {
            (ConstitutiveSourceChart::Linear, None) => source.width == self.source_width,
            (
                ConstitutiveSourceChart::BilinearContact {
                    source_complex,
                    condition_complex,
                },
                Some(c),
            ) => source.width == 2 * source_complex && c.width == 2 * condition_complex,
            _ => false,
        };
        if !valid_source || receiving.is_some_and(|v| v.width != self.target_width) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let next = self
            .occurrences
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let returned = self.allocate_current_return(next)?;
        let contact = condition
            .map(|_| {
                self.surface
                    .fresh_section(1, self.source_width + 1, ResidentGrain(0))
            })
            .transpose()?;
        let lineage = if contact.is_some() {
            vec![vec![], vec![0]]
        } else {
            vec![vec![]]
        };
        let mut passage = self.surface.begin_passage(&lineage)?;
        if let (Some(condition), Some(contact)) = (condition, contact.as_ref()) {
            {
                let lane = passage.open(0, &[])?;
                self.surface
                    .record_constitutive_bilinear_source(&lane, source, condition, contact)?;
            }
            passage.close(0, contact, 64)?;
        }
        let (lane_at, predecessors) = if contact.is_some() {
            (1, vec![0])
        } else {
            (0, vec![])
        };
        {
            let lane = passage.open(lane_at, &predecessors)?;
            let source = contact
                .as_ref()
                .map_or(source, |contact| ResidentConstitutiveCurrent {
                    section: contact,
                    offset: 0,
                    width: self.source_width,
                    denominator: Some(self.source_width),
                    disposition: None,
                });
            self.surface.record_constitutive_current(
                &lane,
                &mut self.basis,
                source,
                receiving,
                &returned.report,
            )?;
        }
        passage.close(lane_at, &returned.report, 64)?;
        let passage = passage.finish()?;
        self.usable = false;
        let reading = passage.launch()?;
        if !reading.obstruction.is_empty() {
            // This kernel validates all current apertures and arithmetic before the basis write.
            self.usable = true;
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "resident constitutive point-current passage: {:?}",
                reading.obstruction
            )));
        }
        self.occurrences = next;
        self.usable = true;
        Ok(returned)
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod contact_tests;
#[cfg(test)]
mod law_rest_tests;

mod neighborhood;
pub(crate) use neighborhood::ResidentNeighborhoodAlternative;
mod read;
pub use neighborhood::{
    GeneratorNeighborhoodRest, GeneratorNeighborhoodStep, NeighborhoodEvidence,
    NeighborhoodEvidenceRest, ResidentGeneratorNeighborhood,
};

mod preimage;
pub use preimage::{ConditionPreimageReading, ConditionPreimageRest, ResidentConditionPreimage};

mod condition_image;
mod image;
pub use condition_image::{ConditionCoverage, ConditionImageReading, ResidentConditionImage};
pub use image::{
    ConstitutiveImageReading, ConstitutiveImageReceiver, ResidentConstitutiveImage,
    ResidentConstitutiveRefinement,
};

mod condition_contact;
mod context_section;
pub use condition_contact::{
    AffineContactReading, ConditionContactMetric, ConditionContactReading, ConditionContactStatus,
    ConditionCurrentRest, PreparedConditionContact, ResidentAffineContact,
    ResidentConditionContact, ResidentConditionCurrent, ResidentConditionStanding,
};
pub use context_section::{ContextualSectionOrigin, ResidentContextualSection};

mod wave_relation;
pub use wave_relation::{
    NormalWaveRelationRest, ResidentWavePullback, ResidentWaveRelation, ResidentWaveSourceContact, WaveSourceReceiver,
};
