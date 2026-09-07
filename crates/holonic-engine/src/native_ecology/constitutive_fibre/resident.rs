//! Resident composition of the existing rational-linear constitutive relation.
//!
//! A returned rational current can enter another operation without a host numerical read.
//! The immutable return includes its original vertical fibre, even after later development.
//! A point-current consumer checks uniqueness on device; it never chooses from a plural fibre.

use super::*;

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
}

impl<'chart> ResidentConstitutiveReturn<'chart> {
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
    /// Enact the existing relation law on resident rational operands. The receiving section is
    /// an actual observation, not a desired answer. Its absence reads the current local domain.
    /// Native arithmetic, disposition and the staged row all precede the continuing write.
    pub fn advance_resident(
        &mut self,
        source: ResidentConstitutiveCurrent<'_, 'chart>,
        receiving: Option<ResidentConstitutiveCurrent<'_, 'chart>>,
    ) -> Result<ResidentConstitutiveReturn<'chart>, ConstitutiveFibreError> {
        if !self.usable {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        if source.width != self.source_width
            || receiving.is_some_and(|v| v.width != self.target_width)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let next = self
            .occurrences
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let width = self.source_width + self.target_width;
        let report_width = self
            .target_width
            .checked_mul(self.target_width)
            .and_then(|n| n.checked_add(width + 4))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let report = self
            .surface
            .fresh_section(1, report_width, ResidentGrain(0))?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface.record_constitutive_current(
                &lane,
                &mut self.basis,
                source,
                receiving,
                &report,
            )?;
        }
        passage.close(0, &report, 64)?;
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
        Ok(ResidentConstitutiveReturn {
            surface: self.surface,
            report,
            source_width: self.source_width,
            target_width: self.target_width,
            occurrence: next,
        })
    }
}

#[cfg(test)]
mod tests;
