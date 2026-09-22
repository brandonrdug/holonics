//! Fixed-generator affine geometry action on the resident complex3 chart.
//!
//! The geometry chart is deliberately separate from the value chart consumed by
//! `NativePairParticipation`.  A source index may occur more than once; the
//! reverse path therefore gathers a local covector and delegates its join to
//! `scatter_phase_adjoint` rather than identifying the two charts.

use super::*;
use crate::ExactWavePhaseTransport;
use crate::resident_section::SLOT_WORDS;
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use relational_geometry::AffineMap3;
use std::rc::Rc;

pub const AFFINE_GEOMETRY_COMPONENTS: usize = 6;
pub const AFFINE_GEOMETRY_COEFFICIENTS: usize = 12;

/// Numerical enclosure law. The legacy coordinate-interval reading remains available
/// for exact reconstruction of older producing words; JointBall keeps the coupled metric.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeEnclosurePropagation {
    #[default]
    ComponentIntervals,
    JointBall,
}

pub struct NativeAffineGeometry<'c> {
    source: Rc<ResidentNormalEnclosureSection<'c>>,
    indices: ResidentSection<'c>,
    source_indices: Vec<usize>,
    coefficients: Rc<ResidentNormalEnclosureSection<'c>>,
    output: Rc<ResidentNormalEnclosureSection<'c>>,
    project: bool,
    enclosure: NativeEnclosurePropagation,
}

pub struct NativeAffineGeometryAdjoint<'c> {
    source: ResidentNormalEnclosureSection<'c>,
}

const REALIFICATION_ENCODE: u32 = 0;
const REALIFICATION_DECODE: u32 = 1;
const REALIFICATION_PROJECT_REAL: u32 = 2;

pub struct NativeRealification<'c> {
    input: Rc<ResidentNormalEnclosureSection<'c>>,
    output: Rc<ResidentNormalEnclosureSection<'c>>,
    mode: u32,
}

pub struct NativeRealificationAdjoint<'c> {
    source: ResidentNormalEnclosureSection<'c>,
}

impl<'c> ResidentNormalEnclosureSection<'c> {
    fn realification(
        self: Rc<Self>,
        mode: u32,
        output_components: usize,
    ) -> Result<NativeRealification<'c>, ConstitutiveFibreError> {
        let surface = self.resident_section().surface();
        let grain = self.grain();
        let rows = self.rows();
        let output_width = output_components
            .checked_add(1)
            .and_then(|value| value.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if rows == 0
            || rows > u32::MAX as usize
            || self.components() == 0
            || self.components() % 2 != 0
            || output_components == 0
            || output_components % 2 != 0
            || !(1..=120).contains(&grain.0)
            || rows.checked_mul(output_width).is_none()
            || rows.checked_mul(SLOT_WORDS / 2).is_none()
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let input_components = self.components();
        let valid_mode = match mode {
            REALIFICATION_ENCODE => input_components
                .checked_mul(2)
                .is_some_and(|value| value == output_components),
            REALIFICATION_DECODE => output_components
                .checked_mul(2)
                .is_some_and(|value| value == input_components),
            REALIFICATION_PROJECT_REAL => output_components == input_components,
            _ => false,
        };
        if !valid_mode {
            return Err(ConstitutiveFibreError::Shape);
        }
        let output = surface.fresh_section(rows, output_width, ResidentGrain(0))?;
        let flags = surface.fresh_section(rows, SLOT_WORDS / 2, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_realification(
                &lane,
                self.resident_section(),
                rows,
                input_components,
                output_components,
                mode,
                &output,
                &flags,
            )?;
            surface.collect_phase_status(&lane, &flags, rows)?;
        }
        passage.close(0, &output, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "realification: {:?}",
                receipt.obstruction
            )));
        }
        let output = Rc::new(Self::from_resident(
            surface,
            output,
            rows,
            output_components,
            grain,
        )?);
        Ok(NativeRealification {
            input: self,
            output,
            mode,
        })
    }

    /// Encode each real scalar of the complex chart as a native complex
    /// channel `(scalar,0)`, doubling the even component count.
    pub fn realify(self: Rc<Self>) -> Result<NativeRealification<'c>, ConstitutiveFibreError> {
        let components = self.components();
        let output_components = components
            .checked_mul(2)
            .ok_or(ConstitutiveFibreError::Shape)?;
        self.realification(REALIFICATION_ENCODE, output_components)
    }

    /// Decode an ambient realified chart by taking each native channel's real
    /// part. This is a projection for arbitrary ambient rows; only its image is
    /// an inverse of `realify`.
    pub fn decode_realification(
        self: Rc<Self>,
    ) -> Result<NativeRealification<'c>, ConstitutiveFibreError> {
        let components = self.components();
        if components % 2 != 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        self.realification(REALIFICATION_DECODE, components / 2)
    }

    /// Project every native complex channel onto its real face.
    pub fn project_real(self: Rc<Self>) -> Result<NativeRealification<'c>, ConstitutiveFibreError> {
        let components = self.components();
        self.realification(REALIFICATION_PROJECT_REAL, components)
    }

    /// Mount exact affine-map rows as certified dyadic coefficient balls.
    ///
    /// The twelve words in each row are `R00..R22,b0..b2`. Every rational
    /// endpoint is widened outward at `grain`, then represented by one centre
    /// and one row-wide L1 radius. The caller retains the original `AffineMap3`
    /// declarations; this upload preserves their exact source only through the
    /// certified packet and performs no rigid-map validation or floating-point
    /// conversion.
    pub fn affine_coefficients(
        surface: &'c ResidentSurface<'c>,
        maps: &[AffineMap3],
        grain: ResidentGrain,
    ) -> Result<Rc<Self>, ConstitutiveFibreError> {
        const ROW_WIDTH: usize = 2 * (AFFINE_GEOMETRY_COEFFICIENTS + 1);
        if maps.is_empty()
            || maps.len() > u32::MAX as usize
            || !(1..=120).contains(&grain.0)
            || maps.len().checked_mul(ROW_WIDTH).is_none()
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let minimum = -(BigInt::from(1_u8) << 127_usize);
        let maximum = (BigInt::from(1_u8) << 127_usize) - BigInt::from(1_u8);
        let scale = BigInt::from(1_u8) << grain.0 as usize;
        let scale = relational_geometry::Rat::from_integer(scale);
        let mut words = Vec::with_capacity(maps.len() * ROW_WIDTH);
        for map in maps {
            let coefficients: [&relational_geometry::Rat; AFFINE_GEOMETRY_COEFFICIENTS] = [
                &map.linear.rows[0][0],
                &map.linear.rows[0][1],
                &map.linear.rows[0][2],
                &map.linear.rows[1][0],
                &map.linear.rows[1][1],
                &map.linear.rows[1][2],
                &map.linear.rows[2][0],
                &map.linear.rows[2][1],
                &map.linear.rows[2][2],
                &map.translation.x,
                &map.translation.y,
                &map.translation.z,
            ];
            let mut centres = Vec::with_capacity(AFFINE_GEOMETRY_COEFFICIENTS);
            let mut radius = BigInt::from(0_u8);
            for coefficient in coefficients {
                let scaled = coefficient * &scale;
                let lower = scaled.floor().to_integer();
                let upper = scaled.ceil().to_integer();
                let span = &upper - &lower;
                let centre = &lower + (&span / BigInt::from(2_u8));
                // Since centre is the floor midpoint, upper-centre is the
                // larger one-sided error and is a valid coordinate bound.
                radius += &upper - &centre;
                centres.push(centre);
            }
            if centres.iter().any(|centre| {
                let lower = centre - &radius;
                let upper = centre + &radius;
                lower < minimum || upper > maximum
            }) {
                return Err(ConstitutiveFibreError::Shape);
            }
            let radius = radius.to_i128().ok_or(ConstitutiveFibreError::Shape)?;
            for centre in centres {
                let value = centre.to_i128().ok_or(ConstitutiveFibreError::Shape)?;
                words.extend([value as i64, (value >> 64) as i64].map(|word| (word, word)));
            }
            words.extend([radius as i64, (radius >> 64) as i64].map(|word| (word, word)));
        }
        let rest = ResidentSectionRest::found(maps.len(), ROW_WIDTH, ResidentGrain(0), 64, words)
            .map_err(|_| ConstitutiveFibreError::Shape)?;
        let section = surface
            .mount_section_rest(&rest)
            .map_err(ConstitutiveFibreError::from)?;
        Ok(Rc::new(Self::from_resident(
            surface,
            section,
            maps.len(),
            AFFINE_GEOMETRY_COEFFICIENTS,
            grain,
        )?))
    }

    /// Apply one fixed machine/arc cut.  The index section is mounted as an
    /// exact width-one packet and remains owned by the returned producing map.
    /// Coefficients are already resident enclosures at the source grain; this
    /// keeps non-dyadic rational maps and their certified radius in the packet.
    pub fn affine_geometry(
        self: Rc<Self>,
        source_indices: &[usize],
        coefficients: Rc<ResidentNormalEnclosureSection<'c>>,
        project: bool,
    ) -> Result<NativeAffineGeometry<'c>, ConstitutiveFibreError> {
        self.affine_geometry_with_enclosure(
            source_indices,
            coefficients,
            project,
            NativeEnclosurePropagation::ComponentIntervals,
        )
    }

    /// Affine transport with an explicit producing enclosure law.
    pub fn affine_geometry_with_enclosure(
        self: Rc<Self>,
        source_indices: &[usize],
        coefficients: Rc<ResidentNormalEnclosureSection<'c>>,
        project: bool,
        enclosure: NativeEnclosurePropagation,
    ) -> Result<NativeAffineGeometry<'c>, ConstitutiveFibreError> {
        let surface = self.resident_section().surface();
        let grain = self.grain();
        let rows = source_indices.len();
        if rows == 0
            || rows > u32::MAX as usize
            || rows
                .checked_mul(2 * (AFFINE_GEOMETRY_COMPONENTS + 1))
                .is_none()
            || rows.checked_mul(SLOT_WORDS / 2).is_none()
            || self.rows() > u32::MAX as usize
            || self.components() != AFFINE_GEOMETRY_COMPONENTS
            || coefficients.rows() != rows
            || coefficients.components() != AFFINE_GEOMETRY_COEFFICIENTS
            || coefficients.grain() != grain
            || !std::ptr::eq(coefficients.resident_section().surface(), surface)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let source_rows = self.rows();
        if source_indices.iter().any(|index| *index >= source_rows) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let values = source_indices
            .iter()
            .map(|index| {
                let value = i64::try_from(*index).map_err(|_| ConstitutiveFibreError::Shape)?;
                Ok((value, value))
            })
            .collect::<Result<Vec<_>, ConstitutiveFibreError>>()?;
        let indices = surface
            .mount_section_rest(
                &ResidentSectionRest::found(rows, 1, ResidentGrain(0), 64, values)
                    .map_err(|_| ConstitutiveFibreError::Shape)?,
            )
            .map_err(ConstitutiveFibreError::from)?;
        let output =
            surface.fresh_section(rows, 2 * (AFFINE_GEOMETRY_COMPONENTS + 1), ResidentGrain(0))?;
        let flags = surface.fresh_section(rows, SLOT_WORDS / 2, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_affine_geometry_forward(
                &lane,
                self.resident_section(),
                &indices,
                coefficients.resident_section(),
                rows,
                grain.0,
                project,
                enclosure == NativeEnclosurePropagation::JointBall,
                &output,
                &flags,
            )?;
            surface.collect_phase_status(&lane, &flags, rows)?;
        }
        passage.close(0, &output, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "affine geometry forward: {:?}",
                receipt.obstruction
            )));
        }
        let output = Rc::new(Self::from_resident(
            surface,
            output,
            rows,
            AFFINE_GEOMETRY_COMPONENTS,
            grain,
        )?);
        Ok(NativeAffineGeometry {
            source: self,
            indices,
            source_indices: source_indices.to_vec(),
            coefficients,
            output,
            project,
            enclosure,
        })
    }
}

impl<'c> NativeRealification<'c> {
    pub fn output(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.output
    }

    pub fn output_handle(&self) -> Rc<ResidentNormalEnclosureSection<'c>> {
        self.output.clone()
    }

    pub fn pull_back(
        &self,
        gy: &ResidentNormalEnclosureSection<'c>,
    ) -> Result<NativeRealificationAdjoint<'c>, ConstitutiveFibreError> {
        let surface = self.input.resident_section().surface();
        let rows = self.input.rows();
        let input_components = self.input.components();
        let output_components = self.output.components();
        let grain = self.input.grain();
        if gy.rows() != rows
            || gy.components() != output_components
            || gy.grain() != grain
            || !std::ptr::eq(gy.resident_section().surface(), surface)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let (mode, returned_components) = match self.mode {
            REALIFICATION_ENCODE => (REALIFICATION_DECODE, input_components),
            REALIFICATION_DECODE => (REALIFICATION_ENCODE, input_components),
            REALIFICATION_PROJECT_REAL => (REALIFICATION_PROJECT_REAL, input_components),
            _ => return Err(ConstitutiveFibreError::Shape),
        };
        let output_width = returned_components
            .checked_add(1)
            .and_then(|value| value.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let returned = surface.fresh_section(rows, output_width, ResidentGrain(0))?;
        let flags = surface.fresh_section(rows, SLOT_WORDS / 2, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_realification(
                &lane,
                gy.resident_section(),
                rows,
                output_components,
                returned_components,
                mode,
                &returned,
                &flags,
            )?;
            surface.collect_phase_status(&lane, &flags, rows)?;
        }
        passage.close(0, &returned, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "realification adjoint: {:?}",
                receipt.obstruction
            )));
        }
        Ok(NativeRealificationAdjoint {
            source: ResidentNormalEnclosureSection::from_resident(
                surface,
                returned,
                rows,
                returned_components,
                grain,
            )?,
        })
    }
}

impl<'c> NativeRealificationAdjoint<'c> {
    pub fn source(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.source
    }

    pub fn into_source(self) -> ResidentNormalEnclosureSection<'c> {
        self.source
    }
}

impl<'c> NativeAffineGeometry<'c> {
    pub fn output(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.output
    }

    pub fn output_handle(&self) -> Rc<ResidentNormalEnclosureSection<'c>> {
        self.output.clone()
    }

    pub fn coefficients(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.coefficients
    }

    pub fn pull_back(
        &self,
        gy: &ResidentNormalEnclosureSection<'c>,
    ) -> Result<NativeAffineGeometryAdjoint<'c>, ConstitutiveFibreError> {
        let surface = self.source.resident_section().surface();
        if gy.rows() != self.output.rows()
            || gy.components() != AFFINE_GEOMETRY_COMPONENTS
            || gy.grain() != self.source.grain()
            || !std::ptr::eq(gy.resident_section().surface(), surface)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let rows = self.output.rows();
        let gathered =
            surface.fresh_section(rows, 2 * (AFFINE_GEOMETRY_COMPONENTS + 1), ResidentGrain(0))?;
        let flags = surface.fresh_section(rows, SLOT_WORDS / 2, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_affine_geometry_adjoint(
                &lane,
                self.coefficients.resident_section(),
                gy.resident_section(),
                rows,
                self.source.grain().0,
                self.project,
                self.enclosure == NativeEnclosurePropagation::JointBall,
                &gathered,
                &flags,
            )?;
            surface.collect_phase_status(&lane, &flags, rows)?;
        }
        passage.close(0, &gathered, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "affine geometry adjoint: {:?}",
                receipt.obstruction
            )));
        }
        let gathered = ResidentNormalEnclosureSection::from_resident(
            surface,
            gathered,
            rows,
            AFFINE_GEOMETRY_COMPONENTS,
            self.source.grain(),
        )?;
        let phases = vec![ExactWavePhaseTransport::identity(); rows];
        let source =
            gathered.scatter_phase_adjoint(&self.source_indices, &phases, self.source.rows())?;
        Ok(NativeAffineGeometryAdjoint { source })
    }
}

impl<'c> NativeAffineGeometryAdjoint<'c> {
    pub fn source(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.source
    }

    pub fn into_source(self) -> ResidentNormalEnclosureSection<'c> {
        self.source
    }
}

#[cfg(test)]
mod tests;
