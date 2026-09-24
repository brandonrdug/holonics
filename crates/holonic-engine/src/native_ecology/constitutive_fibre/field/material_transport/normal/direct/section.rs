use super::enclosure::{decode_ball_words, decode_radius_word};
use super::*;
use crate::resident_section::SLOT_WORDS;
use std::rc::Rc;
mod affine_geometry;
mod composition;
pub use affine_geometry::{
    NativeAffineGeometry, NativeAffineGeometryAdjoint, NativeEnclosurePropagation,
    NativeRealification, NativeRealificationAdjoint,
};

/// One resident enclosure per source row, produced by one applied normal-material passage.
/// The complete section remains on the resident surface; row views borrow its packet and do not
/// expose a point current or a host-side copy.
pub struct ResidentNormalEnclosureSection<'c> {
    surface: &'c ResidentSurface<'c>,
    section: ResidentSection<'c>,
    rows: usize,
    width: usize,
    grain: ResidentGrain,
}

impl<'c> ResidentNormalEnclosureSection<'c> {
    /// Append the homogeneous complex coordinate on device, carrying each row's
    /// existing radius into the enlarged joint packet.
    pub fn append_homogeneous(&self) -> Result<Self, ConstitutiveFibreError> {
        let output =
            self.surface
                .fresh_section(self.rows, 2 * (self.width + 3), ResidentGrain(0))?;
        let mut pass = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            self.surface.record_enclosure_append_homogeneous(
                &lane,
                &self.section,
                self.rows,
                self.width,
                self.grain.0,
                &output,
            )?;
        }
        pass.close(0, &output, 64)?;
        let result = pass.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "append homogeneous enclosure: {:?}",
                result.obstruction
            )));
        }
        Self::from_resident(self.surface, output, self.rows, self.width + 2, self.grain)
    }

    pub fn from_points<'a>(
        source: ResidentConstitutiveSection<'a, 'c>,
        grain: ResidentGrain,
    ) -> Result<Self, ConstitutiveFibreError> {
        if source.rows() == 0
            || source.components() == 0
            || source.components() % 2 != 0
            || source.section.grain().0 != 0
            || !(1..=120).contains(&grain.0)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let width = source.components();
        let stride = width
            .checked_add(1)
            .and_then(|n| n.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let surface = source.section.surface();
        let output = surface.fresh_section(source.rows(), stride, ResidentGrain(0))?;
        let mut pass = surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            surface.record_normal_enclosure_section(&lane, source, grain, &output)?;
        }
        pass.close(0, &output, 64)?;
        let result = pass.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "normal enclosure section: {:?}",
                result.obstruction
            )));
        }
        Self::from_resident(surface, output, source.rows(), width, grain)
    }

    pub(crate) fn from_resident(
        surface: &'c ResidentSurface<'c>,
        section: ResidentSection<'c>,
        rows: usize,
        width: usize,
        grain: ResidentGrain,
    ) -> Result<Self, ConstitutiveFibreError> {
        if rows == 0
            || width == 0
            || width % 2 != 0
            || section.rows() != rows
            || section.width() != 2 * (width + 1)
            || !std::ptr::eq(section.surface(), surface)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        Ok(Self {
            surface,
            section,
            rows,
            width,
            grain,
        })
    }

    pub fn rows(&self) -> usize {
        self.rows
    }

    pub fn components(&self) -> usize {
        self.width
    }

    /// Inspect every row from one resident readout. Row views remain available for callers that
    /// need one row, while telemetry and cold receipts use this batch path to avoid rereading the
    /// entire section once per row.
    pub fn inspect_rows(&self) -> Result<Vec<NativeFieldCurrentBall>, ConstitutiveFibreError> {
        let stride = self
            .width
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if self.section.width() != stride || self.section.rows() != self.rows {
            return Err(ConstitutiveFibreError::Shape);
        }
        let words = self.surface.read_out(&self.section)?;
        (0..self.rows)
            .map(|row| {
                let offset = row
                    .checked_mul(stride)
                    .ok_or(ConstitutiveFibreError::Shape)?;
                decode_ball_words(&words, offset, self.width, self.grain)
            })
            .collect()
    }

    /// Inspect only the certified radius of every row from one resident readout.
    pub fn inspect_radii(&self) -> Result<Vec<holonics::geometry::Rat>, ConstitutiveFibreError> {
        let stride = self
            .width
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if self.section.width() != stride || self.section.rows() != self.rows {
            return Err(ConstitutiveFibreError::Shape);
        }
        let words = self.surface.read_out(&self.section)?;
        (0..self.rows)
            .map(|row| {
                let offset = row
                    .checked_mul(stride)
                    .ok_or(ConstitutiveFibreError::Shape)?;
                decode_radius_word(&words, offset, self.width, self.grain)
            })
            .collect()
    }

    pub fn grain(&self) -> ResidentGrain {
        self.grain
    }

    /// Durable cold packet for a complete row enclosure. Numeric hot paths stay
    /// resident; this is an explicit rest boundary for pending application words.
    pub fn rest(&self) -> Result<ResidentSectionRest, ConstitutiveFibreError> {
        Ok(self.surface.detach_section(&self.section, i64::BITS)?)
    }

    pub fn remount(
        surface: &'c ResidentSurface<'c>,
        rest: ResidentSectionRest,
        rows: usize,
        width: usize,
        grain: ResidentGrain,
    ) -> Result<Self, ConstitutiveFibreError> {
        let stride = width
            .checked_add(1)
            .and_then(|n| n.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if rows == 0 || width == 0 || width % 2 != 0 || !(1..=120).contains(&grain.0) {
            return Err(ConstitutiveFibreError::Shape);
        }
        crate::native_ecology::constitutive_fibre::circulation::rest::point_section(
            &rest, rows, stride,
        )?;
        for row in rest.intervals.chunks_exact(stride) {
            if wides(row)?[width] < 0 {
                return Err(ConstitutiveFibreError::Uncertain);
            }
        }
        let section = surface.mount_section_rest(&rest)?;
        Self::from_resident(surface, section, rows, width, grain)
    }

    /// Placement identity for composing another resident operation on this same surface.
    /// This does not read the current or expose its packet carrier.
    pub fn surface(&self) -> &'c ResidentSurface<'c> {
        self.surface
    }

    pub(crate) fn resident_section(&self) -> &ResidentSection<'c> {
        &self.section
    }

    pub fn row(
        &self,
        row: usize,
    ) -> Result<ResidentNormalEnclosureView<'_, 'c>, ConstitutiveFibreError> {
        if row >= self.rows {
            return Err(ConstitutiveFibreError::Shape);
        }
        Ok(ResidentNormalEnclosureView {
            surface: self.surface,
            section: &self.section,
            offset: row * self.section.width(),
            width: self.width,
            grain: self.grain,
        })
    }

    pub fn sum_same_shape(&self, other: &Self) -> Result<Self, ConstitutiveFibreError> {
        if self.rows != other.rows
            || self.width != other.width
            || self.grain != other.grain
            || !std::ptr::eq(self.surface, other.surface)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let stride = self
            .width
            .checked_add(1)
            .and_then(|n| n.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let output = self
            .surface
            .fresh_section(self.rows, stride, ResidentGrain(0))?;
        let mut pass = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            self.surface.record_normal_enclosure_sum_section(
                &lane,
                self.row(0)?,
                other.row(0)?,
                self.rows,
                &output,
            )?;
        }
        pass.close(0, &output, 64)?;
        let result = pass.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "normal enclosure section sum: {:?}",
                result.obstruction
            )));
        }
        Self::from_resident(self.surface, output, self.rows, self.width, self.grain)
    }

    pub fn restrict_components(
        &self,
        range: std::ops::Range<usize>,
    ) -> Result<Self, ConstitutiveFibreError> {
        let count = range
            .end
            .checked_sub(range.start)
            .ok_or(ConstitutiveFibreError::Shape)?;
        if count == 0 || count % 2 != 0 || range.start % 2 != 0 || range.end > self.width {
            return Err(ConstitutiveFibreError::Shape);
        }
        let output = self.surface.fresh_section(
            self.rows,
            count
                .checked_add(1)
                .and_then(|n| n.checked_mul(2))
                .ok_or(ConstitutiveFibreError::Shape)?,
            ResidentGrain(0),
        )?;
        let mut pass = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            self.surface.record_normal_enclosure_restrict_section(
                &lane,
                self.row(0)?,
                range.start,
                count,
                &output,
            )?;
        }
        pass.close(0, &output, 64)?;
        let result = pass.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "normal enclosure section restriction: {:?}",
                result.obstruction
            )));
        }
        Self::from_resident(self.surface, output, self.rows, count, self.grain)
    }

    pub fn flatten_components(
        &self,
        range: std::ops::Range<usize>,
    ) -> Result<ResidentNormalEnclosure<'c>, ConstitutiveFibreError> {
        let destinations: Vec<usize> = (0..self.rows).collect();
        self.scatter_components(range, &destinations, self.rows)
    }

    pub fn scatter_components(
        &self,
        range: std::ops::Range<usize>,
        destinations: &[usize],
        output_rows: usize,
    ) -> Result<ResidentNormalEnclosure<'c>, ConstitutiveFibreError> {
        let count = range
            .end
            .checked_sub(range.start)
            .ok_or(ConstitutiveFibreError::Shape)?;
        if count == 0
            || count % 2 != 0
            || range.start % 2 != 0
            || range.end > self.width
            || destinations.len() != self.rows
            || output_rows == 0
            || destinations.iter().any(|&d| d >= output_rows)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let mut seen = vec![false; output_rows];
        for &destination in destinations {
            if seen[destination] {
                return Err(ConstitutiveFibreError::Shape);
            }
            seen[destination] = true;
        }
        let map_values = destinations
            .iter()
            .map(|&d| {
                let d = i64::try_from(d).map_err(|_| ConstitutiveFibreError::Shape)?;
                Ok::<_, ConstitutiveFibreError>((d, d))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let map = self.surface.mount_section_rest(
            &ResidentSectionRest::found(destinations.len(), 1, ResidentGrain(0), 64, map_values)
                .map_err(|_| ConstitutiveFibreError::Shape)?,
        )?;
        let output_width = output_rows
            .checked_mul(count)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let output = self.surface.fresh_section(
            1,
            output_width
                .checked_add(1)
                .and_then(|n| n.checked_mul(2))
                .ok_or(ConstitutiveFibreError::Shape)?,
            ResidentGrain(0),
        )?;
        let mut pass = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            self.surface.record_normal_enclosure_scatter_section(
                &lane,
                self.row(0)?,
                range.start,
                count,
                &map,
                output_rows,
                &output,
            )?;
        }
        pass.close(0, &output, 64)?;
        let result = pass.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "normal enclosure section scatter: {:?}",
                result.obstruction
            )));
        }
        ResidentNormalEnclosure::from_resident(self.surface, output, output_width, self.grain)
    }

    /// Carry this generated section forward as the next source of the same conditioned
    /// reaction. `from_points` mounts exact point rows; this is its re-entry counterpart, and
    /// the radius each row already carries is transported by the law rather than discarded or
    /// silently read as a centre. `identity` returns `x + M·φ(x,c)` by contracting `(I+A(c))`
    /// on the shared source, which is what a refinement step composes.
    pub fn reapply_bilinear<'a>(
        &self,
        material: &ResidentNormalMaterialView<'c>,
        condition: ResidentConstitutiveSection<'a, 'c>,
        identity: bool,
    ) -> Result<Self, ConstitutiveFibreError> {
        material.read_applied_bilinear_enclosed_section(self, condition, identity)
    }

    /// The same re-entry when the condition of a row is itself an enclosure.
    pub fn reapply_bilinear_enclosed(
        &self,
        material: &ResidentNormalMaterialView<'c>,
        condition: &ResidentNormalEnclosureSection<'c>,
        identity: bool,
    ) -> Result<Self, ConstitutiveFibreError> {
        material.read_applied_bilinear_enclosed_pair(self, condition, identity)
    }
}

impl<'c> ResidentNormalMaterialView<'c> {
    /// Apply the retained map to an already-enclosed feature section entirely
    /// on the resident device. The centre and radius remain one joint packet.
    pub fn read_applied_enclosed_section(
        &self,
        features: &ResidentNormalEnclosureSection<'c>,
    ) -> Result<ResidentNormalEnclosureSection<'c>, ConstitutiveFibreError> {
        self.read_applied_enclosed_section_with_enclosure(
            features,
            NativeEnclosurePropagation::ComponentIntervals,
        )
    }
    pub fn read_applied_enclosed_section_with_enclosure(
        &self,
        features: &ResidentNormalEnclosureSection<'c>,
        enclosure: NativeEnclosurePropagation,
    ) -> Result<ResidentNormalEnclosureSection<'c>, ConstitutiveFibreError> {
        let source_complex = self
            .source_chart
            .complex_sources()
            .ok_or(ConstitutiveFibreError::Shape)?;
        if features.components() != 2 * source_complex
            || features.grain() != self.grain
            || !std::ptr::eq(features.resident_section().surface(), self.surface)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let rows = features.rows();
        let stride = self
            .targets
            .checked_mul(2)
            .and_then(|n| n.checked_add(1))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let output = self
            .surface
            .fresh_section(rows, 2 * stride, ResidentGrain(0))?;
        let work = self.surface.fresh_section(
            rows,
            self.targets
                .checked_mul(4)
                .ok_or(ConstitutiveFibreError::Shape)?,
            ResidentGrain(0),
        )?;
        let flags = self
            .surface
            .fresh_section(rows, SLOT_WORDS / 2, ResidentGrain(0))?;
        let mut pass = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            self.surface.record_normal_applied_enclosed_features(
                &lane,
                &self.state,
                features.resident_section(),
                rows,
                source_complex,
                self.targets,
                self.grain.0,
                enclosure == NativeEnclosurePropagation::JointBall,
                &output,
                &work,
                &flags,
            )?;
        }
        pass.close(0, &output, 64)?;
        let result = pass.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "applied enclosed normal section: {:?}",
                result.obstruction
            )));
        }
        ResidentNormalEnclosureSection::from_resident(
            self.surface,
            output,
            rows,
            2 * self.targets,
            self.grain,
        )
    }

    /// Apply the retained coefficient map to every row of one resident source section. The
    /// source section is validated as an exact point/rational packet and the output retains its
    /// complete per-row enclosure bounds without mutating the material.
    pub fn read_applied_section<'a>(
        &self,
        source: ResidentConstitutiveSection<'a, 'c>,
    ) -> Result<ResidentNormalEnclosureSection<'c>, ConstitutiveFibreError> {
        let source_complex = self
            .source_chart
            .complex_sources()
            .ok_or(ConstitutiveFibreError::Shape)?;
        let expected = source_complex
            .checked_mul(2)
            .ok_or(ConstitutiveFibreError::Shape)?;
        if source.rows() == 0
            || source.components() != expected
            || source.section.grain().0 != 0
            || !std::ptr::eq(source.section.surface(), self.surface)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let stride = self
            .targets
            .checked_mul(2)
            .and_then(|n| n.checked_add(1))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let output = self.surface.fresh_section(
            source.rows(),
            stride.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?,
            ResidentGrain(0),
        )?;
        let work = self.surface.fresh_section(
            1,
            feature_workspace_words(source_complex, self.targets)
                .ok_or(ConstitutiveFibreError::Shape)?,
            ResidentGrain(0),
        )?;
        let input = self.surface.fresh_section(
            1,
            source_complex
                .checked_mul(2)
                .and_then(|n| {
                    n.checked_add(1)?
                        .checked_mul(4)?
                        .checked_add(3 * self.targets)
                })
                .ok_or(ConstitutiveFibreError::Shape)?,
            ResidentGrain(0),
        )?;
        let mut pass = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            self.surface.record_normal_applied_material_section(
                &lane,
                &self.state,
                source,
                source_complex,
                self.targets,
                self.grain.0,
                &output,
                &work,
                &input,
            )?;
        }
        pass.close(0, &output, 64)?;
        let result = pass.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "applied normal section: {:?}",
                result.obstruction
            )));
        }
        Ok(ResidentNormalEnclosureSection {
            surface: self.surface,
            section: output,
            rows: source.rows(),
            width: self
                .targets
                .checked_mul(2)
                .ok_or(ConstitutiveFibreError::Shape)?,
            grain: self.grain,
        })
    }

    /// Form same-row `(source, condition, condition ⊗ source)` features, then apply the retained
    /// normal map in one resident section passage. Source and condition rows remain correlated.
    pub fn read_applied_bilinear_section<'a>(
        &self,
        source: ResidentConstitutiveSection<'a, 'c>,
        condition: ResidentConstitutiveSection<'a, 'c>,
    ) -> Result<ResidentNormalEnclosureSection<'c>, ConstitutiveFibreError> {
        if source.rows() == 0
            || source.rows() != condition.rows()
            || source.components() % 2 != 0
            || condition.components() % 2 != 0
            || !std::ptr::eq(source.section.surface(), self.surface)
            || !std::ptr::eq(condition.section.surface(), self.surface)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let joined = source.bilinear_features(self.surface, condition)?;
        self.read_applied_section(joined.features())
    }

    /// `M·φ(s,c)` over a section of source rows that are already enclosures, with exact
    /// rational point condition rows. Row by row this is the single-row
    /// [`ResidentNormalMaterialView::read_applied_bilinear`] (or `_identity` when `identity`
    /// is set), and at zero source radius it encloses `read_applied_bilinear_section`.
    pub fn read_applied_bilinear_enclosed_section<'a>(
        &self,
        source: &ResidentNormalEnclosureSection<'c>,
        condition: ResidentConstitutiveSection<'a, 'c>,
        identity: bool,
    ) -> Result<ResidentNormalEnclosureSection<'c>, ConstitutiveFibreError> {
        if condition.section.grain().0 != 0
            || !std::ptr::eq(condition.section.surface(), self.surface)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        self.applied_condition_rows(
            source,
            condition.section,
            condition.components(),
            condition.rational,
            false,
            condition.rows(),
            identity,
        )
    }

    /// The same law when the condition rows are themselves enclosures. Writing `s = x+ε` and
    /// `c = h+δ`, the reaction is `M·φ(x,h) + A(h)ε + L_x δ + Q(δ,ε)`, so the returned radius
    /// is `‖A(h)‖ρ_s + ‖L_x‖ρ_c + ‖Q‖ρ_sρ_c`. No enclosure centre is taken for a point.
    pub fn read_applied_bilinear_enclosed_pair(
        &self,
        source: &ResidentNormalEnclosureSection<'c>,
        condition: &ResidentNormalEnclosureSection<'c>,
        identity: bool,
    ) -> Result<ResidentNormalEnclosureSection<'c>, ConstitutiveFibreError> {
        if condition.grain() != self.grain || !std::ptr::eq(condition.surface, self.surface) {
            return Err(ConstitutiveFibreError::Shape);
        }
        self.applied_condition_rows(
            source,
            condition.resident_section(),
            condition.components(),
            false,
            true,
            condition.rows(),
            identity,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn applied_condition_rows(
        &self,
        source: &ResidentNormalEnclosureSection<'c>,
        condition: &ResidentSection<'c>,
        k: usize,
        condition_rational: bool,
        condition_enclosed: bool,
        condition_rows: usize,
        identity: bool,
    ) -> Result<ResidentNormalEnclosureSection<'c>, ConstitutiveFibreError> {
        let rows = source.rows();
        let d = source.components();
        let features = d
            .checked_mul(k / 2)
            .and_then(|v| v.checked_add(d)?.checked_add(k))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if rows == 0
            || rows != condition_rows
            || d == 0
            || k == 0
            || d % 2 != 0
            || k % 2 != 0
            || self.source_chart
                != (NormalSourceChart::Features {
                    source_complex: features / 2,
                })
            || source.grain() != self.grain
            || !std::ptr::eq(source.surface, self.surface)
            || (identity
                && d != self
                    .targets
                    .checked_mul(2)
                    .ok_or(ConstitutiveFibreError::Shape)?)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let width = if identity {
            d
        } else {
            self.targets
                .checked_mul(2)
                .ok_or(ConstitutiveFibreError::Shape)?
        };
        let output = self.surface.fresh_section(
            rows,
            width
                .checked_add(1)
                .and_then(|n| n.checked_mul(2))
                .ok_or(ConstitutiveFibreError::Shape)?,
            ResidentGrain(0),
        )?;
        let flags = self
            .surface
            .fresh_section(rows, SLOT_WORDS / 2, ResidentGrain(0))?;
        let mut pass = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            self.surface.record_normal_applied_condition_rows(
                &lane,
                &self.state,
                source.resident_section(),
                condition,
                k,
                condition_rational,
                condition_enclosed,
                rows,
                d,
                self.targets,
                identity,
                self.grain.0,
                &output,
                &flags,
            )?;
        }
        pass.close(0, &output, 64)?;
        let result = pass.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "applied conditional reaction section: {:?}",
                result.obstruction
            )));
        }
        ResidentNormalEnclosureSection::from_resident(self.surface, output, rows, width, self.grain)
    }
}

impl<'c> ResidentNormalMaterial<'c> {
    /// Stage one producing covector return on the resident device.  The current
    /// map is applied to the retained feature enclosure, the returned native
    /// covector is scaled by `2^-step_bits`, and the two packets are summed before
    /// the existing normal observation staging runs.  No coefficient or covector
    /// centre is read back to the host and `self` is unchanged on refusal.
    pub fn stage_covector_return(
        &self,
        features: &ResidentNormalEnclosureSection<'c>,
        covectors: &ResidentNormalEnclosureSection<'c>,
        step_bits: u32,
    ) -> Result<Self, ConstitutiveFibreError> {
        if features.rows() == 0
            || features.components()
                != self
                    .source_complex()
                    .checked_mul(2)
                    .ok_or(ConstitutiveFibreError::Shape)?
            || covectors.rows() != features.rows()
            || covectors.components()
                != self
                    .targets
                    .checked_mul(2)
                    .ok_or(ConstitutiveFibreError::Shape)?
            || features.grain() != self.grain
            || covectors.grain() != self.grain
            || !std::ptr::eq(features.surface, self.surface)
            || !std::ptr::eq(covectors.surface, self.surface)
            || step_bits > 120
        {
            return Err(ConstitutiveFibreError::Shape);
        }

        let current = self
            .retained_view()
            .read_applied_enclosed_section(features)?;
        let zero = ResidentNormalEnclosureSection::zeros(
            self.surface,
            covectors.rows(),
            covectors.components(),
            self.grain,
        )?;
        let held = vec![false; covectors.rows() * (covectors.components() / 2)];
        let scaled = covectors.held_refinement(&zero, &held, step_bits)?;
        let proxy = current.sum_same_shape(&scaled)?;
        self.stage_receive_enclosed_section(features, &proxy)
    }

    pub fn stage_receive_enclosed_section(
        &self,
        source: &ResidentNormalEnclosureSection<'c>,
        observed: &ResidentNormalEnclosureSection<'c>,
    ) -> Result<Self, ConstitutiveFibreError> {
        if source.rows() == 0
            || source.rows() != observed.rows()
            || source.components()
                != self
                    .source_complex()
                    .checked_mul(2)
                    .ok_or(ConstitutiveFibreError::Shape)?
            || observed.components()
                != self
                    .targets
                    .checked_mul(2)
                    .ok_or(ConstitutiveFibreError::Shape)?
            || source.grain() != self.grain
            || observed.grain() != self.grain
            || !std::ptr::eq(source.surface, self.surface)
            || !std::ptr::eq(observed.surface, self.surface)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let mut staged = Self {
            surface: self.surface,
            state: Rc::clone(&self.state),
            source_chart: self.source_chart,
            targets: self.targets,
            grain: self.grain,
            observations: self.observations,
            prior: self.prior.clone(),
        };
        let mut pairs = Vec::with_capacity(source.rows());
        for row in 0..source.rows() {
            pairs.push((source.row(row)?, observed.row(row)?));
        }
        staged.receive_many(&pairs)?;
        Ok(staged)
    }




}

/// The two complete response fields share actual immutable producing operator cuts. Input
/// sections remain borrowed comparison operands, never a population retained by the model.
pub struct ResidentNormalSectionReturn<'a, 'c> {
    surface: &'c ResidentSurface<'c>,
    prior: Rc<ResidentSection<'c>>,
    successor: Rc<ResidentSection<'c>>,
    source: ResidentConstitutiveSection<'a, 'c>,
    observed: ResidentConstitutiveSection<'a, 'c>,
    before: ResidentSection<'c>,
    after: ResidentSection<'c>,
    source_chart: NormalSourceChart,
    targets: usize,
    grain: ResidentGrain,
    prior_material: Option<NativeNormalPrior>,
    pub predecessor_observations: u64,
    pub successor_observations: u64,
}
impl<'a, 'c> ResidentNormalSectionReturn<'a, 'c> {
    pub fn source(&self) -> ResidentConstitutiveSection<'a, 'c> {
        self.source
    }
    pub fn observed(&self) -> ResidentConstitutiveSection<'a, 'c> {
        self.observed
    }
    pub fn rows(&self) -> usize {
        self.source.rows()
    }
    fn view<'r>(
        &'r self,
        section: &'r ResidentSection<'c>,
        row: usize,
    ) -> Result<ResidentNormalEnclosureView<'r, 'c>, ConstitutiveFibreError> {
        if row >= self.rows() {
            return Err(ConstitutiveFibreError::Shape);
        }
        Ok(ResidentNormalEnclosureView {
            surface: self.surface,
            section,
            offset: row * section.width(),
            width: 2 * self.targets,
            grain: self.grain,
        })
    }
    pub fn before(
        &self,
        row: usize,
    ) -> Result<ResidentNormalEnclosureView<'_, 'c>, ConstitutiveFibreError> {
        self.view(&self.before, row)
    }
    pub fn forward(
        &self,
        row: usize,
    ) -> Result<ResidentNormalEnclosureView<'_, 'c>, ConstitutiveFibreError> {
        self.view(&self.after, row)
    }
    pub fn inspect_before_operator(
        &self,
    ) -> Result<NormalConstitution, ConstitutiveFibreError> {
        expose_data_energy(
            decode_state_layout(
                &self.surface.detach_section(&self.prior, i64::BITS)?,
                self.source_chart.layout(self.targets)?,
                self.targets,
                self.grain.0,
            )?,
            self.prior_material.as_ref(),
        )
    }
    pub fn inspect_after_operator(
        &self,
    ) -> Result<NormalConstitution, ConstitutiveFibreError> {
        expose_data_energy(
            decode_state_layout(
                &self.surface.detach_section(&self.successor, i64::BITS)?,
                self.source_chart.layout(self.targets)?,
                self.targets,
                self.grain.0,
            )?,
            self.prior_material.as_ref(),
        )
    }
    /// Read the entire field once at the explicitly requested exterior receiver.
    pub fn inspect_forward(&self) -> Result<Vec<NativeFieldCurrentBall>, ConstitutiveFibreError> {
        let words = self.surface.read_out(&self.after)?;
        let scale = BigInt::one() << self.grain.0;
        words
            .chunks_exact(self.after.width())
            .map(|row| {
                let v = wides(row)?;
                let width = 2 * self.targets;
                if v[width] < 0 {
                    return Err(ConstitutiveFibreError::Uncertain);
                }
                Ok(NativeFieldCurrentBall {
                    center: v[..width]
                        .chunks_exact(2)
                        .map(|v| {
                            ExactComplexWaveCurrent::new(
                                Rat::new(v[0].into(), scale.clone()),
                                Rat::new(v[1].into(), scale.clone()),
                            )
                        })
                        .collect(),
                    radius: Rat::new(v[width].into(), scale.clone()),
                })
            })
            .collect()
    }
}
impl<'c> ResidentNormalMaterial<'c> {
    /// Integrate bounded observations into the same sufficient statistics and fit
    /// once. The endpoint equals admitted sequential receives at this chart/grain;
    /// this call does not expose intermediate fitted operators or retain input rows.
    pub fn receive_many(
        &mut self,
        pairs: &[(
            ResidentNormalEnclosureView<'_, 'c>,
            ResidentNormalEnclosureView<'_, 'c>,
        )],
    ) -> Result<(), ConstitutiveFibreError> {
        if pairs.is_empty() {
            return Ok(());
        }
        let observations = self
            .observations
            .checked_add(pairs.len() as u64)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let layout = self.source_chart.layout(self.targets)?;
        let table = self.surface.normal_enclosed_batch_table(
            pairs,
            self.source_complex(),
            self.targets,
            self.grain,
        )?;
        let next = self
            .surface
            .fresh_section(1, layout.state_words, ResidentGrain(0))?;
        let work = self
            .surface
            .fresh_section(1, layout.workspace_words, ResidentGrain(0))?;
        let input = self.surface.fresh_section(
            1,
            4 * (layout.source_components + 1) + 3 * self.targets,
            ResidentGrain(0),
        )?;
        let report = self
            .surface
            .fresh_section(1, layout.report_words, ResidentGrain(0))?;
        let mut p = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = p.open(0, &[])?;
            self.surface.record_normal_enclosed_batch(
                &lane,
                &self.state,
                &table,
                self.source_complex(),
                self.targets,
                self.grain,
                &next,
                &work,
                &input,
                &report,
            )?;
        }
        p.close(0, &next, 64)?;
        let r = p.finish()?.launch()?;
        if !r.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "normal enclosed batch: {:?}",
                r.obstruction
            )));
        }
        self.state = Rc::new(next);
        self.observations = observations;
        Ok(())
    }
    /// Integrate all supplied point observations into the same normal geometry, then fit once.
    /// The row population is a measured section aperture. It is not a native clock or new
    /// coefficient population. Any failure precedes publication of the complete successor.
    pub fn receive_section<'a>(
        &mut self,
        source: ResidentConstitutiveSection<'a, 'c>,
        observed: ResidentConstitutiveSection<'a, 'c>,
    ) -> Result<ResidentNormalSectionReturn<'a, 'c>, ConstitutiveFibreError> {
        let returned = self.prepare_section(source, observed)?;
        self.publish_section(&returned);
        Ok(returned)
    }
    pub(super) fn publish_section(&mut self, returned: &ResidentNormalSectionReturn<'_, 'c>) {
        self.state = Rc::clone(&returned.successor);
        self.observations = returned.successor_observations;
    }
    pub(super) fn prepare_section<'a>(
        &self,
        source: ResidentConstitutiveSection<'a, 'c>,
        observed: ResidentConstitutiveSection<'a, 'c>,
    ) -> Result<ResidentNormalSectionReturn<'a, 'c>, ConstitutiveFibreError> {
        let layout = self.source_chart.layout(self.targets)?;
        if source.rows() != observed.rows()
            || source.components() != layout.source_components
            || observed.components() != layout.target_components
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let count = self
            .observations
            .checked_add(source.rows() as u64)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let fresh = |width| self.surface.fresh_section(1, width, ResidentGrain(0));
        let next = fresh(layout.state_words)?;
        let before = self.surface.fresh_section(
            source.rows(),
            2 * (layout.target_components + 1),
            ResidentGrain(0),
        )?;
        let after = self
            .surface
            .fresh_section(source.rows(), before.width(), ResidentGrain(0))?;
        let work = fresh(layout.workspace_words)?;
        let input = fresh((layout.source_components + 1) * 4 + 3 * self.targets)?;
        let report = fresh(layout.report_words)?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface.record_normal_material_section(
                &lane,
                &self.state,
                source,
                observed,
                self.source_complex(),
                self.targets,
                self.grain.0,
                &next,
                &before,
                &after,
                &work,
                &input,
                &report,
            )?;
        }
        passage.close(0, &after, i64::BITS)?;
        let returned = passage.finish()?.launch()?;
        if !returned.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "normal section: {:?}",
                returned.obstruction
            )));
        }
        let predecessor_observations = self.observations;
        let successor = Rc::new(next);
        let prior = Rc::clone(&self.state);
        Ok(ResidentNormalSectionReturn {
            surface: self.surface,
            prior,
            successor,
            source,
            observed,
            before,
            after,
            source_chart: self.source_chart,
            targets: self.targets,
            grain: self.grain,
            prior_material: self.prior.clone(),
            predecessor_observations,
            successor_observations: count,
        })
    }
}

#[cfg(test)]
mod covector_return_tests {
    use super::*;
    use crate::embedding_fiber::ResidentReadout;

    #[test]
    #[ignore = "requires CUDA; resident normal proxy stages current·feature + 2^-step_bits·g without host arithmetic"]
    fn covector_return_stages_scalar_and_complex_proxy_without_live_mutation() {
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let packet = surface
            .mount_section_rest(
                &ResidentSectionRest::found(
                    1,
                    2,
                    ResidentGrain(0),
                    i64::BITS,
                    vec![(1, 1), (0, 0)],
                )
                .unwrap(),
            )
            .unwrap();
        let features = ResidentNormalEnclosureSection::from_points(
            ResidentConstitutiveSection::integers(&packet).unwrap(),
            ResidentGrain(16),
        )
        .unwrap();
        let covector_packet = surface
            .mount_section_rest(
                &ResidentSectionRest::found(
                    1,
                    2,
                    ResidentGrain(0),
                    i64::BITS,
                    vec![(1, 1), (1, 1)],
                )
                .unwrap(),
            )
            .unwrap();
        let covector = ResidentNormalEnclosureSection::from_points(
            ResidentConstitutiveSection::integers(&covector_packet).unwrap(),
            ResidentGrain(16),
        )
        .unwrap();
        let material =
            ResidentNormalMaterial::found_features(&surface, 1, 1, ResidentGrain(16)).unwrap();
        let staged = material
            .stage_covector_return(&features, &covector, 1)
            .unwrap();
        assert_eq!(
            material.observations(),
            0,
            "prepare must not mutate the live cut"
        );
        assert_eq!(staged.observations(), 1);
        let state = staged.inspect().unwrap();
        // f=1 and g=(1+i), sigma=1/2; H=2, B=(1+i)/2 and the normal reference
        // is (1+i)/4. The applied positive numerical proposal carries its actual defect.
        assert_eq!(
            state.source_normal[0][0],
            ExactComplexWaveCurrent::new(Rat::from_integer(2.into()), Rat::zero())
        );
        assert_eq!(
            state.cross_source[0][0],
            ExactComplexWaveCurrent::new(
                Rat::new(1.into(), 2.into()),
                Rat::new(1.into(), 2.into())
            )
        );
        let reference = ExactComplexWaveCurrent::new(
            Rat::new(1.into(), 4.into()),
            Rat::new(1.into(), 4.into()),
        );
        assert!(
            state.material.coefficients[0][0]
                .subtract(&reference)
                .norm_square()
                <= &state.material.radius * &state.material.radius
        );
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod applied_enclosed_features_tests {
    use super::*;
    use crate::embedding_fiber::ResidentReadout;

    #[test]
    #[ignore = "requires CUDA; three resident rows use one applied normal owner without host per-row transfers"]
    fn applied_enclosed_rows_use_one_owner_and_retain_row_order() {
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let prior = NativeNormalPrior::from_coefficients(vec![vec![ExactComplexWaveCurrent::new(
            Rat::from_integer(2.into()),
            Rat::zero(),
        )]])
        .unwrap();
        let material = ResidentNormalMaterial::found_features_with_prior(
            &surface,
            1,
            1,
            ResidentGrain(16),
            prior,
        )
        .unwrap();
        let raw = surface
            .mount_section_rest(
                &ResidentSectionRest::found(
                    3,
                    2,
                    ResidentGrain(0),
                    i64::BITS,
                    vec![(1, 1), (0, 0), (2, 2), (0, 0), (3, 3), (0, 0)],
                )
                .unwrap(),
            )
            .unwrap();
        let features = ResidentNormalEnclosureSection::from_points(
            ResidentConstitutiveSection::integers(&raw).unwrap(),
            ResidentGrain(16),
        )
        .unwrap();
        let reads = surface.census().section_read_outs;
        let applied = material
            .retained_view()
            .read_applied_enclosed_section(&features)
            .unwrap();
        assert_eq!(surface.census().section_read_outs, reads);
        let values = (0..3)
            .map(|row| {
                applied.row(row).unwrap().inspect().unwrap().center[0]
                    .real
                    .clone()
            })
            .collect::<Vec<_>>();
        assert_eq!(
            values,
            vec![
                Rat::from_integer(2.into()),
                Rat::from_integer(4.into()),
                Rat::from_integer(6.into())
            ]
        );
    }
}
