use super::*;
use crate::native_ecology::constitutive_fibre::normal_feature_state_words;
use crate::native_ecology::constitutive_fibre::{
    ResidentConstitutiveCurrent, ResidentNormalEnclosureView, ResidentNormalInput,
};
impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_normal_applied_condition(
        &self,
        lane: &Lane<'_, 'c>,
        state: &ResidentSection<'c>,
        source: ResidentNormalEnclosureView<'_, 'c>,
        condition: ResidentConstitutiveCurrent<'_, 'c>,
        targets: usize,
        joint: Option<(usize, ResidentNormalEnclosureView<'_, 'c>)>,
        identity: bool,
        out: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        if identity && (joint.is_some() || source.width != 2 * targets) {
            return Err(fail());
        }
        self.validate_normal_input(source.into(), source.grain.0)?;
        self.validate_normal_input(ResidentNormalInput::Point(condition), source.grain.0)?;
        let d = joint.map_or(source.width, |(d, _)| d);
        let tail = if joint.is_some() {
            source.width.checked_sub(d).ok_or_else(fail)?
        } else {
            0
        };
        let external = joint.map_or(source, |(_, external)| external);
        if joint.is_some() {
            self.validate_normal_input(external.into(), source.grain.0)?;
            if external.width != 2 * targets || d == 0 || d % 2 != 0 || tail % 2 != 0 {
                return Err(fail());
            }
        }
        let k = condition.width;
        let features = d
            .checked_mul(k / 2)
            .and_then(|v| v.checked_add(d)?.checked_add(k))
            .ok_or_else(fail)?;
        let words = normal_feature_state_words(features / 2, targets).ok_or_else(fail)?;
        let output_words = targets
            .checked_mul(2)
            .and_then(|v| v.checked_add(tail)?.checked_add(1)?.checked_mul(2))
            .ok_or_else(fail)?;
        if d == 0
            || k == 0
            || d % 2 != 0
            || k % 2 != 0
            || features > u32::MAX as usize
            || targets > u32::MAX as usize
            || !self.operative_shape(state, 1, words)
            || !self.operative_shape(out, 1, output_words)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(state.lo.device_ptr())
            .ptr(state.hi.device_ptr())
            .ptr(source.section.lo.device_ptr())
            .ptr(source.section.hi.device_ptr())
            .u32(source.offset as u32)
            .u32(d as u32)
            .u32(source.width as u32)
            .ptr(external.section.lo.device_ptr())
            .ptr(external.section.hi.device_ptr())
            .u32(external.offset as u32)
            .u32(if identity {
                2
            } else {
                u32::from(joint.is_some())
            })
            .ptr(condition.section.lo.device_ptr())
            .ptr(condition.section.hi.device_ptr())
            .u32(condition.offset as u32)
            .u32(condition.denominator.map_or(u32::MAX, |v| v as u32))
            .u32(condition.disposition.map_or(u32::MAX, |v| v as u32))
            .u32(k as u32)
            .u32(targets as u32)
            .u32(source.grain.0)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_applied_condition",
            1,
            1,
            0,
            &mut p,
            "normal-applied-condition",
        )
    }

    /// The same applied condition over a section of enclosure source rows, each with its own
    /// condition row. `identity` contracts `(I+A(h))` on the shared source rather than summing
    /// two enclosures of it, so a generated section re-enters as the next source at full radius.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_normal_applied_condition_rows(
        &self,
        lane: &Lane<'_, 'c>,
        state: &ResidentSection<'c>,
        source: &ResidentSection<'c>,
        condition: &ResidentSection<'c>,
        k: usize,
        condition_rational: bool,
        condition_enclosed: bool,
        rows: usize,
        d: usize,
        targets: usize,
        identity: bool,
        grain: u32,
        out: &ResidentSection<'c>,
        flags: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        let point = || ResidentRefusal::Declaration {
            operation: "normal-applied-condition-rows",
            what: "an exact-point condition row cannot carry an enclosure radius; \
                   supply the enclosed condition section"
                .into(),
        };
        let width = if identity {
            d
        } else {
            targets.checked_mul(2).ok_or_else(fail)?
        };
        let features = d
            .checked_mul(k / 2)
            .and_then(|v| v.checked_add(d)?.checked_add(k))
            .ok_or_else(fail)?;
        let words = normal_feature_state_words(features / 2, targets).ok_or_else(fail)?;
        let source_words = d
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        let condition_words = if condition_enclosed {
            k.checked_add(1)
                .and_then(|v| v.checked_mul(2))
                .ok_or_else(fail)?
        } else {
            k.checked_add(usize::from(condition_rational))
                .ok_or_else(fail)?
        };
        let output_words = width
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        // An enclosed condition carries a radius word, never a rational denominator; claiming
        // both would let a point port read an enclosure centre as an exact coordinate.
        if condition_enclosed && condition_rational {
            return Err(point());
        }
        let scratch = k
            .checked_mul(std::mem::size_of::<i128>())
            .and_then(|n| u32::try_from(n).ok())
            .filter(|n| *n <= self.declaration.max_sectiond_bytes)
            .ok_or_else(|| ResidentRefusal::Declaration {
                operation: "normal-applied-condition-rows",
                what: format!(
                    "a condition row of {k} coordinates exceeds the declared \
                     {} shared octets",
                    self.declaration.max_sectiond_bytes
                ),
            })?;
        if rows == 0
            || rows > u32::MAX as usize
            || d == 0
            || k == 0
            || d % 2 != 0
            || k % 2 != 0
            || targets == 0
            || !(1..=120).contains(&grain)
            || (identity && d != 2 * targets)
            || features > u32::MAX as usize
            || targets > u32::MAX as usize
            || condition.width > u32::MAX as usize
            || condition.rows != rows
            || condition.width != condition_words
            || condition.grain.0 != 0
            || !std::ptr::eq(condition.surface, self)
            || !self.operative_shape(state, 1, words)
            || !self.operative_shape(source, rows, source_words)
            || !self.operative_shape(out, rows, output_words)
            || !self.operative_shape(flags, rows, SLOT_WORDS / 2)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(state.lo.device_ptr())
            .ptr(state.hi.device_ptr())
            .ptr(source.lo.device_ptr())
            .ptr(source.hi.device_ptr())
            .u32(source.width as u32)
            .ptr(condition.lo.device_ptr())
            .ptr(condition.hi.device_ptr())
            .u32(condition.width as u32)
            .u32(u32::from(condition_enclosed))
            .u32(u32::from(condition_rational))
            .u32(rows as u32)
            .u32(d as u32)
            .u32(k as u32)
            .u32(targets as u32)
            .u32(u32::from(identity))
            .u32(grain)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(flags.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_applied_condition_rows",
            rows,
            1,
            scratch,
            &mut p,
            "normal-applied-condition-rows",
        )?;
        let mut collect = Params::new();
        collect
            .ptr(flags.lo.device_ptr())
            .u32(rows as u32)
            .ptr(lane.slot);
        self.record_blocks(
            lane,
            "section_enclosure_collect_row_status",
            rows,
            1,
            0,
            &mut collect,
            "normal-applied-condition-row-status",
        )
    }
}
