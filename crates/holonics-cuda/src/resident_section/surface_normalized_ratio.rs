//! Binders for the complex receiving potential's phase face and the Holon ratio's logarithmic
//! covector (`kernels/field_normalized_receiver.cuh`). Both read the operands the normalized
//! receiver already owns; neither introduces a second softmax.
use super::*;

impl<'chart> ResidentSurface<'chart> {
    fn normalized_ratio_ball_words(nodes: usize) -> Option<usize> {
        nodes
            .checked_mul(2)
            .and_then(|n| n.checked_add(1))
            .and_then(|n| n.checked_mul(2))
    }

    /// `phi = Im s / 2` over every row of a complex potential section.
    pub(crate) fn record_rows_normalized_phase(
        &self,
        lane: &Lane<'_, 'chart>,
        potential: &ResidentSection<'chart>,
        rows: usize,
        nodes: usize,
        grain: u32,
        phase: &ResidentSection<'chart>,
        flags: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "rows-normalized-phase",
            what: "incompatible receiving phase chart".into(),
        };
        let ball_words = Self::normalized_ratio_ball_words(nodes).ok_or_else(fail)?;
        if rows == 0
            || rows > u32::MAX as usize
            || nodes == 0
            || nodes > u32::MAX as usize / 20
            || !(1..=120).contains(&grain)
            || potential.rows != rows
            || potential.width != ball_words
            || phase.rows != rows
            || phase.width != ball_words
            || flags.rows != rows
            || flags.width != SLOT_WORDS / 2
            || [potential, phase, flags]
                .iter()
                .any(|s| s.grain.0 != 0 || !std::ptr::eq(s.surface, self))
        {
            return Err(fail());
        }
        let mut params = Params::new();
        params
            .ptr(potential.lo.device_ptr())
            .ptr(potential.hi.device_ptr())
            .u32(rows as u32)
            .u32(nodes as u32)
            .u32(grain)
            .ptr(phase.lo.device_ptr())
            .ptr(phase.hi.device_ptr())
            .ptr(flags.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_rows_normalized_phase",
            rows,
            self.declaration.warp_size.max(1),
            0,
            &mut params,
            "rows-normalized-phase",
        )
    }

    /// `(q - p) + i (1/2) q (phi^T - phi^H + 2 pi n)` over every row of a compared face report.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_rows_ratio_covector(
        &self,
        lane: &Lane<'_, 'chart>,
        report: &ResidentSection<'chart>,
        produced: &ResidentSection<'chart>,
        target: &ResidentSection<'chart>,
        branch: &ResidentSection<'chart>,
        rows: usize,
        nodes: usize,
        grain: u32,
        covector: &ResidentSection<'chart>,
        flags: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "rows-ratio-covector",
            what: "incompatible ratio covector chart".into(),
        };
        let ball_words = Self::normalized_ratio_ball_words(nodes).ok_or_else(fail)?;
        let report_words = nodes.checked_mul(20).ok_or_else(fail)?;
        if rows == 0
            || rows > u32::MAX as usize
            || nodes == 0
            || nodes > u32::MAX as usize / 20
            || !(1..=120).contains(&grain)
            || report.rows != rows
            || report.width != report_words
            || covector.rows != rows
            || covector.width != ball_words
            || produced.rows != rows
            || produced.width != ball_words
            || target.rows != rows
            || target.width != ball_words
            || branch.rows != rows
            || branch.width != 6
            || flags.rows != rows
            || flags.width != SLOT_WORDS / 2
            || [report, produced, target, branch, covector, flags]
                .iter()
                .any(|s| s.grain.0 != 0 || !std::ptr::eq(s.surface, self))
        {
            return Err(fail());
        }
        let mut params = Params::new();
        params
            .ptr(report.lo.device_ptr())
            .ptr(produced.lo.device_ptr())
            .ptr(produced.hi.device_ptr())
            .ptr(target.lo.device_ptr())
            .ptr(target.hi.device_ptr())
            .ptr(branch.lo.device_ptr())
            .ptr(branch.hi.device_ptr())
            .u32(rows as u32)
            .u32(nodes as u32)
            .u32(grain)
            .ptr(covector.lo.device_ptr())
            .ptr(covector.hi.device_ptr())
            .ptr(flags.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_rows_ratio_covector",
            rows,
            self.declaration.warp_size.max(1),
            0,
            &mut params,
            "rows-ratio-covector",
        )
    }
}
