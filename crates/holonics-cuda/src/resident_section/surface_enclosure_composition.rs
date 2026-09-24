use super::*;

/// Packet-level restrictions of existing enclosure algebra; all shapes are checked below.
pub(crate) enum EnclosureComposition<'a, 'c> {
    Gather {
        input: &'a ResidentSection<'c>,
        map: &'a ResidentSection<'c>,
        components: usize,
        output_components: usize,
    },
    GatherAdjoint {
        input: &'a ResidentSection<'c>,
        offsets: &'a ResidentSection<'c>,
        entries: &'a ResidentSection<'c>,
        components: usize,
    },
    Concatenate {
        table: &'a ResidentSection<'c>,
        source_count: usize,
        source_width: usize,
    },
    Refine {
        generated: &'a ResidentSection<'c>,
        seed: &'a ResidentSection<'c>,
        mask: &'a ResidentSection<'c>,
        components: usize,
        step_bits: u32,
    },
    /// `realified`: the power-neutral chart `s ⊕ c ⊕ (c_r s)_r` over each real coordinate
    /// `c_r` of `c`, width `d + k + d·k`; otherwise the complex product, `d + k + d·k/2`.
    Features {
        source: &'a ResidentSection<'c>,
        condition: &'a ResidentSection<'c>,
        d: usize,
        k: usize,
        grain: u32,
        realified: bool,
    },
    FeaturesAdjoint {
        source: &'a ResidentSection<'c>,
        condition: &'a ResidentSection<'c>,
        covector: &'a ResidentSection<'c>,
        d: usize,
        k: usize,
        grain: u32,
        realified: bool,
    },
    NormalAdjoint {
        state: &'a ResidentSection<'c>,
        covector: &'a ResidentSection<'c>,
        sources: usize,
        targets: usize,
        grain: u32,
        joint: bool,
    },
    /// The implicit-midpoint (Cayley) reaction step of the power-neutral law
    /// (`kernels/enclosure_cayley.cuh`): outputs the step `y` and the midpoint `(p + y)/2`.
    /// `condition` is absent exactly when `k = 0`. `certified` is the host's exact passivity
    /// certificate of the linear self-relation; the kernel refuses without it.
    CayleyReaction {
        state: &'a ResidentSection<'c>,
        drive: &'a ResidentSection<'c>,
        condition: Option<&'a ResidentSection<'c>>,
        n: usize,
        k: usize,
        grain: u32,
        certified: bool,
    },
    /// Its adjoint: outputs `u = A⁻ᴴ g` and the drive covector `2u − g`.
    CayleyAdjoint {
        state: &'a ResidentSection<'c>,
        condition: Option<&'a ResidentSection<'c>>,
        covector: &'a ResidentSection<'c>,
        n: usize,
        k: usize,
        grain: u32,
        certified: bool,
    },
}
impl<'c> ResidentSurface<'c> {
    /// `(2n, state words)` of a power-neutral reaction material with `n` complex targets and `k`
    /// real contrast coordinates (`F = n + k/2 + n·k` complex sources); `n ≤ 8` (the kernel's
    /// per-row solve extent).
    fn cayley_extent(&self, n: usize, k: usize) -> Option<(usize, usize)> {
        if n == 0 || n > 8 || k % 2 != 0 || k >= u32::MAX as usize {
            return None;
        }
        let f = n.checked_mul(k)?.checked_add(n)?.checked_add(k / 2)?;
        let words = crate::native_ecology::constitutive_fibre::normal_feature_state_words(f, n)?;
        Some((2 * n, words))
    }
    pub(crate) fn record_enclosure_composition(
        &self,
        lane: &Lane<'_, 'c>,
        operation: EnclosureComposition<'_, 'c>,
        outputs: &[&ResidentSection<'c>],
        flags: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "enclosure-composition",
            what: "incompatible enclosure or map extent".into(),
        };
        let out = *outputs.first().ok_or_else(fail)?;
        let rows = out.rows();
        let ball = |s: &ResidentSection<'c>, r: usize, d: usize| {
            d > 0
                && d % 2 == 0
                && d < u32::MAX as usize
                && r > 0
                && r <= u32::MAX as usize
                && d.checked_add(1)
                    .and_then(|n| n.checked_mul(2))
                    .is_some_and(|w| self.operative_shape(s, r, w))
        };
        let same_rows = |a: &ResidentSection<'c>, b: &ResidentSection<'c>| a.rows() == b.rows();
        if rows == 0
            || rows > u32::MAX as usize
            || !self.operative_shape(flags, rows, SLOT_WORDS / 2)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        let kernel = match operation {
            EnclosureComposition::Gather {
                input,
                map,
                components: d,
                output_components: od,
            } => {
                if outputs.len() != 1
                    || !ball(input, input.rows(), d)
                    || !ball(out, rows, od)
                    || !self.operative_shape(map, rows, 4)
                {
                    return Err(fail());
                }
                p.ptr(input.lo.device_ptr())
                    .ptr(input.hi.device_ptr())
                    .ptr(map.lo.device_ptr())
                    .ptr(map.hi.device_ptr())
                    .u32(input.rows() as u32)
                    .u32(rows as u32)
                    .u32(d as u32)
                    .u32(od as u32);
                "section_enclosure_gather_phase"
            }
            EnclosureComposition::GatherAdjoint {
                input,
                offsets,
                entries,
                components: d,
            } => {
                if outputs.len() != 1
                    || !ball(input, input.rows(), d)
                    || !ball(out, rows, d)
                    || rows
                        .checked_add(1)
                        .is_none_or(|n| !self.operative_shape(offsets, n, 1))
                    || !self.operative_shape(entries, input.rows(), 4)
                {
                    return Err(fail());
                }
                p.ptr(input.lo.device_ptr())
                    .ptr(input.hi.device_ptr())
                    .ptr(offsets.lo.device_ptr())
                    .ptr(offsets.hi.device_ptr())
                    .ptr(entries.lo.device_ptr())
                    .ptr(entries.hi.device_ptr())
                    .u32(input.rows() as u32)
                    .u32(rows as u32)
                    .u32(d as u32);
                "section_enclosure_scatter_phase_adjoint"
            }
            EnclosureComposition::Concatenate {
                table,
                source_count,
                source_width,
            } => {
                if outputs.len() != 1
                    || source_count == 0
                    || source_count > u32::MAX as usize
                    || source_width == 0
                    || source_width > u32::MAX as usize
                    || !self.operative_shape(table, source_count, 4)
                    || !self.operative_shape(out, rows, source_width)
                {
                    return Err(fail());
                }
                p.ptr(table.lo.device_ptr())
                    .ptr(table.hi.device_ptr())
                    .u32(source_count as u32)
                    .u32(source_width as u32)
                    .u32(rows as u32);
                "section_enclosure_concatenate_rows"
            }
            EnclosureComposition::Refine {
                generated,
                seed,
                mask,
                components: d,
                step_bits,
            } => {
                if outputs.len() != 1
                    || step_bits > 120
                    || !ball(generated, rows, d)
                    || !ball(seed, rows, d)
                    || !ball(out, rows, d)
                    || !self.operative_shape(mask, rows, d / 2)
                {
                    return Err(fail());
                }
                p.ptr(generated.lo.device_ptr())
                    .ptr(generated.hi.device_ptr())
                    .ptr(seed.lo.device_ptr())
                    .ptr(seed.hi.device_ptr())
                    .ptr(mask.lo.device_ptr())
                    .ptr(mask.hi.device_ptr())
                    .u32(rows as u32)
                    .u32(d as u32)
                    .u32(step_bits);
                "section_enclosure_refine_rows"
            }
            EnclosureComposition::Features {
                source,
                condition,
                d,
                k,
                grain,
                realified,
            } => {
                let f = d
                    .checked_mul(if realified { k } else { k / 2 })
                    .and_then(|n| n.checked_add(d)?.checked_add(k))
                    .ok_or_else(fail)?;
                if outputs.len() != 1
                    || !(1..=120).contains(&grain)
                    || !same_rows(source, condition)
                    || !ball(source, rows, d)
                    || !ball(condition, rows, k)
                    || !ball(out, rows, f)
                {
                    return Err(fail());
                }
                p.ptr(source.lo.device_ptr())
                    .ptr(source.hi.device_ptr())
                    .ptr(condition.lo.device_ptr())
                    .ptr(condition.hi.device_ptr())
                    .u32(rows as u32)
                    .u32(d as u32)
                    .u32(k as u32)
                    .u32(grain)
                    .u32(u32::from(realified));
                "section_enclosure_bilinear_features"
            }
            EnclosureComposition::FeaturesAdjoint {
                source,
                condition,
                covector,
                d,
                k,
                grain,
                realified,
            } => {
                let f = d
                    .checked_mul(if realified { k } else { k / 2 })
                    .and_then(|n| n.checked_add(d)?.checked_add(k))
                    .ok_or_else(fail)?;
                if outputs.len() != 2
                    || !(1..=120).contains(&grain)
                    || !ball(source, rows, d)
                    || !ball(condition, rows, k)
                    || !ball(covector, rows, f)
                    || !ball(out, rows, d)
                    || !ball(outputs[1], rows, k)
                {
                    return Err(fail());
                }
                p.ptr(source.lo.device_ptr())
                    .ptr(source.hi.device_ptr())
                    .ptr(condition.lo.device_ptr())
                    .ptr(condition.hi.device_ptr())
                    .ptr(covector.lo.device_ptr())
                    .ptr(covector.hi.device_ptr())
                    .u32(rows as u32)
                    .u32(d as u32)
                    .u32(k as u32)
                    .u32(grain)
                    .u32(u32::from(realified));
                "section_enclosure_bilinear_adjoint"
            }
            EnclosureComposition::NormalAdjoint {
                state,
                covector,
                sources,
                targets,
                grain,
                joint,
            } => {
                let words = crate::native_ecology::constitutive_fibre::normal_feature_state_words(
                    sources, targets,
                )
                .ok_or_else(fail)?;
                let d = sources.checked_mul(2).ok_or_else(fail)?;
                let t = targets.checked_mul(2).ok_or_else(fail)?;
                if outputs.len() != 1
                    || !(1..=120).contains(&grain)
                    || !self.operative_shape(state, 1, words)
                    || !ball(covector, rows, t)
                    || !ball(out, rows, d)
                {
                    return Err(fail());
                }
                p.ptr(state.lo.device_ptr())
                    .ptr(state.hi.device_ptr())
                    .ptr(covector.lo.device_ptr())
                    .ptr(covector.hi.device_ptr())
                    .u32(rows as u32)
                    .u32(sources as u32)
                    .u32(targets as u32)
                    .u32(grain)
                    .u32(u32::from(joint));
                "section_normal_enclosed_adjoint"
            }
            EnclosureComposition::CayleyReaction {
                state,
                drive,
                condition,
                n,
                k,
                grain,
                certified,
            } => {
                let (d, words) = self.cayley_extent(n, k).ok_or_else(fail)?;
                if outputs.len() != 2
                    || !(1..=120).contains(&grain)
                    || !self.operative_shape(state, 1, words)
                    || !ball(drive, rows, d)
                    || condition.is_some() != (k > 0)
                    || condition.is_some_and(|c| !ball(c, rows, k))
                    || !ball(out, rows, d)
                    || !ball(outputs[1], rows, d)
                {
                    return Err(fail());
                }
                let c = condition.unwrap_or(drive);
                p.ptr(state.lo.device_ptr())
                    .ptr(state.hi.device_ptr())
                    .ptr(drive.lo.device_ptr())
                    .ptr(drive.hi.device_ptr())
                    .ptr(c.lo.device_ptr())
                    .ptr(c.hi.device_ptr())
                    .u32(rows as u32)
                    .u32(n as u32)
                    .u32(k as u32)
                    .u32(grain)
                    .u32(u32::from(certified));
                "section_enclosure_cayley_reaction"
            }
            EnclosureComposition::CayleyAdjoint {
                state,
                condition,
                covector,
                n,
                k,
                grain,
                certified,
            } => {
                let (d, words) = self.cayley_extent(n, k).ok_or_else(fail)?;
                if outputs.len() != 2
                    || !(1..=120).contains(&grain)
                    || !self.operative_shape(state, 1, words)
                    || !ball(covector, rows, d)
                    || condition.is_some() != (k > 0)
                    || condition.is_some_and(|c| !ball(c, rows, k))
                    || !ball(out, rows, d)
                    || !ball(outputs[1], rows, d)
                {
                    return Err(fail());
                }
                let c = condition.unwrap_or(covector);
                p.ptr(state.lo.device_ptr())
                    .ptr(state.hi.device_ptr())
                    .ptr(c.lo.device_ptr())
                    .ptr(c.hi.device_ptr())
                    .ptr(covector.lo.device_ptr())
                    .ptr(covector.hi.device_ptr())
                    .u32(rows as u32)
                    .u32(n as u32)
                    .u32(k as u32)
                    .u32(grain)
                    .u32(u32::from(certified));
                "section_enclosure_cayley_adjoint"
            }
        };
        for output in outputs {
            p.ptr(output.lo.device_ptr()).ptr(output.hi.device_ptr());
        }
        p.ptr(flags.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(lane, kernel, rows, 1, 0, &mut p, "enclosure-composition")?;
        let mut joined = Params::new();
        joined
            .ptr(flags.lo.device_ptr())
            .u32(rows as u32)
            .ptr(lane.slot);
        self.record_blocks(
            lane,
            "section_enclosure_collect_row_status",
            rows,
            1,
            0,
            &mut joined,
            "enclosure-row-obstruction-union",
        )
    }
}
