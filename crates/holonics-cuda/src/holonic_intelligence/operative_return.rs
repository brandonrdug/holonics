//! The reconciled morphology law of the recurrent operator: the emitted face meets its next
//! occurrence, and the return deposits a factorized overlay on the cross-section it crossed.
//!
//! When a continuing occurrence enters (the previous context followed by at least one more
//! address), the retained terminal emission of the previous cycle is compared, row by row, with
//! the address that actually followed it. The differential of the normalized exponential receiver
//! returns through the terminal reactions (`scale · tanh · scale`) onto the tied cross-section as
//! `ΔW = −η · Dᵀ X`, carried as the additive factorized overlay `u · v` (`u = [V, rank]`,
//! `v = [rank, H]`) that the next tiled contraction applies beside the resident base. Rows the
//! differential does not touch are unchanged: the support is the causal cone of the return.
//!
//! Formal owners composed: `HolonicRecurrentEcology.FiniteRecurrentOperation.advanceMorphology`
//! (the signature: morphology, the entering occurrence, the presented and reacted carriers),
//! `HolonicCultivationCharts.GradientProposal` and `FactorizedLinearOverlay`,
//! `NativeMorphologyVariant.LocalCausalConeCultivation`, and the normalized exponential receiver of
//! `HolonicAdjointNormalization`. No world verdict, reward, label, status, or caller-supplied
//! factor enters: the only exterior data are the declared apertures, reported in every deposit.

use crate::DeviceBuffer;
use serde::{Deserialize, Serialize};

use super::NativeOverlayRest;

use crate::{
    embedding_fiber::MountedReadout,
    resident_section::{
        PassageBuilder, ResidentEndpoint, ResidentGrain, ResidentRefusal, ResidentSection, ResidentSurface,
        SeriesAperture,
    },
};

/// The declared apparatus apertures of the return. `learning_shift` is `k` in `η = 2^-k`; it enters
/// only as the exponent of the deposit readout. `series_terms` is the certified exponential's
/// aperture. Neither is derived from the material and both are reported in the deposit.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeReturnAperture {
    pub learning_shift: u32,
    pub series_terms: u32,
}

/// The testimony of one deposit, carried in the trace of the operation that enacted it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeMorphologyDeposit {
    /// The coefficient population deposited on.
    pub population: u32,
    pub rank: usize,
    pub cross_section_rows: usize,
    pub cross_section_width: usize,
    pub learning_shift: u32,
    pub series_terms: u32,
    pub u_exponent: i32,
    pub v_exponent: i32,
    pub u_octaves: u32,
    pub v_octaves: u32,
    /// The grain coarsening of each factor, derived from the carrier budget of the consuming
    /// factorized contraction so the overlay can be applied beside the base; reported, never chosen.
    pub u_shift: u32,
    pub v_shift: u32,
    pub differential_widest_interval: u64,
    pub next_occurrences: Vec<u32>,
}

/// One factorized overlay atom retained by the successor ecology: sealed resident words.
pub(super) struct OverlayAtom<'chart> {
    u: ResidentEndpoint<'chart>,
    v: ResidentEndpoint<'chart>,
    rank: usize,
    u_exponent: i32,
    v_exponent: i32,
    u_octaves: u32,
    v_octaves: u32,
}

impl<'chart> OverlayAtom<'chart> {
    pub(super) fn detach(&self, surface: &ResidentSurface<'chart>) -> Result<NativeOverlayRest, ResidentRefusal> {
        let rest = NativeOverlayRest { rows: self.u.rows(), width: self.v.width(), rank: self.rank,
            u: surface.detach_endpoint(&self.u)?, v: surface.detach_endpoint(&self.v)?,
            u_exponent: self.u_exponent, v_exponent: self.v_exponent,
            u_octaves: self.u_octaves, v_octaves: self.v_octaves };
        rest.validate()?;
        Ok(rest)
    }

    pub(super) fn remount(surface: &'chart ResidentSurface<'chart>, rest: &NativeOverlayRest) -> Result<Self, ResidentRefusal> {
        rest.validate()?;
        Ok(Self { u: surface.mount_endpoint_rest(rest.rows, rest.rank, &rest.u)?,
            v: surface.mount_endpoint_rest(rest.rank, rest.width, &rest.v)?, rank: rest.rank,
            u_exponent: rest.u_exponent, v_exponent: rest.v_exponent,
            u_octaves: rest.u_octaves, v_octaves: rest.v_octaves })
    }
    pub(super) fn rank(&self) -> usize {
        self.rank
    }

    /// Borrow the two resident coefficient factors without copying the held morphology.
    /// The forward uses `U(Vx)`; its return crosses these same factors in reverse order.
    pub(super) fn readouts(
        &self,
        surface: &'chart ResidentSurface<'chart>,
    ) -> (MountedReadout<'chart>, MountedReadout<'chart>) {
        (
            MountedReadout::borrowed(surface.readout(), self.u.lo_device_ptr(), self.u.rows(), self.rank, self.u_octaves, self.u_exponent),
            MountedReadout::borrowed(surface.readout(), self.v.lo_device_ptr(), self.rank, self.v.width(), self.v_octaves, self.v_exponent),
        )
    }
}

/// The carriers the return reads: the emission and reacted tiles of the terminal branch and the
/// carrier presented to the tied contraction.
pub(super) struct ReturnMaterial<'a, 'chart> {
    pub emission: &'a [ResidentSection<'chart>],
    pub reacted: &'a [ResidentSection<'chart>],
    pub presented: &'a ResidentSection<'chart>,
    pub presented_octaves: u32,
    pub rows: usize,
    pub width: usize,
    pub grain: ResidentGrain,
}

/// The next occurrence of every emitted row, if `entering` continues `previous`: row `j` emitted
/// after `previous[..=j]` and is met by `entering[j + 1]`. An occurrence that does not continue
/// the emitted line has no comparison and returns nothing.
pub(super) fn continuation_next_occurrences(previous: &[u32], entering: &[u32]) -> Option<Vec<u32>> {
    if previous.is_empty()
        || entering.len() <= previous.len()
        || entering[..previous.len()] != *previous
    {
        return None;
    }
    Some(entering[1..=previous.len()].to_vec())
}

struct CountedOctets<'chart> {
    surface: &'chart ResidentSurface<'chart>,
    buffer: DeviceBuffer<u8>,
    octets: usize,
}

impl<'chart> CountedOctets<'chart> {
    fn upload(
        surface: &'chart ResidentSurface<'chart>,
        bytes: &[u8],
    ) -> Result<Self, ResidentRefusal> {
        let buffer = surface.alloc_octets(bytes.len().max(1))?;
        buffer.copy_from_slice(bytes)?;
        Ok(Self {
            surface,
            buffer,
            octets: bytes.len().max(1),
        })
    }
    fn device_ptr(&self) -> u64 {
        self.buffer.device_ptr()
    }
}

impl Drop for CountedOctets<'_> {
    fn drop(&mut self) {
        self.surface.released_octets(self.octets as u64);
    }
}

/// The factor grains of a deposit, derived from the carrier budget of the consuming factorized
/// contraction: its stages are admitted in causal order without crediting a negative exponent, so
/// the presented octaves, the inner reduction, the two directed hands, the rank join, and a margin
/// of ten octaves for the next cycle's wider input are fixed, and what remains is split between
/// the two factors.  Returns `(u_shift, v_shift)`.
pub(super) fn factor_shifts(
    presented_octaves: u32,
    inner: usize,
    rank: usize,
    differential_octaves: u32,
) -> Result<(u32, u32), ResidentRefusal> {
    let ceil_log2 = |n: usize| n.max(1).next_power_of_two().ilog2();
    let fixed = presented_octaves
        .saturating_add(ceil_log2(inner))
        .saturating_add(2)
        .saturating_add(ceil_log2(rank))
        .saturating_add(10);
    let available = ResidentSurface::carrier_octaves()
        .checked_sub(fixed)
        .filter(|available| *available >= 8)
        .ok_or_else(|| ResidentRefusal::Declaration {
            operation: "deposit",
            what: format!(
                "the carrier admits no overlay beside a presented carrier of {presented_octaves} octaves"
            ),
        })?;
    let v_target = available / 2;
    let u_target = available - v_target;
    Ok((
        differential_octaves.saturating_sub(u_target),
        presented_octaves.saturating_sub(v_target),
    ))
}

/// The material of a deposit on one cross-section: the differential that returned to its output
/// and the carrier it was presented, at one grain.
pub(super) struct DepositMaterial<'a, 'chart> {
    pub differential: &'a ResidentSection<'chart>,
    pub differential_octaves: u32,
    pub presented: &'a ResidentSection<'chart>,
    pub presented_octaves: u32,
    pub grain: ResidentGrain,
}

/// Identity-admittance specialization of an ALREADY admitted HNP0 comparison. The numerical
/// passage does not establish that two fields should agree: an additive junction's derivative
/// alone supplies neither an observation target nor a learning law. Source duality is the
/// declared coefficient-coordinate pairing; no fabricated all-ones tensor is needed.
pub(super) fn enact_identity_admittance_contact<'chart>(
    surface: &'chart ResidentSurface<'chart>,
    presented: &ResidentSection<'chart>,
    presented_octaves: u32,
    transported: &ResidentSection<'chart>,
    transported_octaves: u32,
    arrived: &ResidentSection<'chart>,
    arrived_octaves: u32,
    aperture: NativeReturnAperture,
) -> Result<Option<(OverlayAtom<'chart>, NativeMorphologyDeposit)>, ResidentRefusal> {
    let refuse = |what: &str| ResidentRefusal::Declaration {
        operation: "identity-admittance-return", what: what.to_owned(),
    };
    if presented.rows() == 0 || presented.width() == 0 || transported.width() == 0
        || transported.rows() != presented.rows() || arrived.rows() != transported.rows()
        || arrived.width() != transported.width() || arrived.grain() != transported.grain()
        || presented.grain() != transported.grain()
    {
        return Err(refuse("the actual junction inputs do not share the declared carrier charts"));
    }
    let Some(differential) = native_section_difference(surface, transported, transported_octaves,
        arrived, arrived_octaves)? else { return Ok(None) };
    deposit_from_material(surface, DepositMaterial {
        differential: &differential.section, differential_octaves: differential.octaves,
        presented, presented_octaves, grain: presented.grain(),
    }, aperture).map(Some)
}

/// The receiver differential before returning through any intervening native reactions.
pub(super) fn native_section_difference<'chart>(
    surface: &'chart ResidentSurface<'chart>,
    transported: &ResidentSection<'chart>, transported_octaves: u32,
    arrived: &ResidentSection<'chart>, arrived_octaves: u32,
) -> Result<Option<ReturnedDifferential<'chart>>, ResidentRefusal> {
    let refuse = |what: &str| ResidentRefusal::Declaration {
        operation: "native-section-difference", what: what.to_owned(),
    };
    if transported.rows() == 0 || transported.width() == 0
        || arrived.rows() != transported.rows() || arrived.width() != transported.width()
        || arrived.grain() != transported.grain()
    {
        return Err(refuse("the two native arrivals do not share the target chart"));
    }
    let negative = crate::resident_section::DyadicEnclosure { lo: -1, hi: -1, grain: 0 };
    let negate_shape = surface.shape_scale(arrived.rows(), arrived.width(), arrived_octaves, negative)?;
    let difference_shape = surface.shape_re_entry(
        arrived.rows(), arrived.width(), transported_octaves, negate_shape.needed,
    )?;
    let negated = surface.fresh_section(arrived.rows(), arrived.width(), arrived.grain())?;
    let difference = surface.fresh_section(arrived.rows(), arrived.width(), arrived.grain())?;
    let mut passage = surface.begin_passage(&[vec![], vec![0]])?;
    {
        let lane = passage.open(0, &[])?;
        surface.record_scale(&lane, arrived, negative, &negated)?;
    }
    passage.close(0, &negated, negate_shape.needed)?;
    {
        let lane = passage.open(1, &[0])?;
        surface.record_re_entry(&lane, transported, &negated, &difference)?;
    }
    passage.close(1, &difference, difference_shape.needed)?;
    let reading = passage.finish()?.launch()?;
    if !reading.obstruction.is_empty() {
        return Err(refuse("the joined current returned a resident obstruction"));
    }
    // A zero maximum bit width certifies BOTH endpoints at EVERY coordinate are zero.
    // This is exact zero transport, not a magnitude threshold or a semantic importance score.
    if reading.slots[1].max_octave == 0 {
        return Ok(None);
    }
    Ok(Some(ReturnedDifferential { section: difference, octaves: reading.slots[1].max_octave }))
}

/// Deposit one overlay atom `u · v` with `u = −η · dᵀ` and `v = x`: one passage of three
/// occurrences — the transposed seal of the differential, the carry or coarsening of the
/// presented carrier, and its midpoint seal.
pub(super) fn deposit_from_material<'chart>(
    surface: &'chart ResidentSurface<'chart>,
    material: DepositMaterial<'_, 'chart>,
    aperture: NativeReturnAperture,
) -> Result<(OverlayAtom<'chart>, NativeMorphologyDeposit), ResidentRefusal> {
    let refuse = |what: String| ResidentRefusal::Declaration {
        operation: "deposit",
        what,
    };
    let rows = material.differential.rows();
    if rows == 0
        || material.presented.rows() != rows
        || material.differential.grain() != material.grain
        || material.presented.grain() != material.grain
    {
        return Err(refuse("the differential and presented carriers disagree".to_owned()));
    }
    let out_rows = material.differential.width();
    let inner = material.presented.width();
    let (u_shift, v_shift) =
        factor_shifts(material.presented_octaves, inner, rows, material.differential_octaves)?;
    let seal_shape = surface.shape_transpose_seal(rows, out_rows, material.differential_octaves)?;
    let v_scale = crate::resident_section::DyadicEnclosure {
        lo: 1,
        hi: 1,
        grain: v_shift,
    };
    let carry_shape = if v_shift == 0 {
        surface.shape_carry(rows, inner, material.presented_octaves)?
    } else {
        surface.shape_scale(rows, inner, material.presented_octaves, v_scale)?
    };
    let u = surface.fresh_section(out_rows, rows, material.grain)?;
    let v = surface.fresh_section(rows, inner, material.grain)?;
    let mut builder: PassageBuilder<'chart> = surface.begin_passage(&[vec![], vec![], vec![1]])?;
    {
        let lane = builder.open(0, &[])?;
        surface.record_transpose_seal(&lane, material.differential, u_shift, &u)?;
    }
    builder.close(0, &u, seal_shape.needed)?;
    {
        let lane = builder.open(1, &[])?;
        if v_shift == 0 {
            surface.record_carry(&lane, material.presented, &v)?;
        } else {
            surface.record_scale(&lane, material.presented, v_scale, &v)?;
        }
    }
    builder.close(1, &v, carry_shape.needed)?;
    {
        let lane = builder.open(2, &[1])?;
        surface.record_midpoint_seal(&lane, &v, carry_shape.needed)?;
    }
    builder.close_fused(2)?;
    let reading = builder.finish()?.launch()?;
    if !reading.obstruction.is_empty() {
        return Err(refuse(format!(
            "the deposit refused with flags {:#x}",
            reading.obstruction.joined_flags()
        )));
    }
    let u_octaves = reading.slots.first().map(|slot| slot.max_octave.max(1)).unwrap_or(1);
    let v_octaves = reading.slots.get(1).map(|slot| slot.max_octave.max(1)).unwrap_or(1);
    let grain = i32::try_from(material.grain.0).map_err(|_| refuse("the grain overflowed".to_owned()))?;
    let shift = i32::try_from(aperture.learning_shift)
        .map_err(|_| refuse("the learning shift overflowed".to_owned()))?;
    let u_exponent = grain
        .checked_add(shift)
        .and_then(i32::checked_neg)
        .and_then(|exponent| exponent.checked_add(i32::try_from(u_shift).ok()?))
        .ok_or_else(|| refuse("the deposit exponent overflowed".to_owned()))?;
    let v_exponent = i32::try_from(v_shift)
        .ok()
        .and_then(|shift| shift.checked_sub(grain))
        .ok_or_else(|| refuse("the presented exponent overflowed".to_owned()))?;
    let deposit = NativeMorphologyDeposit {
        population: u32::MAX,
        rank: rows,
        cross_section_rows: out_rows,
        cross_section_width: inner,
        learning_shift: aperture.learning_shift,
        series_terms: aperture.series_terms,
        u_exponent,
        v_exponent,
        u_octaves,
        v_octaves,
        u_shift,
        v_shift,
        differential_widest_interval: reading.slots.first().map(|slot| slot.max_width).unwrap_or(0),
        next_occurrences: Vec::new(),
    };
    Ok((
        OverlayAtom {
            u: u.into_lower_endpoint(),
            v: v.into_lower_endpoint(),
            rank: rows,
            u_exponent,
            v_exponent,
            u_octaves,
            v_octaves,
        },
        deposit,
    ))
}

/// The returned differential at the tied contraction's output, for the return through the body.
pub(super) struct ReturnedDifferential<'chart> {
    pub section: ResidentSection<'chart>,
    pub octaves: u32,
}

/// Move an already-declared dyadic factor before a linear pullback. The ideal adjoint commutes
/// with this factor. The finite-grain passage encloses any division remainder instead of clipping
/// a large unscaled intermediate; callers must not apply the same factor again at deposition.
pub(super) fn scale_contact_differential<'chart>(
    surface: &'chart ResidentSurface<'chart>, differential: ReturnedDifferential<'chart>, shift: u32,
) -> Result<(ReturnedDifferential<'chart>, Option<u64>), ResidentRefusal> {
    // None means no new scaling receiver ran; it does not claim the existing enclosure is a point.
    if shift == 0 { return Ok((differential, None)); }
    if i32::try_from(shift).is_err() {
        return Err(ResidentRefusal::Declaration { operation: "contact-current-scale", what: "dyadic exponent outside the chart".to_owned() });
    }
    let scale = crate::resident_section::DyadicEnclosure { lo: 1, hi: 1, grain: shift };
    let input = &differential.section;
    let shape = surface.shape_scale(input.rows(), input.width(), differential.octaves, scale)?;
    let output = surface.fresh_section(input.rows(), input.width(), input.grain())?;
    let mut passage = surface.begin_passage(&[vec![]])?;
    {
        let lane = passage.open(0, &[])?;
        surface.record_scale(&lane, input, scale, &output)?;
    }
    passage.close(0, &output, shape.needed)?;
    let reading = passage.finish()?.launch()?;
    if !reading.obstruction.is_empty() {
        return Err(ResidentRefusal::Declaration { operation: "contact-current-scale", what: "the dyadic current scaling was obstructed".to_owned() });
    }
    Ok((ReturnedDifferential { section: output, octaves: reading.slots[0].max_octave.max(1) }, Some(reading.slots[0].max_width)))
}

/// The tile table of the terminal face: `tiles[4t..4t+4] = e_lo, e_hi, t_lo, t_hi`, uploaded once.
fn terminal_tile_table<'chart>(
    surface: &'chart ResidentSurface<'chart>,
    material: &ReturnMaterial<'_, 'chart>,
) -> Result<(CountedOctets<'chart>, usize), ResidentRefusal> {
    let refuse = |what: String| ResidentRefusal::Declaration {
        operation: "receiver-return",
        what,
    };
    let tile_count = material.emission.len();
    if tile_count == 0
        || material.reacted.len() != tile_count
        || material.presented.rows() != material.rows
    {
        return Err(refuse(
            "the emission, reacted, and presented populations disagree".to_owned(),
        ));
    }
    let tile_width = material.emission[0].width();
    let mut addresses: Vec<u8> = Vec::with_capacity(tile_count * 4 * 8);
    for (emission, reacted) in material.emission.iter().zip(material.reacted) {
        if emission.rows() != material.rows
            || reacted.rows() != material.rows
            || emission.width() != tile_width
            || reacted.width() != tile_width
            || emission.grain() != material.grain
            || reacted.grain() != material.grain
        {
            return Err(refuse("the terminal tiles are not one uniform tiled face".to_owned()));
        }
        for address in [
            emission.lo_device_ptr(),
            emission.hi_device_ptr(),
            reacted.lo_device_ptr(),
            reacted.hi_device_ptr(),
        ] {
            addresses.extend_from_slice(&address.to_le_bytes());
        }
    }
    if tile_count * tile_width != material.width {
        return Err(refuse("the tiles do not cover the emitted face exactly".to_owned()));
    }
    Ok((CountedOctets::upload(surface, &addresses)?, tile_width))
}

/// The receiver differential alone, without a deposit: the emitted face meets `next` row by row
/// and `p − [o = next]` returns through the terminal reactions onto the tied contraction's
/// output.  The dissection's excitation.
pub(super) fn receiver_differential<'chart>(
    surface: &'chart ResidentSurface<'chart>,
    material: ReturnMaterial<'_, 'chart>,
    next: &[u32],
    terms: SeriesAperture,
) -> Result<ReturnedDifferential<'chart>, ResidentRefusal> {
    if next.len() != material.rows {
        return Err(ResidentRefusal::Declaration {
            operation: "receiver-return",
            what: "the next-occurrence population disagrees with the rows".to_owned(),
        });
    }
    let (tiles, tile_width) = terminal_tile_table(surface, &material)?;
    let mut next_bytes: Vec<u8> = Vec::with_capacity(next.len() * 4);
    for address in next {
        next_bytes.extend_from_slice(&address.to_le_bytes());
    }
    let next_resident = CountedOctets::upload(surface, &next_bytes)?;
    let return_shape =
        surface.shape_receiver_return(material.rows, material.width, tile_width, material.grain, terms)?;
    let u = surface.fresh_section(material.width, material.rows, material.grain)?;
    let differential = surface.fresh_section(material.rows, material.width, material.grain)?;
    let mut builder: PassageBuilder<'chart> = surface.begin_passage(&[vec![]])?;
    {
        let lane = builder.open(0, &[])?;
        surface.record_receiver_return(
            &lane,
            tiles.device_ptr(),
            (material.width / tile_width) as u32,
            tile_width as u32,
            material.rows as u32,
            material.width as u32,
            next_resident.device_ptr(),
            material.grain,
            terms,
            0,
            &return_shape,
            &u,
            &differential,
        )?;
    }
    builder.close(0, &u, return_shape.needed)?;
    let reading = builder.finish()?.launch()?;
    if !reading.obstruction.is_empty() {
        return Err(ResidentRefusal::Declaration {
            operation: "receiver-return",
            what: format!("the excitation refused with flags {:#x}", reading.obstruction.joined_flags()),
        });
    }
    drop(u);
    drop(tiles);
    drop(next_resident);
    Ok(ReturnedDifferential {
        section: differential,
        octaves: return_shape.needed,
    })
}

/// Enact the return on the resident surface: one passage of four occurrences — the receiver
/// return, its midpoint seal, the carry of the presented carrier, and its seal — and the overlay
/// atom the successor retains.

pub(super) fn enact_return<'chart>(
    surface: &'chart ResidentSurface<'chart>,
    material: ReturnMaterial<'_, 'chart>,
    next: &[u32],
    aperture: NativeReturnAperture,
) -> Result<(OverlayAtom<'chart>, NativeMorphologyDeposit, ReturnedDifferential<'chart>), ResidentRefusal> {
    let refuse = |what: String| ResidentRefusal::Declaration {
        operation: "receiver-return",
        what,
    };
    if next.len() != material.rows {
        return Err(refuse("the next-occurrence population disagrees with the rows".to_owned()));
    }
    let (tiles, tile_width) = terminal_tile_table(surface, &material)?;
    let tile_count = material.width / tile_width;
    let mut next_bytes: Vec<u8> = Vec::with_capacity(next.len() * 4);
    for address in next {
        next_bytes.extend_from_slice(&address.to_le_bytes());
    }
    let next_resident = CountedOctets::upload(surface, &next_bytes)?;
    let terms = SeriesAperture(aperture.series_terms);
    let (u_shift, v_shift) = factor_shifts(
        material.presented_octaves,
        material.presented.width(),
        material.rows,
        material.grain.0 + 2,
    )?;
    let return_shape =
        surface.shape_receiver_return(material.rows, material.width, tile_width, material.grain, terms)?;
    let v_scale = crate::resident_section::DyadicEnclosure {
        lo: 1,
        hi: 1,
        grain: v_shift,
    };
    let carry_shape = if v_shift == 0 {
        surface.shape_carry(
            material.rows,
            material.presented.width(),
            material.presented_octaves,
        )?
    } else {
        surface.shape_scale(
            material.rows,
            material.presented.width(),
            material.presented_octaves,
            v_scale,
        )?
    };
    let u = surface.fresh_section(material.width, material.rows, material.grain)?;
    let v = surface.fresh_section(material.rows, material.presented.width(), material.grain)?;
    let differential = surface.fresh_section(material.rows, material.width, material.grain)?;
    let mut builder: PassageBuilder<'chart> =
        surface.begin_passage(&[vec![], vec![0], vec![], vec![2]])?;
    {
        let lane = builder.open(0, &[])?;
        surface.record_receiver_return(
            &lane,
            tiles.device_ptr(),
            tile_count as u32,
            tile_width as u32,
            material.rows as u32,
            material.width as u32,
            next_resident.device_ptr(),
            material.grain,
            terms,
            u_shift,
            &return_shape,
            &u,
            &differential,
        )?;
    }
    builder.close(0, &u, return_shape.needed)?;
    {
        let lane = builder.open(1, &[0])?;
        surface.record_midpoint_seal(&lane, &u, return_shape.needed)?;
    }
    builder.close_fused(1)?;
    {
        let lane = builder.open(2, &[])?;
        if v_shift == 0 {
            surface.record_carry(&lane, material.presented, &v)?;
        } else {
            surface.record_scale(&lane, material.presented, v_scale, &v)?;
        }
    }
    builder.close(2, &v, carry_shape.needed)?;
    {
        let lane = builder.open(3, &[2])?;
        surface.record_midpoint_seal(&lane, &v, carry_shape.needed)?;
    }
    builder.close_fused(3)?;
    let reading = builder.finish()?.launch()?;
    if !reading.obstruction.is_empty() {
        return Err(refuse(format!(
            "the return refused with flags {:#x}",
            reading.obstruction.joined_flags()
        )));
    }
    let u_octaves = reading.slots.first().map(|slot| slot.max_octave.max(1)).unwrap_or(1);
    let differential_widest_interval =
        reading.slots.first().map(|slot| slot.max_width).unwrap_or(0);
    let v_octaves = reading.slots.get(2).map(|slot| slot.max_octave.max(1)).unwrap_or(1);
    let grain = i32::try_from(material.grain.0).map_err(|_| refuse("the grain overflowed".to_owned()))?;
    let shift = i32::try_from(aperture.learning_shift)
        .map_err(|_| refuse("the learning shift overflowed".to_owned()))?;
    let u_exponent = grain
        .checked_add(shift)
        .and_then(i32::checked_neg)
        .and_then(|exponent| exponent.checked_add(i32::try_from(u_shift).ok()?))
        .ok_or_else(|| refuse("the deposit exponent overflowed".to_owned()))?;
    let v_exponent = i32::try_from(v_shift)
        .ok()
        .and_then(|shift| shift.checked_sub(grain))
        .ok_or_else(|| refuse("the presented exponent overflowed".to_owned()))?;
    let deposit = NativeMorphologyDeposit {
        population: u32::MAX,
        rank: material.rows,
        cross_section_rows: material.width,
        cross_section_width: material.presented.width(),
        learning_shift: aperture.learning_shift,
        series_terms: aperture.series_terms,
        u_exponent,
        v_exponent,
        u_octaves,
        v_octaves,
        u_shift,
        v_shift,
        differential_widest_interval,
        next_occurrences: next.to_vec(),
    };
    drop(tiles);
    drop(next_resident);
    Ok((
        OverlayAtom {
            u: u.into_lower_endpoint(),
            v: v.into_lower_endpoint(),
            rank: material.rows,
            u_exponent,
            v_exponent,
            u_octaves,
            v_octaves,
        },
        deposit,
        ReturnedDifferential {
            section: differential,
            octaves: return_shape.needed,
        },
    ))
}

/// One atom's contribution to a tile of the tied contraction, shaped before the passage opens:
/// the borrowed readouts over the atom's sealed words and the admitted law shape.
pub(super) struct OverlayTile<'chart> {
    u_tile: MountedReadout<'chart>,
    v: MountedReadout<'chart>,
    shape: crate::resident_section::LawShape,
}

impl OverlayTile<'_> {
    pub(super) fn needed(&self) -> u32 {
        self.shape.needed
    }
}

/// Shape `out = u_tile · (v · input)` over the rows `first_row .. first_row + tile_rows` of the
/// cross-section. Pure: nothing is allocated or launched here, so it may precede a capture.
pub(super) fn overlay_tile<'chart>(
    surface: &'chart ResidentSurface<'chart>,
    atom: &OverlayAtom<'chart>,
    input: &ResidentSection<'chart>,
    input_octaves: u32,
    first_row: usize,
    tile_rows: usize,
) -> Result<OverlayTile<'chart>, ResidentRefusal> {
    let word = std::mem::size_of::<i64>();
    let offset = first_row
        .checked_mul(atom.rank)
        .and_then(|words| words.checked_mul(word))
        .and_then(|octets| u64::try_from(octets).ok())
        .ok_or(ResidentRefusal::Declaration {
            operation: "factorized-contract",
            what: "the overlay tile offset overflowed".to_owned(),
        })?;
    let u_tile = MountedReadout::borrowed(
        surface.readout(),
        atom.u.lo_device_ptr() + offset,
        tile_rows,
        atom.rank,
        atom.u_octaves,
        atom.u_exponent,
    );
    let v = MountedReadout::borrowed(
        surface.readout(),
        atom.v.lo_device_ptr(),
        atom.rank,
        atom.v.width(),
        atom.v_octaves,
        atom.v_exponent,
    );
    let shape = surface.shape_factorized_contract(
        input.rows(),
        input.width(),
        input_octaves,
        &u_tile,
        &v,
        atom.rank,
    )?;
    Ok(OverlayTile { u_tile, v, shape })
}

/// Record one shaped contribution as occurrence `index` of an open passage into the
/// pre-allocated `out`.
pub(super) fn record_overlay_contribution<'chart>(
    surface: &'chart ResidentSurface<'chart>,
    builder: &mut PassageBuilder<'chart>,
    index: usize,
    tile: &OverlayTile<'chart>,
    input: &ResidentSection<'chart>,
    out: &ResidentSection<'chart>,
) -> Result<(), ResidentRefusal> {
    {
        let lane = builder.open(index, &[])?;
        surface.record_factorized_contract(&lane, input, &tile.u_tile, &tile.v, &tile.shape, out)?;
    }
    builder.close(index, out, tile.shape.needed)
}



#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn continuation_returns_the_address_that_followed_every_emitted_row() {
        assert_eq!(
            continuation_next_occurrences(&[7, 9], &[7, 9, 11]),
            Some(vec![9, 11])
        );
        assert_eq!(
            continuation_next_occurrences(&[7, 9], &[7, 9, 11, 13]),
            Some(vec![9, 11])
        );
    }

    #[test]
    fn a_non_continuing_occurrence_has_no_comparison() {
        assert_eq!(continuation_next_occurrences(&[7, 9], &[7, 9]), None);
        assert_eq!(continuation_next_occurrences(&[7, 9], &[7, 10, 11]), None);
        assert_eq!(continuation_next_occurrences(&[7, 9], &[9]), None);
        assert_eq!(continuation_next_occurrences(&[], &[1, 2]), None);
    }
}
