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

use mount::DeviceBuffer;
use serde::Serialize;

use crate::{
    embedding_fiber::MountedReadout,
    resident_section::{
        PassageBuilder, ResidentGrain, ResidentRefusal, ResidentSection, ResidentSurface,
        SeriesAperture,
    },
};

/// The declared apparatus apertures of the return. `learning_shift` is `k` in `η = 2^-k`; it enters
/// only as the exponent of the deposit readout. `series_terms` is the certified exponential's
/// aperture. Neither is derived from the material and both are reported in the deposit.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct NativeReturnAperture {
    pub learning_shift: u32,
    pub series_terms: u32,
}

/// The testimony of one deposit, carried in the trace of the operation that enacted it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeMorphologyDeposit {
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
    u: ResidentSection<'chart>,
    v: ResidentSection<'chart>,
    rank: usize,
    u_exponent: i32,
    v_exponent: i32,
    u_octaves: u32,
    v_octaves: u32,
}

impl OverlayAtom<'_> {
    pub(super) fn rank(&self) -> usize {
        self.rank
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

/// Enact the return on the resident surface: one passage of four occurrences — the receiver
/// return, its midpoint seal, the carry of the presented carrier, and its seal — and the overlay
/// atom the successor retains.
pub(super) fn enact_return<'chart>(
    surface: &'chart ResidentSurface<'chart>,
    material: ReturnMaterial<'_, 'chart>,
    next: &[u32],
    aperture: NativeReturnAperture,
) -> Result<(OverlayAtom<'chart>, NativeMorphologyDeposit), ResidentRefusal> {
    let refuse = |what: String| ResidentRefusal::Declaration {
        operation: "receiver-return",
        what,
    };
    let tile_count = material.emission.len();
    if tile_count == 0
        || material.reacted.len() != tile_count
        || next.len() != material.rows
        || material.presented.rows() != material.rows
    {
        return Err(refuse(
            "the emission, reacted, presented, and next-occurrence populations disagree".to_owned(),
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
    let mut next_bytes: Vec<u8> = Vec::with_capacity(next.len() * 4);
    for address in next {
        next_bytes.extend_from_slice(&address.to_le_bytes());
    }
    let tiles = CountedOctets::upload(surface, &addresses)?;
    let next_resident = CountedOctets::upload(surface, &next_bytes)?;
    let terms = SeriesAperture(aperture.series_terms);
    // The factor grains are derived from the carrier budget of the consuming factorized
    // contraction (its stages are admitted in causal order without crediting a negative exponent):
    // the presented octaves, the inner reduction, the two directed hands, the rank join, and a
    // margin of four octaves for the next cycle's input are fixed; what remains is split between
    // the two factors.
    let ceil_log2 = |n: usize| n.max(1).next_power_of_two().ilog2();
    let fixed = material
        .presented_octaves
        .saturating_add(ceil_log2(material.presented.width()))
        .saturating_add(2)
        .saturating_add(ceil_log2(material.rows))
        .saturating_add(4);
    let available = ResidentSurface::carrier_octaves()
        .checked_sub(fixed)
        .filter(|available| *available >= 8)
        .ok_or_else(|| refuse(format!("the carrier admits no overlay beside a presented carrier of {} octaves", material.presented_octaves)))?;
    let v_target = available / 2;
    let u_target = available - v_target;
    let v_shift = material.presented_octaves.saturating_sub(v_target);
    let u_shift = (material.grain.0 + 2).saturating_sub(u_target);
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
            u,
            v,
            rank: material.rows,
            u_exponent,
            v_exponent,
            u_octaves,
            v_octaves,
        },
        deposit,
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
