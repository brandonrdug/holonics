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
        PassageBuilder, ResidentEndpoint, ResidentGrain, ResidentRefusal, ResidentSection, ResidentSurface,
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

/// The five resident sections of one already-admitted local contact. The session owns the
/// source/target lineage and must establish its joining before calling this numerical passage.
/// Shape equality alone never establishes that relation. Admittance and source duality are
/// native constitutive chart data, not caller-provided scores or a fabricated semantic current.
pub(super) struct SectionContactMaterial<'a, 'chart> {
    pub presented: &'a ResidentSection<'chart>,
    pub presented_octaves: u32,
    pub transported: &'a ResidentSection<'chart>,
    pub transported_octaves: u32,
    pub arrived: &'a ResidentSection<'chart>,
    pub arrived_octaves: u32,
    pub admittance: &'a ResidentSection<'chart>,
    pub admittance_octaves: u32,
    pub source_duality: &'a ResidentSection<'chart>,
    pub source_duality_octaves: u32,
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

/// The non-prefix current chart of `ConstitutiveSectionReturn` in
/// `HolonicOrientedSiteTransport.lean`. All four elementary operations remain resident:
/// d = admittance * (transported - arrived), v = source_duality * presented.
/// The existing deposit seals u = -2^-learning_shift * d^T and v. Thus its effective formal
/// admittance includes that explicitly declared dyadic readout. Interval sealing retains the
/// existing deposit's numerical boundary; this function does not claim a new exact real model.
pub(super) fn enact_section_contact<'chart>(
    surface: &'chart ResidentSurface<'chart>,
    material: SectionContactMaterial<'_, 'chart>,
    aperture: NativeReturnAperture,
) -> Result<(OverlayAtom<'chart>, NativeMorphologyDeposit), ResidentRefusal> {
    let refuse = |what: &str| ResidentRefusal::Declaration {
        operation: "section-contact-return",
        what: what.to_owned(),
    };
    let rows = material.presented.rows();
    let input_width = material.presented.width();
    let output_width = material.transported.width();
    let grain = material.presented.grain();
    let inputs = [material.transported, material.arrived, material.admittance];
    if rows == 0 || input_width == 0 || output_width == 0
        || inputs.iter().any(|part| part.rows() != rows || part.width() != output_width)
        || material.source_duality.rows() != rows || material.source_duality.width() != input_width
        || inputs.iter().any(|part| part.grain() != grain)
        || material.source_duality.grain() != grain
    {
        return Err(refuse("the joined contact has incompatible resident charts"));
    }
    let negative = crate::resident_section::DyadicEnclosure { lo: -1, hi: -1, grain: 0 };
    let negate_shape = surface.shape_scale(rows, output_width, material.arrived_octaves, negative)?;
    let difference_shape = surface.shape_re_entry(
        rows, output_width, material.transported_octaves, negate_shape.needed,
    )?;
    let current_shape = surface.shape_hadamard(
        rows, output_width, difference_shape.needed, material.admittance_octaves,
    )?;
    let covector_shape = surface.shape_hadamard(
        rows, input_width, material.presented_octaves, material.source_duality_octaves,
    )?;
    let negated = surface.fresh_section(rows, output_width, grain)?;
    let difference = surface.fresh_section(rows, output_width, grain)?;
    let differential = surface.fresh_section(rows, output_width, grain)?;
    let covector = surface.fresh_section(rows, input_width, grain)?;
    let mut passage = surface.begin_passage(&[vec![], vec![0], vec![1], vec![]])?;
    {
        let lane = passage.open(0, &[])?;
        surface.record_scale(&lane, material.arrived, negative, &negated)?;
    }
    passage.close(0, &negated, negate_shape.needed)?;
    {
        let lane = passage.open(1, &[0])?;
        surface.record_re_entry(&lane, material.transported, &negated, &difference)?;
    }
    passage.close(1, &difference, difference_shape.needed)?;
    {
        let lane = passage.open(2, &[1])?;
        surface.record_hadamard(&lane, &difference, material.admittance, &differential)?;
    }
    passage.close(2, &differential, current_shape.needed)?;
    {
        let lane = passage.open(3, &[])?;
        surface.record_hadamard(&lane, material.presented, material.source_duality, &covector)?;
    }
    passage.close(3, &covector, covector_shape.needed)?;
    let reading = passage.finish()?.launch()?;
    if !reading.obstruction.is_empty() {
        return Err(refuse("the native joined-section passage returned an obstruction"));
    }
    deposit_from_material(surface, DepositMaterial {
        differential: &differential,
        differential_octaves: reading.slots[2].max_octave.max(1),
        presented: &covector,
        presented_octaves: reading.slots[3].max_octave.max(1),
        grain,
    }, aperture)
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
#[path = "operative_adjoint_tests.rs"]
mod adjoint_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{embedding_fiber::ResidentReadout, resident_section::ResidentSectionRest};

    #[test]
    #[ignore = "requires CUDA; explicit joined-section numerical binding"]
    fn joined_section_contact_deposits_oriented_factors_without_host_section_reads() {
        let readout = ResidentReadout::new().expect("CUDA readout");
        let surface = ResidentSurface::on(&readout).expect("resident surface");
        let grain = ResidentGrain(4);
        let mount = |width, words: &[i64]| {
            surface.mount_section_rest(&ResidentSectionRest {
                rows: 1, width, grain, bound_octaves: 8,
                intervals: words.iter().map(|word| (*word, *word)).collect(),
            }).expect("native section")
        };
        let presented = mount(3, &[16, 32, 0]);
        let transported = mount(2, &[48, 64]);
        let arrived = mount(2, &[80, 16]);
        let admittance = mount(2, &[8, 32]);
        let duality = mount(3, &[16, 8, 48]);
        let make = |arrived| SectionContactMaterial {
            presented: &presented, presented_octaves: 8,
            transported: &transported, transported_octaves: 8,
            arrived, arrived_octaves: 8,
            admittance: &admittance, admittance_octaves: 8,
            source_duality: &duality, source_duality_octaves: 8,
        };
        let before = surface.census();
        let (atom, receipt) = enact_section_contact(&surface, make(&arrived),
            NativeReturnAperture { learning_shift: 1, series_terms: 14 }).expect("contact return");
        assert_eq!(surface.census().section_read_outs, before.section_read_outs,
            "only the final test receiver may read a section");
        assert_eq!(receipt.rank, 1, "one paired occurrence, not a caller-chosen rank");
        assert!(receipt.next_occurrences.is_empty(), "no token comparison was fabricated");
        // The complete factorized map is [[1/2,1/2,0],[-3,-3,0]]. A later query which
        // excites an unused column does not make it participate in this local deposit.
        let query = mount(3, &[32, 16, 1584]);
        let apply = |atom: &OverlayAtom<'_>| {
            let (u, v) = atom.readouts(&surface);
            let inward_shape = surface.shape_contract(1, 3, 12, &v).expect("inward shape");
            let outward_shape = surface.shape_contract(1, 1, inward_shape.needed, &u).expect("outward shape");
            let inward = surface.fresh_section(1, 1, grain).unwrap();
            let outward = surface.fresh_section(1, 2, grain).unwrap();
            let mut passage = surface.begin_passage(&[vec![], vec![0]]).unwrap();
            {
                let lane = passage.open(0, &[]).unwrap();
                surface.record_contract(&lane, &query, &v, &inward).unwrap();
            }
            passage.close(0, &inward, inward_shape.needed).unwrap();
            {
                let lane = passage.open(1, &[0]).unwrap();
                surface.record_contract(&lane, &inward, &u, &outward).unwrap();
            }
            passage.close(1, &outward, outward_shape.needed).unwrap();
            let reading = passage.finish().unwrap().launch().unwrap();
            assert!(reading.obstruction.is_empty());
            surface.read_out(&outward).unwrap()
        };
        assert_eq!(apply(&atom), vec![(24, 24), (-144, -144)]);
        let (matched, _) = enact_section_contact(&surface, make(&transported),
            NativeReturnAperture { learning_shift: 1, series_terms: 14 }).expect("matched return");
        assert_eq!(apply(&matched), vec![(0, 0), (0, 0)]);
    }

    #[test]
    #[ignore = "requires CUDA; explicit joined-section chart refusal"]
    fn joined_section_contact_refuses_incompatible_charts_before_allocating_a_deposit() {
        let readout = ResidentReadout::new().expect("CUDA readout");
        let surface = ResidentSurface::on(&readout).expect("resident surface");
        let mount = |grain| surface.mount_section_rest(&ResidentSectionRest {
            rows: 1, width: 1, grain, bound_octaves: 8, intervals: vec![(16,16)],
        }).unwrap();
        let standing = mount(ResidentGrain(4));
        let wrong_chart = mount(ResidentGrain(3));
        let before = surface.census();
        let returned = enact_section_contact(&surface, SectionContactMaterial {
            presented: &standing, presented_octaves: 8,
            transported: &standing, transported_octaves: 8,
            arrived: &wrong_chart, arrived_octaves: 8,
            admittance: &standing, admittance_octaves: 8,
            source_duality: &standing, source_duality_octaves: 8,
        }, NativeReturnAperture { learning_shift: 0, series_terms: 14 });
        assert!(matches!(returned, Err(ResidentRefusal::Declaration { operation: "section-contact-return", .. })));
        let after = surface.census();
        assert_eq!(before.resident_octets_now, after.resident_octets_now);
        assert_eq!(before.section_read_outs, after.section_read_outs);
    }

    #[test]
    #[ignore = "requires CUDA; additive-junction matched and unaffected controls"]
    fn identity_admittance_matched_current_is_absent_and_an_unaffected_native_coordinate_stands() {
        use super::super::operative_adjoint::{NativeAdjointContraction, add_overlay_adjoints};
        let readout = ResidentReadout::new().expect("CUDA readout");
        let surface = ResidentSurface::on(&readout).expect("resident surface");
        let grain = ResidentGrain(4);
        let mount = |words: &[i64]| surface.mount_section_rest(&ResidentSectionRest {
            rows: 1, width: words.len(), grain, bound_octaves: 8,
            intervals: words.iter().map(|word| (*word,*word)).collect(),
        }).unwrap();
        let x = mount(&[16,0]);
        let transported = mount(&[48,80]);
        let same_face_distinct_carrier = mount(&[48,80]);
        let arrived = mount(&[64,112]);
        let aperture = NativeReturnAperture { learning_shift: 0, series_terms: 14 };
        assert!(enact_identity_admittance_contact(&surface, &x, 8, &transported, 8,
            &same_face_distinct_carrier, 8, aperture).unwrap().is_none());
        let (atom, _) = enact_identity_admittance_contact(&surface, &x, 8, &transported, 8,
            &arrived, 8, aperture).unwrap().expect("nonzero local current");
        let dy = mount(&[16,0]);
        let base = NativeAdjointContraction { section: mount(&[16,80]), bound_octaves: 8, tiles: 1 };
        let before = surface.census();
        let returned = add_overlay_adjoints(&surface, base, &dy, 8, &[atom]).unwrap();
        assert_eq!(surface.census().section_read_outs, before.section_read_outs);
        assert_eq!(surface.read_out(&returned.section).unwrap(), vec![(32,32),(80,80)],
            "the affected coordinate changed and the nonzero unaffected coordinate stayed exact");
    }

    #[test]
    #[ignore = "requires CUDA; declared current scaling and division enclosures"]
    fn contact_readout_scale_retains_signed_division_enclosures() {
        let readout = ResidentReadout::new().expect("CUDA readout");
        let surface = ResidentSurface::on(&readout).expect("resident surface");
        let section = surface.mount_section_rest(&ResidentSectionRest {
            rows: 1, width: 3, grain: ResidentGrain(4), bound_octaves: 8,
            intervals: vec![(3,3),(-3,-3),(32,32)],
        }).unwrap();
        let before = surface.census();
        let (scaled, width) = scale_contact_differential(&surface,
            ReturnedDifferential { section, octaves: 8 }, 1).unwrap();
        assert_eq!(surface.census().section_read_outs, before.section_read_outs);
        assert_eq!(width, Some(1));
        assert_eq!(surface.read_out(&scaled.section).unwrap(), vec![(1,2),(-2,-1),(16,16)]);
        let (unchanged, observation) = scale_contact_differential(&surface, scaled, 0).unwrap();
        assert_eq!(observation, None);
        assert_eq!(surface.read_out(&unchanged.section).unwrap(), vec![(1,2),(-2,-1),(16,16)]);
    }

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
