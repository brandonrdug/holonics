//! The engine's realization (C5 of #603: cut from `field.rs` by object, each item's text as it stood but for its visibility).

#[allow(unused_imports)]
use crate::field::*;
#[allow(unused_imports)]
use crate::inherited::tower::{affine, covector, deposit_step, div_nearest, exp_series, face_code, fewer_bits_weighed, fit32, fit64, half_turn, on_step_grain, outer_sum, ratio_adjoint, ratio_to_power, reach, refuse, release, toward, transposed, weighed_code, Result, TowerError, TowerFace, FACE_BITS, FIRST_RATE, MATERIAL_BITS, MOVE_BITS, SECOND_RATE};
#[allow(unused_imports)]
use crate::inherited::keyed_modes::{ln2_face, log2_face, Exponential};
#[allow(unused_imports)]
use rayon::prelude::*;

/// [definition; agent-inferred, November 1] **A read's logits and its echoes** (§15.3): each unresolved
/// site's readout logits on `2^(−16)` bits (its cavity field where it carries an [`Echo`]) and every
/// site's echo `B_i` on `2^(−63)`: the mean over the heads and the consecutive ticks of the round
/// trip `Σ_j p_ji^(t) p_ij^(t+1)`, `j` reading `i` at one tick and `i` reading `j` at the next. That is
/// the reaction term of the cavity method (TAP's Onsager term, `Σ_j J_ij J_ji` at the order where the
/// read's currents are their shares' averages, the material's gains at the founding's identity): the
/// share of a site's own signal the contacts return to it within one read.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FieldRead {
    pub logits: Vec<Option<Vec<i64>>>,
    pub echo: Vec<u64>,
}

/// [definition; agent-inferred, November 1] **A realization of the field's read and return**: a
/// region's faces and the covector over a section's regions, bit for bit the host's
/// ([`HostField`]). The card's realization is one such; a realization that cannot read a region
/// refuses, never substitutes.
pub trait FieldRealization {
    fn read_and_return(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)>;
    /// [realization; theory, November 13, P58 item 3] **The training path's faces**: each region's open sites' masses at their classes with
    /// their totals, `(m_c, T)` (what [`compared`] reads of a face before a port, [`faces_at_class`]), and the covector, from one read and
    /// return. By default read off the whole faces; a realization that gathers them fetches those words alone. The same pairs either way.
    fn read_and_return_at_class(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<(u128, u128)>>>, Vec<i128>)> {
        let (faces, g) = self.read_and_return(field, regions)?;
        Ok((faces_at_class(&faces, regions), g))
    }
    /// [realization; theory, November 13, P60 items 1d and 2] **The training path with the opening's codes**: [`FieldRealization::read_and_return_at_class`]
    /// and, where the field has the opening's lift, each region's opening code at every compared place ([`Field::opening_codes`]; empty without it).
    /// By default the codes are the host's; a realization that compares the opening in its own forward returns its own, the same words.
    #[allow(clippy::type_complexity)]
    fn read_and_return_opening(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<(u128, u128)>>>, Vec<i128>, Vec<Vec<Option<i64>>>)> {
        let (at_class, g) = self.read_and_return_at_class(field, regions)?;
        let codes = if field.declaration.opening { regions.par_iter().map(|r| field.opening_codes(r)).collect::<Result<_>>()? } else { Vec::new() };
        Ok((at_class, g, codes))
    }
    fn read_faces(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<Vec<Option<TowerFace>>>>;
    /// Each unresolved site's readout logits on `2^(−16)` bits ([`Field::logits`]), the release's read.
    fn read_logits(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<FieldRead>>;
    /// The landmarks of `sites` in `region` ([`Field::landmarks`]), a reading of its last tick.
    fn read_landmarks(&mut self, field: &Field, region: &Region, question: usize, sites: &[usize], count: usize) -> Result<Vec<Vec<(usize, u64)>>>;
    /// The site pairs the realization's contact has met so far, where it counts them.
    fn met_pairs(&self) -> Option<u128> {
        None
    }
    /// [measurement; theory, November 12] The realization's counters so far ([`RealizationCounters`]), where it keeps them: a reading for
    /// the receipts, which no law reads.
    fn counters(&self) -> Option<RealizationCounters> {
        None
    }
    /// A held read's rows by where their mass lies, summed over `regions` ([`Field::held_rows_all`]; each region's
    /// answer start in `questions`), a reading for the receipts.
    fn read_row_shares(&mut self, _field: &Field, _regions: &[Region], _questions: &[usize]) -> Result<Vec<HeldRows>> {
        refuse("a realization that cannot read its rows' shares")
    }
    /// The contact covector by where its pairs lie over `regions` ([`Field::covector_shares`]), a reading.
    fn read_covector_shares(&mut self, _field: &Field, _regions: &[Region]) -> Result<Vec<[u128; 2]>> {
        refuse("a realization that cannot read its covector's shares")
    }
    /// The held answer rows' currents by where they come from, region by region ([`Field::row_currents`]; each region's
    /// answer start in `questions`), a reading.
    fn read_row_currents(&mut self, _field: &Field, _regions: &[Region], _questions: &[usize], _returning: bool) -> Result<Vec<Vec<RowCurrent>>> {
        refuse("a realization that cannot read its rows' currents")
    }
    /// Each region's tick reads ([`Field::tick_reads`]), a reading.
    fn read_ticks(&mut self, _field: &Field, _regions: &[Region]) -> Result<Vec<Vec<TickRead>>> {
        refuse("a realization that cannot read its ticks")
    }
    /// [measurement; theory, November 13, P57 item 2 (G132)] Each region's faces and, by stage ([`Field::tick_charts`]: each tick's opening,
    /// then after the last tick), the open sites' chart rows in site order (`D` words each), a reading.
    fn read_tick_charts(&mut self, _field: &Field, _regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Vec<i32>>>)> {
        refuse("a realization that cannot read its charts by stage")
    }
    /// [measurement; Brandon, November 15 00:58Z; the record of November 13 on loudness beside surprise, test 1] Each region's faces and, by
    /// stage ([`Field::tick_scales`]: each tick's opening, then after the last tick), the open sites' lane scales in site order (`L` each, the
    /// lanes' powers), a reading.
    fn read_tick_scales(&mut self, _field: &Field, _regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Vec<i128>>>)> {
        refuse("a realization that cannot read its lane powers by stage")
    }
    /// [measurement; theory, November 11 18:33, part P2] The faces of `regions` ([`FieldRealization::read_faces`]) and the carry circles' gates
    /// over their open sites ([`CarryGates`]), a reading. By default the faces are the realization's own read and the gates the host's
    /// ([`Field::carry_gates_of`]); a realization that holds the gates in its forward reads them from the same pass.
    fn read_faces_gated(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, CarryGates)> {
        let faces = self.read_faces(field, regions)?;
        let mut gates = CarryGates::new(field.declaration.carry);
        for region in regions {
            gates.add(&field.carry_gates_of(region)?);
        }
        Ok((faces, gates))
    }
    /// Each of `sites`' near field by offset in `region` ([`Field::near_offsets`]), a reading.
    fn read_near_offsets(&mut self, _field: &Field, _region: &Region, _sites: &[usize]) -> Result<Vec<NearOffsets>> {
        refuse("a realization that cannot read its near fields")
    }
    /// Each of `sites`' clocks by tick in `region` ([`Field::blank_clocks`]), a reading.
    fn read_blank_clocks(&mut self, _field: &Field, _region: &Region, _sites: &[usize]) -> Result<Vec<BlankClocks>> {
        refuse("a realization that cannot read its blanks' clocks")
    }
}

/// [measurement; theory, November 12] **A realization's counters** ([`FieldRealization::counters`]): its forward reads and returns, the site
/// pairs its contact met, the batches it split its reads into, and its largest batch's store in octets. A reading only.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RealizationCounters {
    pub reads: u64,
    pub returns: u64,
    pub pairs: u128,
    pub batches: u64,
    pub peak_store: u64,
}

/// The host's realization: the regions on the host's cores, each region's forward and reverse on
/// one core.
#[derive(Clone, Copy, Debug, Default)]
pub struct HostField;

impl FieldRealization for HostField {
    fn read_and_return(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)> {
        field.read_and_return(regions)
    }
    fn read_faces(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<Vec<Option<TowerFace>>>> {
        field.read_faces(regions)
    }
    fn read_logits(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<FieldRead>> {
        field.read_logits(regions)
    }
    fn read_landmarks(&mut self, field: &Field, region: &Region, question: usize, sites: &[usize], count: usize) -> Result<Vec<Vec<(usize, u64)>>> {
        field.landmarks(region, question, sites, count)
    }
    fn read_row_shares(&mut self, field: &Field, regions: &[Region], questions: &[usize]) -> Result<Vec<HeldRows>> {
        field.held_rows_all(regions, questions)
    }
    fn read_covector_shares(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<[u128; 2]>> {
        field.covector_shares(regions)
    }
    fn read_row_currents(&mut self, field: &Field, regions: &[Region], questions: &[usize], returning: bool) -> Result<Vec<Vec<RowCurrent>>> {
        regions.iter().zip(questions).map(|(r, &q)| field.row_currents(r, q, returning)).collect()
    }
    fn read_ticks(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<Vec<TickRead>>> {
        regions.par_iter().map(|r| field.tick_reads(r)).collect()
    }

    fn read_tick_charts(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Vec<i32>>>)> {
        let dw = field.declaration.width;
        let faces = field.read_faces(regions)?;
        let charts = regions
            .par_iter()
            .map(|r| {
                let stages = field.tick_charts(r)?;
                Ok(stages.iter().map(|s| (0..r.classes.len()).filter(|&t| r.unresolved[t]).flat_map(|t| s[t * dw..(t + 1) * dw].iter().copied()).collect()).collect())
            })
            .collect::<Result<Vec<Vec<Vec<i32>>>>>()?;
        Ok((faces, charts))
    }

    fn read_tick_scales(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Vec<i128>>>)> {
        let lanes = field.declaration.lanes;
        let faces = field.read_faces(regions)?;
        let scales = regions
            .par_iter()
            .map(|r| {
                let stages = field.tick_scales(r)?;
                Ok(stages.iter().map(|s| (0..r.classes.len()).filter(|&t| r.unresolved[t]).flat_map(|t| s[t * lanes..(t + 1) * lanes].iter().copied()).collect()).collect())
            })
            .collect::<Result<Vec<Vec<Vec<i128>>>>>()?;
        Ok((faces, scales))
    }

    fn read_near_offsets(&mut self, field: &Field, region: &Region, sites: &[usize]) -> Result<Vec<NearOffsets>> {
        field.near_offsets(region, sites)
    }

    fn read_blank_clocks(&mut self, field: &Field, region: &Region, sites: &[usize]) -> Result<Vec<BlankClocks>> {
        field.blank_clocks(region, sites)
    }
}

/// [agent-inferred, November 1] A held step read on regions it was not fit on
/// ([`FieldLearner::read_step_on`]): its change to those regions' code (the stepped material's
/// code less the material's before the step, on `2^(−20)` bits), the further halvings of the last
/// size read ([`FieldLearner::next_scale`]: the step stands at them unless refused), and whether
/// it refused the step. Read only under [`FieldLearner::read_held`], `false` since November 3: a
/// declared comparison, never the law.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FieldNext {
    pub change: i64,
    pub halvings: u32,
    pub refused: bool,
}

/// A section's receipt: its unresolved sites, its code before and after (on `2^(−20)` bits), its
/// halvings (`0` since the step fluxes, November 5, and still printed), whether a step was deposited,
/// and the held read of the step the section before deposited on this section's regions (only under
/// [`FieldLearner::read_held`]).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FieldReceipt {
    /// The sites the codes are of: each region's domain where it read an open site (§16.23).
    pub sites: usize,
    pub code_before: i64,
    /// The section's code reread under its step; none since the step fluxes (§16.47, Brandon, November 5 17:32).
    pub code_after: Option<i64>,
    pub halvings: u32,
    pub deposited: bool,
    pub next: Option<FieldNext>,
    /// [measurement; §16.41] The step's first-order change of the section's code at its full size, `Σ_i g_i Δθ_i` on the
    /// codes' grain ([`predicted_change`]; `None` past its carrier), and the change a reread measured there (none since
    /// the step fluxes): the section's own parabola `e(μ) = aμ + bμ²` with `a` the first and `a + b` the second.
    pub predicted: Option<i64>,
    pub change: Option<i64>,
    /// [measurement; agent-inferred, November 4, §16.41] **The step before, priced on this section**: `Σ_i g_i Δθ_i` with `g`
    /// this section's covector at the material that stands and `Δθ` the step the section before stood at (its halvings
    /// released), on the codes' grain: the first-order change of this section's code were that step taken once more. Negative
    /// where the step before was short of what this section, which it was not fit on, would take; positive where it went
    /// past. `None` at a learner's first section, after a section that deposited nothing, or past its carrier.
    pub transfer: Option<i64>,
    /// [measurement; agent-inferred, November 6, the unified-theory reading of 08:54] **The external price**, `p_ext =
    /// Σ_i g_i Δθᵉ_i` on the codes' grain, with `Δθᵉ` the step the moments would deposit before this section's covector
    /// moves them (`deposit_step(m_(s−1), v_(s−1))`): a step this section never shaped, priced on it as `transfer` prices the
    /// step before on the next section, with no self-alignment. `transfer − external` of the section before reads the
    /// step's curvature `ΔθᵀHΔθ` from the pass alone, with no reread. `None` past its carrier.
    pub external: Option<i64>,
    /// [measurement; theory, November 12, G96's third branch] **The predicted change by founded part** ([`predicted_parts`]):
    /// `predicted`'s terms gathered by part, [`PART_NAMES`] in order and the old entries last, each on the codes' grain; their sum
    /// stands within one unit a family and part under `predicted`. `None` past its carrier. A reading.
    pub predicted_parts: Option<[i64; PARTS + 1]>,
    /// [measurement; theory, November 13, P60 item 1d] **The opening's code** by region, where the field has the opening's lift: the sum of
    /// `−log₂ p̂⁰_t(u_t)` over the region's compared places on `2^(−20)` bits, and their count (empty without the lift). Read at the material the
    /// section's comparison read, before its deposit.
    pub opening: Vec<(i64, usize)>,
}
