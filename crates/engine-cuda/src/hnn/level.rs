//! The card realization's level (C5 of #603: cut from `hnn/field.rs` by object, each item's text as it stood but for its visibility).

#[allow(unused_imports)]
use crate::hnn::field::*;
#[allow(unused_imports)]
use core::ffi::c_void;
#[allow(unused_imports)]
use std::time::Instant;
#[allow(unused_imports)]
use holonics_engine::field::{band_bits, landmarks_of, BlankClocks, CarryGates, Constitution, Declaration, ReadLogits, Realization, HeldRows, NearOffsets, RealizationCounters, RowCurrent, Region, Scale, TickRead, NEAR, SHARE_BITS, STATE_BITS};
#[allow(unused_imports)]
use holonics_engine::field::{level_cut, level_section, strand_level_cut, PACE_BITS};
#[allow(unused_imports)]
use holonics_engine::field::{TowerError, TowerFace, MATERIAL_BITS};
#[allow(unused_imports)]
use crate::cuda::{Dim3, Module};
#[allow(unused_imports)]
use crate::hnn::card::{Card, CardBuffer, CardError};

/// A level above for a run ([`Resident::tower_run`]): the level's field's words and buffers, the glue's material (read by the
/// level's words pointed at it), each level's covector, and the cut's section and half turn.
pub(crate) struct TowerRun<'c> {
    pub(crate) cwords: Words,
    pub(crate) glue_at: u64,
    pub(crate) _cup: Upload<'c>,
    pub(crate) _glue: Pooled<'c, i32>,
    pub(crate) cg: Option<Pooled<'c, i128>>,
    pub(crate) gg: Option<Pooled<'c, i128>>,
    pub(crate) harmonics: usize,
    pub(crate) split: usize,
    pub(crate) section: i64,
    pub(crate) pi: i128,
    pub(crate) offsets: (usize, usize, usize, usize, usize),
    pub(crate) reach_a: u64,
    pub(crate) reach_b: u64,
    /// [the record of the two streams §11] Where the run is of passages read by two streams on a tower that carries its one-sided block
    /// (the host's `Constitution::scale_forward_before`): the block's offsets `B⁻`, `b_B⁻` in the glue and `B⁻`'s reach. The level's
    /// words then carry the known stream's word (`FieldWords::before`), so its ticks hear only the epochs before.
    pub(crate) before: Option<(usize, usize, u64)>,
}

/// A site that reads no epoch (`LEVEL_NONE` in `kernels/field.cu`).
pub(crate) const LEVEL_NONE: u32 = u32::MAX;

/// A strand batch's tables for the level ([`Resident::tower_batch`]): each fine site's own epoch (an open place none), each epoch's run
/// of known sites (`lo`, `hi`), and the two runs of sites that read it (the known sites of the epoch after it, `lo1`, `hi1`, and the open
/// places that stand in that epoch, `lo2`, `hi2`). [`TowerBatch::epoch`] then holds the epoch each site reads.
pub(crate) struct StrandTables<'c> {
    pub(crate) own: Pooled<'c, u32>,
    pub(crate) lo: Pooled<'c, u32>,
    pub(crate) hi: Pooled<'c, u32>,
    pub(crate) lo1: Pooled<'c, u32>,
    pub(crate) hi1: Pooled<'c, u32>,
    pub(crate) lo2: Pooled<'c, u32>,
    pub(crate) hi2: Pooled<'c, u32>,
}

/// A level's epochs for one batch ([`Resident::tower_batch`]): the epochs staged as the level's regions, each fine place's epoch, its
/// harmonics, the epochs' fine offsets, and the per-pass buffers.
pub(crate) struct TowerBatch<'c> {
    pub(crate) st: Staged<'c>,
    pub(crate) ticks: Vec<Tick<'c>>,
    pub(crate) _trips: Pooled<'c, i128>,
    pub(crate) _moment: Pooled<'c, i64>,
    pub(crate) pr: Pooled<'c, i64>,
    pub(crate) _clocks: Vec<Pooled<'c, i64>>,
    pub(crate) _plain: Pooled<'c, u8>,
    pub(crate) split_read: Pooled<'c, i32>,
    pub(crate) split_scale: Pooled<'c, i128>,
    pub(crate) restricted: Pooled<'c, i64>,
    pub(crate) read1: Pooled<'c, i32>,
    pub(crate) scale1: Pooled<'c, i128>,
    pub(crate) pad: Pooled<'c, i64>,
    pub(crate) epoch: Pooled<'c, u32>,
    pub(crate) harmonics: Pooled<'c, i64>,
    pub(crate) off: Pooled<'c, u32>,
    /// The level's skin addresses, its clock's skins and near phases (the stores the fine batch keeps for its own clock).
    pub(crate) _saddr: Pooled<'c, i64>,
    pub(crate) _stores: Vec<Pooled<'c, u32>>,
    /// A strand batch's tables ([`StrandTables`]).
    pub(crate) strand: Option<StrandTables<'c>>,
}

impl<'c> Resident<'c> {

    /// [definition; agent-inferred, November 3] **A tower's packets' level on the card** (the host's `field::scale`): the
    /// packets' field uploaded beside the fine one (reading its resident exponential), the glue uploaded, and each level's
    /// covector where the run returns one.
    /// `one_sided`: the known stream's word of a run of passages read by two streams (`FieldWords::before`, one or two), zero otherwise.
    pub(crate) fn tower_run(&self, field: &Constitution, s: &Scale, face: u64, returning: bool, one_sided: u64) -> Result<TowerRun<'c>> {
        let (mut cwords, cup, _) = self.upload(&s.coarse, Some(face))?;
        let glue = self.timed(Kind::Copy, || self.take_up(&s.glue)).map_err(device)?;
        let offsets = s.glue_offsets(field.declaration.width);
        let (a, ab, b, bb, _) = offsets;
        let reach = |from: usize, to: usize| s.glue[from..to].iter().map(|v| v.unsigned_abs() as u64).max().unwrap_or(0);
        let cg = if returning { Some(self.timed(Kind::Alloc, || self.take_zeroed::<i128>(s.coarse.theta.len())).map_err(device)?) } else { None };
        // (the glue's whole covector: where the level carries its one-sided block, a run of the law leaves that block's at zero)
        let gg = if returning { Some(self.timed(Kind::Alloc, || self.take_zeroed::<i128>(s.glue.len())).map_err(device)?) } else { None };
        cwords.gcov = cg.as_ref().map_or(0, |g| g.device_ptr());
        let _ = (ab, bb);
        let before = if one_sided != 0 {
            let (b2, bb2, _) = s.before_offsets(field.declaration.width).ok_or(TowerError::Refused("a strand's level on a tower without its one-sided block"))?;
            cwords.before = one_sided;
            Some((b2, bb2, reach(b2, bb2)))
        } else {
            None
        };
        Ok(TowerRun { cwords, glue_at: glue.device_ptr(), _cup: cup, _glue: glue, cg, gg, harmonics: s.harmonics, split: s.split, section: level_section(field.declaration.alphabet), pi: field.half_turn(), offsets, reach_a: reach(a, offsets.1), reach_b: reach(b, offsets.3), before })
    }

    /// A batch's epochs staged as the level's field's regions (an epoch definite where its every place is, keyed where any is: unresolved
    /// and carrying class 0 where keyed and not definite), each region cut from its places' `news` by the host's `level_cut`; each fine
    /// place's epoch and harmonics, the epochs' fine offsets, the level's clocks uploaded as the cut gives them and its per-pass buffers.
    /// [realization; agent-inferred, November 14, the ring record §4] The level's ticks are each read's own ([`Resident::level_ticks`]): the
    /// news is the opening's comparison's face, which no mark enters (the host's `Constitution::level_news` reads `cavity_forward`), so a field that reads
    /// twice cuts its level once a batch and both reads stand on the cut.
    /// [the record of the two streams §11] A batch of passages read by two streams (`tr.before`; the host's `strand_level_cut`): each
    /// region's known stream is cut from its places' `news` where a one-sided stream can name a site, with `open_news` each place's
    /// expected news; an epoch's sites are its known sites; each site's epoch here is the one it reads (the epoch before its own, an
    /// open place's the one before the epoch of the place before it), and [`StrandTables`] hold the rest.
    pub(crate) fn tower_batch(&self, field: &Constitution, tr: &mut TowerRun<'c>, fine: &Staged<'c>, regions: usize, news: &[i64], open_news: Option<&[i64]>) -> Result<TowerBatch<'c>> {
        let s = field.scale.as_deref().ok_or(TowerError::Refused("a level's batch of a field without a level"))?;
        let coarse = &s.coarse;
        let cd = coarse.declaration;
        let h = tr.harmonics;
        let carried = vec![(0u32, 1u32 << 16)];
        let mut owned: Vec<(Vec<usize>, Vec<bool>, Vec<Option<Vec<(u32, u32)>>>)> = Vec::with_capacity(regions);
        let (mut epoch_of, mut harm, mut off, mut taus) = (Vec::with_capacity(fine.sites), Vec::with_capacity(fine.sites * h), Vec::new(), Vec::with_capacity(regions));
        // The strand batch's tables, and its regions' known places (the stage's own, taken off while the level's regions are staged).
        let heard: Vec<u32> = self.strand_heard.borrow().clone();
        let strand = tr.before.is_some();
        if strand && (heard.len() != regions || open_news.is_none()) {
            return Err(TowerError::Refused("a strand's level's batch without its regions' known places or their expected news"));
        }
        let (mut own, mut lo, mut hi, mut lo1, mut hi1, mut lo2, mut hi2): (Vec<u32>, Vec<u32>, Vec<u32>, Vec<u32>, Vec<u32>, Vec<u32>, Vec<u32>) = Default::default();
        for r in 0..regions {
            let (first, end) = (fine.region_off[r] as usize, fine.region_off[r + 1] as usize);
            if strand {
                let n = heard[r] as usize;
                if end - first != 2 * n {
                    return Err(TowerError::Refused("a strand staged as other than its known sites and as many open places"));
                }
                let open_news = open_news.ok_or(TowerError::Refused("a strand's level without its expected news"))?;
                let sc = strand_level_cut(&news[first..first + n], &open_news[first..first + n], tr.section, h, tr.pi)?;
                let base = off.len() as u32;
                let epochs = sc.cut.anchors.len();
                let ends = |j: usize| sc.cut.anchors.get(j + 1).copied().unwrap_or(n);
                for j in 0..epochs {
                    off.push((first + sc.cut.anchors[j]) as u32);
                    lo.push((first + sc.cut.anchors[j]) as u32);
                    hi.push((first + ends(j)) as u32);
                    if j + 1 < epochs {
                        // The sites that read epoch `j`: the known sites of epoch `j + 1`, and the open places whose place before stands in it.
                        lo1.push((first + sc.cut.anchors[j + 1]) as u32);
                        hi1.push((first + ends(j + 1)) as u32);
                        lo2.push((first + n + sc.cut.anchors[j + 1] + 1) as u32);
                        hi2.push((first + n + (ends(j + 1) + 1).min(n)) as u32);
                    } else {
                        lo1.push(0);
                        hi1.push(0);
                        lo2.push(0);
                        hi2.push(0);
                    }
                }
                epoch_of.extend(sc.source.iter().map(|src| src.map_or(LEVEL_NONE, |j| base + j as u32)));
                own.extend(sc.cut.epoch.iter().map(|&j| base + j as u32));
                own.extend(std::iter::repeat_n(LEVEL_NONE, n));
                harm.extend_from_slice(&sc.cut.harmonics);
                harm.extend_from_slice(&sc.open_harmonics);
                taus.push(sc.cut.tau);
                owned.push((vec![0usize; epochs], vec![false; epochs], vec![None; epochs]));
                continue;
            }
            let cut = level_cut(&news[first..end], tr.section, h, tr.pi)?;
            let base = off.len() as u32;
            let epochs = cut.anchors.len();
            let (mut unres, mut faces) = (Vec::with_capacity(epochs), Vec::with_capacity(epochs));
            for j in 0..epochs {
                let span = first + cut.anchors[j]..first + cut.anchors.get(j + 1).copied().unwrap_or(end - first);
                off.push(span.start as u32);
                let definite = span.clone().all(|t| fine.definite[t] != 0);
                let keyed = span.clone().any(|t| fine.unresolved[t] == 0 || fine.mix_off[t + 1] != fine.mix_off[t]);
                unres.push(!definite);
                faces.push((keyed && !definite).then(|| carried.clone()));
            }
            epoch_of.extend(cut.epoch.iter().map(|&j| base + j as u32));
            harm.extend_from_slice(&cut.harmonics);
            taus.push(cut.tau);
            owned.push((vec![0usize; epochs], unres, faces));
        }
        off.push(fine.sites as u32);
        let pregions: Vec<Region> = owned.iter().map(|(c, u, f)| Region { classes: c, unresolved: u, faces: if f.iter().any(Option::is_some) { f } else { &[] }, locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false }).collect();
        // (the level's regions are epochs, no passage read by two streams: the fine batch's known places stand aside while they are staged)
        let fine_heard = std::mem::take(&mut *self.strand_heard.borrow_mut());
        let staged = self.stage(&pregions, cd.alphabet, cd.width, &cd, &mut tr.cwords);
        *self.strand_heard.borrow_mut() = fine_heard;
        let st = staged?;
        let (sites, m2, n) = (st.sites, 2 * cd.complex(), cd.modes);
        let trips = self.timed(Kind::Alloc, || self.take_zeroed::<i128>(sites.max(1))).map_err(device)?;
        tr.cwords.trips = trips.device_ptr();
        // The level carries no moments: its values and probes read zero there.
        let moment = self.timed(Kind::Alloc, || self.take_zeroed::<i64>((sites * m2).max(1))).map_err(device)?;
        tr.cwords.moment = moment.device_ptr();
        let pr = self.timed(Kind::Alloc, || self.take::<i64>((sites * m2).max(1))).map_err(device)?;
        tr.cwords.pr = pr.device_ptr();
        // The level's clock (the host's `level_paces`): every turned head on the news between the epochs' anchors, uploaded as the cut
        // gives it; the frames and the skins' addresses then follow by the fine field's own laws on the level's strand.
        let paced = cd.paced_heads();
        let one = 1i64 << PACE_BITS;
        let (mut kappa, mut tau, mut plain) = (Vec::with_capacity(paced * sites), Vec::with_capacity(paced * sites), Vec::with_capacity(paced * regions));
        for _ in 0..paced {
            for t in &taus {
                tau.extend_from_slice(t);
                kappa.extend((0..t.len()).map(|j| if j == 0 { one } else { t[j] - t[j - 1] }));
            }
            plain.extend(taus.iter().map(|t| u8::from((1..t.len()).all(|j| t[j] - t[j - 1] == one))));
        }
        let up64 = |v: &[i64]| self.timed(Kind::Copy, || self.take_up(if v.is_empty() { &[0i64][..] } else { v })).map_err(device);
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let clocks = vec![up64(&kappa)?, up64(&tau)?, up64(&tau)?, self.timed(Kind::Alloc, || self.take::<i64>((2 * paced * sites * n).max(1))).map_err(device)?];
        let plain = self.timed(Kind::Copy, || self.take_up(if plain.is_empty() { &[0u8][..] } else { &plain[..] })).map_err(device)?;
        tr.cwords.kappa = clocks[0].device_ptr();
        tr.cwords.tau = clocks[1].device_ptr();
        tr.cwords.sigma = clocks[2].device_ptr();
        tr.cwords.pframe = clocks[3].device_ptr();
        tr.cwords.plain = plain.device_ptr();
        // The level's own stores of its clock, as the fine batch keeps them for its own (`skin_fill` fills the pairs' and the crowds' skins at
        // each tick, `clock_fill` the near phases and skins and the crowd edges' far skins once the clock is set).
        let saddr = alloc64(3 * paced * n * sites)?;
        tr.cwords.saddr = saddr.device_ptr();
        let alloc32 = |len: usize| self.timed(Kind::Alloc, || self.take::<u32>(len.max(1))).map_err(device);
        let mut stores = Vec::new();
        if paced > 0 {
            stores.push(alloc32(paced * st.skin_entries * n)?);
            stores.push(alloc32(paced * sites * tr.cwords.slots as usize * n)?);
            (tr.cwords.skin, tr.cwords.cskin) = (stores[0].device_ptr(), stores[1].device_ptr());
        } else {
            (tr.cwords.skin, tr.cwords.cskin) = (0, 0);
        }
        let tm = cd.moment_modes();
        if paced > 0 && tm > 0 {
            let near = tm * sites * CLOCK_NEAR;
            stores.push(alloc32(2 * near)?);
            stores.push(alloc32(near)?);
            (tr.cwords.mphase, tr.cwords.mskin) = (stores[2].device_ptr(), stores[3].device_ptr());
        } else {
            (tr.cwords.mphase, tr.cwords.mskin) = (0, 0);
        }
        if paced > 0 {
            self.launch("field_skin_addresses", Self::cells((paced * n * sites) as u64), THREADS, &mut [arg(&mut tr.cwords)])?;
            self.launch("field_pframes", Self::cells((paced * sites * n) as u64), THREADS, &mut [arg(&mut tr.cwords)])?;
            self.clock_fill(coarse, &tr.cwords, sites)?;
        }
        let d0 = field.declaration.width;
        let split_read = self.timed(Kind::Alloc, || self.take::<i32>((fine.sites * d0).max(1))).map_err(device)?;
        let split_scale = self.timed(Kind::Alloc, || self.take::<i128>((fine.sites * field.declaration.lanes).max(1))).map_err(device)?;
        let restricted = alloc64(sites * h * d0)?;
        let read1 = self.timed(Kind::Alloc, || self.take::<i32>((sites * cd.width).max(1))).map_err(device)?;
        let scale1 = self.timed(Kind::Alloc, || self.take::<i128>((sites * cd.lanes).max(1))).map_err(device)?;
        let pad = alloc64(sites * h * d0)?;
        let epoch = self.timed(Kind::Copy, || self.take_up(if epoch_of.is_empty() { &[0u32][..] } else { &epoch_of[..] })).map_err(device)?;
        let harmonics = up64(&harm)?;
        let off = self.timed(Kind::Copy, || self.take_up(&off)).map_err(device)?;
        let strand = if strand {
            let up32 = |v: &[u32]| self.timed(Kind::Copy, || self.take_up(if v.is_empty() { &[0u32][..] } else { v })).map_err(device);
            Some(StrandTables { own: up32(&own)?, lo: up32(&lo)?, hi: up32(&hi)?, lo1: up32(&lo1)?, hi1: up32(&hi1)?, lo2: up32(&lo2)?, hi2: up32(&hi2)? })
        } else {
            None
        };
        Ok(TowerBatch { st, ticks: Vec::new(), _trips: trips, _moment: moment, pr, _clocks: clocks, _plain: plain, split_read, split_scale, restricted, read1, scale1, pad, epoch, harmonics, off, _saddr: saddr, _stores: stores, strand })
    }

    /// A read's own ticks on a batch's level ([`Resident::tower_batch`]): every tick kept where the read keeps the fine field's, and the shares
    /// stored where it stores them, taken as [`Resident::tick`] takes the fine field's.
    pub(crate) fn level_ticks(&self, field: &Constitution, tb: &TowerBatch<'c>, regions: usize, stored: bool, returning: bool, kept: bool) -> Result<Vec<Tick<'c>>> {
        let s = field.scale.as_deref().ok_or(TowerError::Refused("a level's ticks of a field without a level"))?;
        (0..if kept { s.coarse.declaration.ticks } else { 1 }).map(|_| self.tick(tb.st.sites, tb.st.pairs, regions, &s.coarse, stored, returning, true)).collect()
    }

    /// The level's forward at the split (the host's `scale_forward`): the fine faces read, each epoch's harmonics of its places' reads
    /// restricted through `A`, the level's ticks, and the prolongation, each place reading its epoch's harmonic blocks at its own phase,
    /// added back into the fine faces.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn tower_forward(&self, field: &Constitution, words: &mut Words, tr: &mut TowerRun<'c>, tb: &TowerBatch<'c>, regions: usize, stored: bool, returning: bool, kept: bool) -> Result<()> {
        let s = field.scale.as_deref().ok_or(TowerError::Refused("a level's forward of a field without a level"))?;
        let (d0, d1, h) = (field.declaration.width, s.coarse.declaration.width, tr.harmonics);
        let (a, ab, b, bb, _) = tr.offsets;
        let epochs = tb.st.sites;
        self.chart(words, words.x, &tb.split_read, &tb.split_scale, false)?;
        let (mut src, mut hp, mut op, mut e64, mut h32, mut w32, mut dst) = (tb.split_read.device_ptr(), tb.harmonics.device_ptr(), tb.off.device_ptr(), epochs as u64, h as u32, d0 as u32, tb.restricted.device_ptr());
        // [the record of the two streams §11] A strand's level: the restriction over each epoch's known sites, and below the epoch before
        // through `B⁻` (the host's `scale_forward_before`).
        let (b, bb, reach_b) = match (tr.before, tb.strand.as_ref()) {
            (Some((b2, bb2, reach2)), Some(tables)) => {
                let (mut lo, mut hi, mut none2a, mut none2b) = (tables.lo.device_ptr(), tables.hi.device_ptr(), 0u64, 0u64);
                self.launch("field_level_chart32_spans", Self::cells((epochs * h * d0) as u64), THREADS, &mut [arg(words), arg(&mut src), arg(&mut hp), arg(&mut lo), arg(&mut hi), arg(&mut none2a), arg(&mut none2b), arg(&mut e64), arg(&mut h32), arg(&mut w32), arg(&mut dst)])?;
                (b2, bb2, reach2)
            }
            (None, None) => {
                self.launch("field_level_chart32", Self::cells((epochs * h * d0) as u64), THREADS, &mut [arg(words), arg(&mut src), arg(&mut hp), arg(&mut op), arg(&mut e64), arg(&mut h32), arg(&mut w32), arg(&mut dst)])?;
                (b, bb, tr.reach_b)
            }
            _ => return Err(TowerError::Refused("a strand's level's run and its batch's tables stand together")),
        };
        let mut gwords = tr.cwords;
        gwords.theta = tr.glue_at;
        self.affine("field_affine_x64", &mut gwords, a as u64, ab as u64, tr.reach_a, d1, h * d0, tb.restricted.device_ptr(), h * d0, tr.cwords.x, d1, 0, false)?;
        for k in 0..s.coarse.declaration.ticks {
            self.tick_forward(&s.coarse, &mut tr.cwords, &tb.ticks, k, kept, stored, false, false, returning, tb.pr.device_ptr(), epochs, tb.st.pairs, regions)?;
        }
        let x1 = tr.cwords.x;
        self.chart(&mut tr.cwords, x1, &tb.read1, &tb.scale1, false)?;
        let mut gwords = tr.cwords;
        gwords.theta = tr.glue_at;
        self.affine("field_affine_x32", &mut gwords, b as u64, bb as u64, reach_b, h * d0, d1, tb.read1.device_ptr(), d1, tb.pad.device_ptr(), h * d0, 0, false)?;
        let (mut vp, mut hp, mut ep, mut h32, mut w32, mut dst, mut add) = (tb.pad.device_ptr(), tb.harmonics.device_ptr(), tb.epoch.device_ptr(), h as u32, d0 as u32, words.x, 1u32);
        self.launch("field_level_unchart", Self::cells((tb_fine_sites(words) * d0) as u64), THREADS, &mut [arg(words), arg(&mut vp), arg(&mut hp), arg(&mut ep), arg(&mut h32), arg(&mut w32), arg(&mut dst), arg(&mut add)])
    }

    /// The level's reverse at the split (the host's `scale_return`): `back.dx`, the covector of the fine faces after the prolongation,
    /// carried through the prolongation, the level's ticks and the restriction into the covector of the fine faces before it; the
    /// level's and the glue's covectors added into their own buffers. The cut is data and takes nothing.
    pub(crate) fn tower_back(&self, field: &Constitution, words: &mut Words, tr: &mut TowerRun<'c>, tb: &TowerBatch<'c>, back: &Back<'c>, cb: &Back<'c>) -> Result<()> {
        let s = field.scale.as_deref().ok_or(TowerError::Refused("a level's reverse of a field without a level"))?;
        let (d0, d1, h) = (field.declaration.width, s.coarse.declaration.width, tr.harmonics);
        let (a, ab, b, bb, _) = tr.offsets;
        let epochs = tb.st.sites;
        let (cg, gg) = match (tr.cg.as_deref(), tr.gg.as_deref()) {
            (Some(cg), Some(gg)) => (cg, gg),
            _ => return Err(TowerError::Refused("a level's reverse without its levels' covectors")),
        };
        // The prolongation: `δv(j)` each epoch's harmonics of its places' covectors, then `δb_B`, `δB` and `δr̂¹ = Bᵀ δv`.
        let (mut src, mut hp, mut op, mut e64, mut h32, mut w32, mut dst) = (back.dx.device_ptr(), tb.harmonics.device_ptr(), tb.off.device_ptr(), epochs as u64, h as u32, d0 as u32, tb.pad.device_ptr());
        // [the record of the two streams §11] A strand's level: an epoch's `δv⁻` is the chart of the covectors of the sites that read it (the
        // known sites of the epoch after it and the open places that stand in that epoch), through `B⁻`; the restriction returns to each
        // epoch's known sites alone (the host's `scale_return_before`).
        let (b, bb, own_epoch) = match (tr.before, tb.strand.as_ref()) {
            (Some((b2, bb2, _)), Some(tables)) => {
                let (mut lo1, mut hi1, mut lo2, mut hi2) = (tables.lo1.device_ptr(), tables.hi1.device_ptr(), tables.lo2.device_ptr(), tables.hi2.device_ptr());
                self.launch("field_level_chart64_spans", Self::cells((epochs * h * d0) as u64), THREADS, &mut [arg(words), arg(&mut src), arg(&mut hp), arg(&mut lo1), arg(&mut hi1), arg(&mut lo2), arg(&mut hi2), arg(&mut e64), arg(&mut h32), arg(&mut w32), arg(&mut dst)])?;
                (b2, bb2, tables.own.device_ptr())
            }
            (None, None) => {
                self.launch("field_level_chart64", Self::cells((epochs * h * d0) as u64), THREADS, &mut [arg(words), arg(&mut src), arg(&mut hp), arg(&mut op), arg(&mut e64), arg(&mut h32), arg(&mut w32), arg(&mut dst)])?;
                (b, bb, tb.epoch.device_ptr())
            }
            _ => return Err(TowerError::Refused("a strand's level's run and its batch's tables stand together")),
        };
        self.outer_biased(&mut tr.cwords, gg, b as u64, bb as u64, h * d0, d1, tb.pad.device_ptr(), h * d0, tb.read1.device_ptr(), d1, false, false)?;
        let mut gwords = tr.cwords;
        gwords.theta = tr.glue_at;
        self.transposed(&mut gwords, b as u64, h * d0, d1, tb.pad.device_ptr(), h * d0, cb.dr.device_ptr(), false, false)?;
        self.ratio_adjoint(&mut tr.cwords, tb.read1.device_ptr(), tb.scale1.device_ptr(), cb.dr.device_ptr(), 0, cb.dx.device_ptr(), false)?;
        // The level's ticks, in reverse.
        for (at, tick) in tb.ticks.iter().enumerate().rev() {
            self.tick_back(&s.coarse, &mut tr.cwords, tick, at, cg, cb, cb.dm.device_ptr(), epochs, false)?;
        }
        // The restriction: `δb_A`, `δA` and `δm = Aᵀ δx¹`, each place's part at its own phase through its read's adjoint into `δx`.
        self.outer_biased(&mut tr.cwords, gg, a as u64, ab as u64, d1, h * d0, cb.dx.device_ptr(), d1, tb.restricted.device_ptr(), h * d0, true, false)?;
        let mut gwords = tr.cwords;
        gwords.theta = tr.glue_at;
        self.transposed(&mut gwords, a as u64, d1, h * d0, cb.dx.device_ptr(), d1, tb.pad.device_ptr(), false, false)?;
        let (mut vp, mut hp, mut ep, mut h32, mut w32, mut dst, mut add) = (tb.pad.device_ptr(), tb.harmonics.device_ptr(), own_epoch, h as u32, d0 as u32, back.dr.device_ptr(), 0u32);
        self.launch("field_level_unchart", Self::cells((tb_fine_sites(words) * d0) as u64), THREADS, &mut [arg(words), arg(&mut vp), arg(&mut hp), arg(&mut ep), arg(&mut h32), arg(&mut w32), arg(&mut dst), arg(&mut add)])?;
        self.ratio_adjoint(words, tb.split_read.device_ptr(), tb.split_scale.device_ptr(), back.dr.device_ptr(), back.dx.device_ptr(), back.dx.device_ptr(), false)
    }
}
