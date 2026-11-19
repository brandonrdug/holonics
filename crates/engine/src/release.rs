//! **Reading until agreement, and writing.**
//!
//! the writer opens every answer place beside the known prompt and resolves them by octaves of distance from it, one place a
//! read, each drawn from its face on the region as it stands; its refine passes reread each place with every other standing
//!
//! Kind: chain over the reads. Kernels: the forward's kernels, one read a place.
//! Lean: `HNN/ReleaseRun`.
//! Atlas: `hnn.field-residual-half-rank`, `tower.field-exchange-walk`, `tower.field-reach-census`, `tower.field-redraw`, `tower.field-ring-census`,
//! `tower.field-ring-tilt`, `tower.field-settle`, `tower.field-state-charge`, `tower.field-write-by-the-training-clock`.
//! Records: `2026-11-01_THE_PROBLEM_IS_ONE_FIELD…`, `2026-11-13_THE_FIELD_RINGS…`, `2026-11-14_THE_MARK_IS…`. The derivations' history is in the
//! records; the items below keep their reasons.

#[allow(unused_imports)]
use crate::field::*;
#[allow(unused_imports)]
use rayon::prelude::*;

/// [measurement; agent-inferred, November 5, §16.47] **One read of the release** ([`Constitution::sample_observed`]): its index
/// (sweeps first, then the refine steps), its pass (zero for the sweeps, `p` for the `p`-th refine pass), and every
/// problem's classes, open places and faces as the read meets them (no faces at the release's end).
pub struct ReleaseRead<'a> {
    pub read: usize,
    pub pass: usize,
    pub classes: &'a [Vec<usize>],
    pub open: &'a [Vec<bool>],
    pub faces: Option<&'a [Vec<Option<TowerFace>>]>,
    /// [measurement; §16.47] The read's runs' certificate ([`Constitution::sample_runs`]): the entropies past each run's first place
    /// summed over the problems, read on this read's own faces, on the codes' `2^(−20)` bits (zero, one place a read), and
    /// the problems whose sum reached the run's bound (a refine run is chosen on its places' last draws, and passes the bound
    /// where a redraw moved a context).
    pub bound: i128,
    pub passed: usize,
}

impl Constitution {

    /// [definition; the ring record §4] The index of a mark's strength for the encoding at `base` ([`Loci::mark`]'s order).
    pub(crate) fn mark_base(&self, base: usize) -> usize {
        let l = &self.layout;
        if base == l.enc {
            0
        } else if base == l.before {
            1
        } else {
            2
        }
    }

    /// [definition; the ring record §4; G176] **The mark a silent site opens on**, with its strength on the material's grain: the law's where the
    /// field reads twice and `marks` (the second read's) holds the site's, at `α_b`; else the ruler's ([`Constitution::mark`], its `2^(−16)` strength
    /// carried to the material's grain); none at a resolved or carried site.
    pub(crate) fn marked<'m>(&'m self, region: &Region, base: usize, s: usize, marks: Option<&'m [Option<Shares>]>) -> Option<(i128, &'m Shares)> {
        if !region.unresolved[s] || Self::carried(region, s).is_some() {
            return None;
        }
        if let Some(law) = self.law_mark(region, base, s, marks) {
            return Some(law);
        }
        let (alpha, ruler) = self.mark.as_ref()?;
        Some((i128::from(*alpha) << (MATERIAL_BITS - STATE_BITS), ruler.get(s)?.as_ref()?))
    }

    /// The law's mark alone ([`Constitution::marked`]): where the field reads twice and the second read's `marks` holds the site's, at `α_b`.
    pub(crate) fn law_mark<'m>(&self, region: &Region, base: usize, s: usize, marks: Option<&'m [Option<Shares>]>) -> Option<(i128, &'m Shares)> {
        if !self.declaration.mark || !region.unresolved[s] || Self::carried(region, s).is_some() {
            return None;
        }
        let face = marks?.get(s)?.as_ref()?;
        Some((i128::from(self.theta[self.layout.mark + self.mark_base(base)]), face))
    }

    /// [definition; agent-inferred, November 14, G180] **The two reads' mean**: where the field reads twice, the section's summed covector of
    /// both reads ([`Constitution::returned`]) released by one bit, once, after every region is summed, so the bits are the partition's sum on any
    /// partition; at the founding the two reads' covectors are equal and the mean is either. Unchanged where the field reads once.
    pub fn both_reads_mean(&self, mut g: Vec<i128>) -> Vec<i128> {
        if self.declaration.mark {
            for x in g.iter_mut() {
                *x = release(*x, 1);
            }
        }
        g
    }

    /// [definition; theory, November 10 01:36] **The parallel certified settle**: the exchange walk's law and `h`
    /// ([`Constitution::exchange_walk`]: composition held, two places' letters exchanged, each place's face `f_t(· | rest)`, the
    /// answer's code `C = Σ_t −log₂ f_t(x_t)` on the codes' `2^(−20)` bits), many exchanges a pass. Each pass, in each active
    /// problem: (1) **propose** greedily by bare gain `g = c_i(x_i) + c_j(x_j) − c_i(x_j) − c_j(x_i)` on the current faces (the
    /// most first, then the nearer pair, then the earlier), every pair with `g > h` whose claim (the places within `NEAR − 1`
    /// of `i` and of `j`, the near field's reach) touches no place already claimed; (2) **keep by attribution**: every
    /// proposal applied, one re-read, each place's fall `c_t(x_t) − c′_t(x′_t)` attributed to the exchange that claimed it,
    /// the exchanges whose claimed places fell by more than `h` kept and the rest undone; (3) **certify the kept set whole**:
    /// re-read, `C` must fall by more than `h` × the kept exchanges; where it does not, the weaker half by attributed fall
    /// (`⌈n/2⌉`, agent-inferred: the fewest re-reads that still end) is undone and the set re-read, until certified or empty.
    /// A problem rests at a pass that keeps nothing. `pass` is shown each pass ([`SettlePass`], the pass before the first,
    /// then each) and the settle stops where it returns false: a problem still active there has not rested. Returns each
    /// problem's answer (its places past the question, the void past its letters) and its record.
    pub fn settle(&self, problems: &[(&[usize], usize)], written: &[Vec<usize>], void: usize, h: i128, realization: &mut dyn Realization, pass: &mut dyn FnMut(&SettlePass) -> bool) -> Result<(Vec<Vec<usize>>, Vec<SettleRecord>)> {
        let (out, records) = self.certified_passes(problems, written, void, h, false, 2, 1, false, &|_, _| {}, realization, &mut |_, x, f| exchange_proposals(x, f, h), pass)?;
        let records = records
            .into_iter()
            .map(|r| SettleRecord { places: r.places, start: r.start, end: r.end, kept: r.kept.iter().map(|m| ExchangeMove { i: m.at[0].0, j: m.at[1].0, gain: m.gain, fall: m.fall }).collect(), undone: r.undone, rested: r.rested })
            .collect();
        Ok((out, records))
    }

    /// [definition; theory, November 10 04:40] **The re-draws through a lens on the certificate** ([`Constitution::redraw`]'s law and
    /// stops): every face the walk reads (each answer's places and its stop place, the first void past its letters where the
    /// room holds it) passes through `lens` (the answer's letters and its faces in place order, the stop place's last), and the
    /// certificate's code is read on the lensed faces, the stop place's at the void among them; the proposals, `v`, the entropy
    /// and the neutrality read the lensed faces too. A lens is a function of the answer as it stands, so a change's attributed
    /// fall carries what it did to the lens at every claimed place.
    #[allow(clippy::too_many_arguments)]
    pub fn redraw_lensed(&self, problems: &[(&[usize], usize)], written: &[Vec<usize>], void: usize, h: i128, lens: &dyn Fn(&[usize], &mut [TowerFace]), realization: &mut dyn Realization, pass: &mut dyn FnMut(&SettlePass) -> bool) -> Result<(Vec<Vec<usize>>, Vec<CertifiedRecord>)> {
        self.certified_passes(problems, written, void, h, true, 1, 2, true, lens, realization, &mut |round, x, f| if round % 2 == 1 { redraw_proposals(x, f, void) } else { exchange_proposals(x, f, h) }, pass)
    }

    /// [definition; theory, November 10 04:15] **Point re-draws at the highest surprise, alternating with exchanges**: the
    /// odd passes re-draw ([`redraw_proposals`]: each place with `v_t = c_t(x_t) − H(f_t)` above a nat, the most first, to
    /// its face's top letter given the rest, where that letter's bare price `ln f_t(top) − ln f_t(x_t)` is at least a nat, the
    /// claims within `NEAR − 1` disjoint), the even passes exchange ([`exchange_proposals`], the settle's); each pass certified
    /// as the settle certifies ([`Constitution::settle`]: one re-read, each claim's attributed fall above `h` kept, the kept set's
    /// whole fall above `h` × the kept, the weaker half undone until it is). An answer stops at neutrality (its code at or under
    /// its faces' summed entropy) or where nothing stands in a re-draw pass and an exchange pass in a row; `pass` stops the
    /// whole. Returns each answer and its record.
    pub fn redraw(&self, problems: &[(&[usize], usize)], written: &[Vec<usize>], void: usize, h: i128, realization: &mut dyn Realization, pass: &mut dyn FnMut(&SettlePass) -> bool) -> Result<(Vec<Vec<usize>>, Vec<CertifiedRecord>)> {
        self.certified_passes(problems, written, void, h, true, 1, 2, false, &|_, _| {}, realization, &mut |round, x, f| if round % 2 == 1 { redraw_proposals(x, f, void) } else { exchange_proposals(x, f, h) }, pass)
    }

    /// [definition; theory, November 10 01:36 and 03:55] **The certified passes** [`Constitution::settle`] and [`Constitution::redraw`] share:
    /// each pass, each active problem's proposals (`propose`, from its letters and its locked faces: each a set of places and
    /// the letters they take, its bare gain, the claims of different proposals disjoint), all applied and read once, each
    /// place's fall attributed to the proposal whose claim (the places within `NEAR − 1` of a place it rewrites) holds it, the
    /// proposals whose claims fell by more than `h` kept and the rest undone, then the kept set certified whole on a re-read
    /// (its fall above `h` × the kept), its weaker half by attributed fall (`⌈n/2⌉`) undone and the set re-read until it is.
    /// `propose` is shown the pass's number. A problem of fewer than `least` letters rests where it is written; one rests after
    /// `cycle` passes in a row that keep nothing (one of each proposer); where `neutral`, one stops at neutrality (its code at or
    /// under its faces' summed entropy). [theory, November 10 04:40] Where `stop`, each answer's stop place (the first void past
    /// its letters, where the room holds it) is read and coded at the void beside its letters, inside the claims near it; every
    /// face read passes through `lens` (the answer and its faces in place order) before anything reads it.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn certified_passes(&self, problems: &[(&[usize], usize)], written: &[Vec<usize>], void: usize, h: i128, neutral: bool, least: usize, cycle: usize, stop: bool, lens: &dyn Fn(&[usize], &mut [TowerFace]), realization: &mut dyn Realization, propose: &mut dyn FnMut(usize, &[usize], &[TowerFace]) -> Vec<(Vec<(usize, usize)>, i128)>, pass: &mut dyn FnMut(&SettlePass) -> bool) -> Result<(Vec<Vec<usize>>, Vec<CertifiedRecord>)> {
        if written.len() != problems.len() {
            return refuse("a certified walk with one written answer a problem");
        }
        let reach = NEAR - 1;
        let letters: Vec<usize> = written.iter().map(|w| w.iter().take_while(|&&c| c != void).count()).collect();
        let mut answers: Vec<Vec<usize>> = written.iter().zip(&letters).map(|(w, &n)| w[..n].to_vec()).collect();
        // Each place's code at its letter, the stop place's (past the letters) at the void.
        let codes = |faces: &[TowerFace], x: &[usize]| -> Vec<i128> { faces.iter().enumerate().map(|(t, f)| f.code(x.get(t).copied().unwrap_or(void)) as i128).collect() };
        let summed = |faces: &[TowerFace]| -> i128 { faces.iter().map(entropy).sum() };
        let read = |answers: &[Vec<usize>], ks: &[usize], realization: &mut dyn Realization| -> Result<Vec<Vec<TowerFace>>> {
            let mut faces = self.locked_faces(problems, answers, ks, void, stop, realization)?;
            for (&k, f) in ks.iter().zip(faces.iter_mut()) {
                lens(&answers[k], f);
            }
            Ok(faces)
        };
        let everyone: Vec<usize> = (0..problems.len()).collect();
        let mut faces = read(&answers, &everyone, realization)?;
        let mut records: Vec<CertifiedRecord> = (0..problems.len())
            .map(|k| {
                let c = codes(&faces[k], &answers[k]).iter().sum();
                CertifiedRecord { places: letters[k], start: c, end: c, rested: letters[k] < least, ..CertifiedRecord::default() }
            })
            .collect();
        let mut active: Vec<bool> = letters.iter().map(|&n| n >= least).collect();
        let stand = |k: usize, faces: &[Vec<TowerFace>], answers: &[Vec<usize>], records: &mut [CertifiedRecord], active: &mut [bool]| {
            records[k].entropy = summed(&faces[k]);
            records[k].root = root_charge(&answers[k], &faces[k][..answers[k].len()]);
            if neutral && active[k] && records[k].end <= records[k].entropy {
                records[k].neutral = true;
                active[k] = false;
            }
        };
        for k in 0..problems.len() {
            stand(k, &faces, &answers, &mut records, &mut active);
        }
        #[allow(clippy::too_many_arguments)]
        fn report<'a>(rounds: usize, active: &[bool], records: &[CertifiedRecord], faces: &[Vec<TowerFace>], answers: &'a [Vec<usize>], kept: usize, undone: usize, outside: i128, changed: i128) -> SettlePass<'a> {
            let ln2 = crate::field::ln2_face();
            let past = |nats: i128| -> usize { faces.iter().zip(answers).map(|(f, x)| f.iter().zip(x).filter(|&(face, &a)| ((face.code(a) as i128 - entropy(face)) * ln2) >> 30 > nats << 20).count()).sum() };
            let (over, over2) = (past(1), past(2));
            SettlePass {
                pass: rounds,
                active: active.iter().filter(|&&a| a).count(),
                kept,
                undone,
                code: records.iter().map(|r| r.end).sum(),
                entropy: records.iter().map(|r| r.entropy).sum(),
                root: records.iter().map(|r| r.root).sum(),
                over,
                over2,
                places: answers.iter().map(Vec::len).sum(),
                kind: 0,
                outside,
                changed,
                answers,
            }
        }
        let mut go = pass(&report(0, &active, &records, &faces, &answers, 0, 0, 0, 0));
        let kind = |rounds: usize| rounds % cycle;
        let mut rounds = 0usize;
        let mut idle = vec![0usize; problems.len()];
        while go && active.iter().any(|&a| a) {
            rounds += 1;
            // (1) Each active problem's proposals, their claims disjoint; each place's claimant.
            let mut proposals: Vec<Vec<(Vec<(usize, usize, usize)>, i128)>> = vec![Vec::new(); problems.len()];
            let mut claim: Vec<Vec<Option<usize>>> = faces.iter().map(|f| vec![None; f.len()]).collect();
            for k in 0..problems.len() {
                if !active[k] {
                    continue;
                }
                let len = faces[k].len();
                for (n, (at, g)) in propose(rounds, &answers[k], &faces[k][..answers[k].len()]).into_iter().enumerate() {
                    for &(t, _) in &at {
                        for u in t.saturating_sub(reach)..=(t + reach).min(len - 1) {
                            if claim[k][u].is_some_and(|o| o != n) {
                                return refuse("a certified walk's proposals that share a claimed place");
                            }
                            claim[k][u] = Some(n);
                        }
                    }
                    let at = at.into_iter().map(|(t, to)| (t, answers[k][t], to)).collect();
                    proposals[k].push((at, g));
                }
                if proposals[k].is_empty() {
                    idle[k] += 1;
                    if idle[k] >= cycle {
                        records[k].rested = true;
                        active[k] = false;
                    }
                }
            }
            let ks: Vec<usize> = (0..problems.len()).filter(|&k| !proposals[k].is_empty()).collect();
            if ks.is_empty() {
                go = pass(&SettlePass { kind: kind(rounds), ..report(rounds, &active, &records, &faces, &answers, 0, 0, 0, 0) });
                continue;
            }
            let apply = |answers: &mut [Vec<usize>], k: usize, at: &[(usize, usize, usize)]| at.iter().for_each(|&(t, _, to)| answers[k][t] = to);
            let undo = |answers: &mut [Vec<usize>], k: usize, at: &[(usize, usize, usize)]| at.iter().for_each(|&(t, from, _)| answers[k][t] = from);
            // (2) Every proposal applied and read once; each place's fall attributed to its claimant.
            let before: Vec<Vec<i128>> = (0..problems.len()).map(|k| if proposals[k].is_empty() { Vec::new() } else { codes(&faces[k], &answers[k]) }).collect();
            for &k in &ks {
                for (at, _) in &proposals[k] {
                    apply(&mut answers, k, at);
                }
            }
            let reread = read(&answers, &ks, realization)?;
            let attributed = |k: usize, now: &[i128], n: usize| -> Vec<i128> {
                let mut fall = vec![0i128; n];
                for (t, owner) in claim[k].iter().enumerate() {
                    if let Some(p) = owner {
                        fall[*p] += before[k][t] - now[t];
                    }
                }
                fall
            };
            let (mut kept_all, mut undone_all, mut outside, mut changed) = (0usize, 0usize, 0i128, 0i128);
            let mut now_faces: Vec<Option<Vec<TowerFace>>> = vec![None; problems.len()];
            let mut kept: Vec<Vec<usize>> = vec![Vec::new(); problems.len()];
            for (&k, after) in ks.iter().zip(reread) {
                let now = codes(&after, &answers[k]);
                for (t, owner) in claim[k].iter().enumerate() {
                    let delta = (before[k][t] - now[t]).abs();
                    changed += delta;
                    if owner.is_none() {
                        outside += delta;
                    }
                }
                let fall = attributed(k, &now, proposals[k].len());
                for (p, (at, _)) in proposals[k].iter().enumerate() {
                    if fall[p] > h {
                        kept[k].push(p);
                    } else {
                        undo(&mut answers, k, at);
                        undone_all += 1;
                    }
                }
                if kept[k].len() == proposals[k].len() {
                    now_faces[k] = Some(after);
                }
            }
            // (3) Each kept set certified whole, its weaker half undone until it is.
            let mut pending: Vec<usize> = ks.iter().copied().filter(|&k| !kept[k].is_empty()).collect();
            while !pending.is_empty() {
                let stale: Vec<usize> = pending.iter().copied().filter(|&k| now_faces[k].is_none()).collect();
                for (&k, f) in stale.iter().zip(read(&answers, &stale, realization)?) {
                    now_faces[k] = Some(f);
                }
                let mut next = Vec::new();
                for k in pending {
                    let f = now_faces[k].take().ok_or(TowerError::Refused("a certified walk's kept set without its read"))?;
                    let now = codes(&f, &answers[k]);
                    let c: i128 = now.iter().sum();
                    let fall = attributed(k, &now, proposals[k].len());
                    if records[k].end - c > h * kept[k].len() as i128 {
                        for &p in &kept[k] {
                            let (at, g) = &proposals[k][p];
                            records[k].kept.push(CertifiedMove { at: at.clone(), gain: *g, fall: fall[p] });
                        }
                        kept_all += kept[k].len();
                        records[k].end = c;
                        faces[k] = f;
                        continue;
                    }
                    let mut by: Vec<usize> = kept[k].clone();
                    by.sort_by_key(|&p| (fall[p], p));
                    let weak = by.len().div_ceil(2);
                    for &p in &by[..weak] {
                        undo(&mut answers, k, &proposals[k][p].0);
                    }
                    undone_all += weak;
                    kept[k] = by[weak..].to_vec();
                    kept[k].sort_unstable();
                    if !kept[k].is_empty() {
                        next.push(k);
                    }
                }
                pending = next;
            }
            for &k in &ks {
                records[k].undone += proposals[k].len() - kept[k].len();
                if kept[k].is_empty() {
                    idle[k] += 1;
                    if idle[k] >= cycle {
                        records[k].rested = true;
                        active[k] = false;
                    }
                } else {
                    idle[k] = 0;
                    stand(k, &faces, &answers, &mut records, &mut active);
                }
            }
            go = pass(&SettlePass { kind: kind(rounds), ..report(rounds, &active, &records, &faces, &answers, kept_all, undone_all, outside, changed) });
        }
        let out = answers.iter().zip(written).map(|(a, w)| {
            let mut placed = a.clone();
            placed.extend(std::iter::repeat_n(void, w.len() - a.len()));
            placed
        }).collect();
        Ok((out, records))
    }

    /// [measurement; theory, November 10 02:03] **Every face of the answers `ks` with every other place locked**
    /// (the exchange walks' read on main, kept for the transmission readings when the field was reset to the line, November 11), and with `stop` also the stop place, the first void past the
    /// letters, where the room holds it (its face last); in the order of `ks`.
    pub fn locked_faces(&self, problems: &[(&[usize], usize)], answers: &[Vec<usize>], ks: &[usize], void: usize, stop: bool, realization: &mut dyn Realization) -> Result<Vec<Vec<TowerFace>>> {
        let region_of = |k: usize, answer: &[usize]| -> Vec<usize> {
            let (q, room) = problems[k];
            let mut classes: Vec<usize> = q.iter().chain(answer).copied().collect();
            classes.extend(std::iter::repeat_n(void, NEAR.min(room.saturating_sub(answer.len()))));
            classes
        };
        let places: Vec<(usize, usize)> = ks.iter().flat_map(|&k| (0..answers[k].len() + usize::from(stop && problems[k].1 > answers[k].len())).map(move |i| (k, i))).collect();
        let owned: Vec<(Vec<usize>, Vec<bool>)> = places
            .iter()
            .map(|&(k, i)| {
                let classes = region_of(k, &answers[k]);
                let at = problems[k].0.len() + i;
                let open = (0..classes.len()).map(|t| t == at).collect();
                (classes, open)
            })
            .collect();
        let regions: Vec<Region> = owned.iter().map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false }).collect();
        let faces = if regions.is_empty() { Vec::new() } else { realization.read_faces(self, &regions)? };
        let mut out: Vec<Vec<TowerFace>> = ks.iter().map(|_| Vec::new()).collect();
        let at: std::collections::BTreeMap<usize, usize> = ks.iter().enumerate().map(|(n, &k)| (k, n)).collect();
        for (f, &(k, i)) in faces.into_iter().zip(&places) {
            out[at[&k]].push(f.get(problems[k].0.len() + i).cloned().flatten().ok_or(TowerError::Refused("an exchange walk's open place without a face"))?);
        }
        Ok(out)
    }

    /// Each region's unresolved sites' logits, read in parallel.
    pub fn read_logits(&self, regions: &[Region]) -> Result<Vec<ReadLogits>> {
        regions.par_iter().map(|r| self.pass(r, false).map(|p| ReadLogits { logits: p.logits, echo: p.echo })).collect()
    }

    /// A site's face at its pump: over every class before the extent is read, over every class but the
    /// void after it.
    /// [definition; agent-inferred, November 3, §16.27, the comparison record's §3.3] **The release by the training clock run
    /// backwards**: training reads a region whose open sites are a uniform state of a random reading order (§16.23); the
    /// release runs that clock backwards. Every answer place opens unresolved beside its known question; over `sweeps`
    /// sweeps the open places are resolved by octaves of their distance from the question, each octave in its keyed order
    /// once the earlier octaves are resolved (§16.47), about `n/sweeps` a sweep, each drawn from its own
    /// face at temperature one (the field's own probabilities, an exact integer draw against the face's masses) on the read
    /// of the region as it stands, with every place resolved before it known. No place is chosen by its certainty, nothing
    /// is left open, and a place drawn as the void closes the answer there: every place past it is resolved as the void,
    /// so the region stays an answer and its void tail, the only states training reads (§16.35). Returns each problem's
    /// answer places' classes, in place order, and stops early (every place it did not reach drawn on its last read) where
    /// `sweep` says to. `refine` passes then revisit the written answer, one place at a time (§16.36, §16.47); zero writes it once.
    pub fn sample_realized(&self, problems: &[(&[usize], usize)], sweeps: usize, refine: usize, void: usize, seed: u64, realization: &mut dyn Realization, sweep: &mut dyn FnMut(usize, usize) -> bool) -> Result<Vec<Vec<usize>>> {
        self.sample_observed(problems, sweeps, refine, void, seed, realization, sweep, &mut |_| {})
    }

    /// [agent-inferred, November 5] **A release's read of the problems it still writes**: only the `active` problems' regions
    /// are read (a problem with no place this read is left out), and their faces are returned at their own problems'
    /// places, every other problem's empty. A region's faces are its own (each region is read alone), so the answers are the
    /// same bits; a finished problem no longer takes a region's read (the unified-theory reading of November 5, 17:41: about
    /// 60% of a 32-answer write's region reads were of finished problems).
    ///
    /// [definition; agent-inferred, November 5, the unified-theory reading of 22:38] With `near_tail`, **the writer's region ends
    /// `NEAR` places past its lowest resolved void**, as every training region and the withheld read do: the places past it are
    /// the void, resolved, and no field trained under the near tail met them (a refine pass redrew each place beside up to
    /// 2,000 of them). Its faces past the cut are none; every open place stands before it.
    pub(crate) fn read_active(&self, starts: &[usize], classes: &[Vec<usize>], open: &[Vec<bool>], active: &[usize], void: usize, near_tail: bool, realization: &mut dyn Realization) -> Result<Vec<Vec<Option<TowerFace>>>> {
        let cut = |k: usize| -> usize {
            let len = classes[k].len();
            match (near_tail, (starts[k]..len).find(|&t| !open[k][t] && classes[k][t] == void)) {
                (true, Some(end)) => (end + NEAR).min(len),
                _ => len,
            }
        };
        let regions: Vec<Region> = active.iter().map(|&k| Region { classes: &classes[k][..cut(k)], unresolved: &open[k][..cut(k)], faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false }).collect();
        let mut faces: Vec<Vec<Option<TowerFace>>> = vec![Vec::new(); classes.len()];
        if regions.is_empty() {
            return Ok(faces);
        }
        for (mut read, &k) in realization.read_faces(self, &regions)?.into_iter().zip(active) {
            read.resize(classes[k].len(), None);
            faces[k] = read;
        }
        Ok(faces)
    }

    /// [definition; theory, November 16 20:39Z, Build B's refine] **An act's draft redrawn once, place by place, its predicted reaction known.**
    /// Problem `k` is the prompt `prompts[k]` and the run `written[k]` the release wrote after it; its first `drafts[k]` places are the draft. The
    /// draft's places are opened (silent, as every open place is) and the rest of the run, the field's own predicted reaction, stays written.
    /// At each read every problem with a draft place left redraws one: the place whose written symbol carries the most news under the read's
    /// faces (the earlier at equal news), which is the landmark order on places' news (atlas `code.site-isolation-landmark`), never a face's top.
    /// It is drawn as the release draws a letter, by a keyed uniform against the face's masses with the void left out, and stands resolved for
    /// the next read. Each draft place is redrawn once, so a problem takes as many reads as its draft has places. Returns each run with its
    /// draft redrawn. Why: an open place is silent, so the predicted reaction can pull on the draft only once the draft is reopened with the
    /// reaction written; the pull comes from the passage alone (the field drafts in the world's form, and a draft redrawn before a value
    /// draws toward forms that precede a value), with no goal from outside and no selection.
    #[allow(clippy::too_many_arguments)]
    pub fn refine_drafts(&self, prompts: &[&[usize]], written: &[Vec<usize>], drafts: &[usize], void: usize, seed: u64, realization: &mut dyn Realization) -> Result<Vec<Vec<usize>>> {
        if prompts.len() != written.len() || prompts.len() != drafts.len() || drafts.iter().zip(written).any(|(&d, w)| d > w.len()) || void >= self.declaration.alphabet {
            return refuse("drafts to refine that are not one a problem within its run, or a void outside the alphabet");
        }
        let mix = |counter: u64| -> u64 {
            let mut z = seed.wrapping_add(counter.wrapping_mul(0x9E37_79B9_7F4A_7C15));
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        };
        let starts: Vec<usize> = prompts.iter().map(|q| q.len()).collect();
        let mut classes: Vec<Vec<usize>> = prompts.iter().zip(written).map(|(q, w)| q.iter().copied().chain(w.iter().copied()).collect()).collect();
        let mut open: Vec<Vec<bool>> = classes.iter().map(|c| vec![false; c.len()]).collect();
        let mut left: Vec<Vec<usize>> = (0..prompts.len()).map(|k| (starts[k]..starts[k] + drafts[k]).collect()).collect();
        let held: Vec<Vec<usize>> = classes.clone();
        for (k, places) in left.iter().enumerate() {
            for &t in places {
                open[k][t] = true;
                classes[k][t] = void;
            }
        }
        let mut read = 0u64;
        loop {
            let active: Vec<usize> = (0..prompts.len()).filter(|&k| !left[k].is_empty()).collect();
            if active.is_empty() {
                break;
            }
            let faces = self.read_active(&starts, &classes, &open, &active, void, true, realization)?;
            for &k in &active {
                let mut pick: Option<(usize, i64)> = None;
                for (i, &t) in left[k].iter().enumerate() {
                    let face = faces[k][t].as_ref().ok_or(TowerError::Refused("a draft's open place without a face"))?;
                    let news = face.code(held[k][t]);
                    if pick.is_none_or(|(_, best)| news > best) {
                        pick = Some((i, news));
                    }
                }
                let Some((i, _)) = pick else { continue };
                let t = left[k].remove(i);
                let face = faces[k][t].as_ref().ok_or(TowerError::Refused("a draft's open place without a face"))?;
                let u = ((mix(((k as u64) << 40) ^ ((t as u64) << 8) ^ (read << 56) ^ 0x1D) as u128) << 64) | mix(((k as u64) << 40) ^ ((t as u64) << 8) ^ (read << 56) ^ 0x1E) as u128;
                let letters = face.total - face.masses[void];
                classes[k][t] = if letters == 0 {
                    held[k][t]
                } else {
                    let u = u % letters;
                    let mut acc = 0u128;
                    (0..face.masses.len()).filter(|&c| c != void).find(|&c| {
                        acc += face.masses[c];
                        acc > u
                    }).unwrap_or(held[k][t])
                };
                open[k][t] = false;
            }
            read += 1;
        }
        Ok(classes.iter().zip(&starts).map(|(c, &q)| c[q..].to_vec()).collect())
    }

    /// [measurement; agent-inferred, November 5, §16.47] **The release, read as it writes** ([`Constitution::sample_realized`],
    /// draw for draw): `observe` is shown every read the release makes (each sweep's and each refine step's), with every
    /// problem's classes, open places and faces as that read meets them, before its draws, and once more at the end with no
    /// faces. A reading only: nothing in the release reads it.
    #[allow(clippy::too_many_arguments)]
    pub fn sample_observed(&self, problems: &[(&[usize], usize)], sweeps: usize, refine: usize, void: usize, seed: u64, realization: &mut dyn Realization, sweep: &mut dyn FnMut(usize, usize) -> bool, observe: &mut dyn FnMut(ReleaseRead)) -> Result<Vec<Vec<usize>>> {
        self.release(problems, sweeps, refine, void, seed, 0, true, false, None, false, realization, sweep, observe)
    }

    /// [definition; agent-inferred, November 5, the unified-theory reading of 17:41, its bound read without a maximum]
    /// **A read releases a run** ([`Constitution::sample_observed`] with `run_bound` on the codes' `2^(−20)` bits; zero, one place a
    /// read): past each read's free places, the walk releases each next open place of its order (within the octave in the
    /// sweeps) while the entropies of the places it adds, read on this read's faces, sum within `run_bound`; a refine pass's
    /// run reopens the next places of its order whose entropies at their last draw sum so, and draws them all from one
    /// read. Drawing a run from one read loses at most `ΣH − H_joint` of its joint, its total correlation, and since the
    /// joint holds at least the first place's entropy that is at most the added places' sum, so `run_bound` bounds the
    /// loss with no place chosen by its certainty: certainty sets only how long the run is. Why: one place a read made a
    /// write of 32 answers about 3,000 full reads; a place whose face is nearly settled adds almost nothing to the joint's
    /// loss when it is drawn beside the run's first.
    #[allow(clippy::too_many_arguments)]
    /// `near_tail` is the writer's region law ([`Constitution::read_active`]); `false` declares the whole room for comparison.
    /// `place_order` draws each octave's places in place order rather than its keyed order. [agent-inferred, November 6, the
    /// unified-theory reading of 03:08] `lengths`, where given, fixes each answer's length: its places past it stand resolved as
    /// the void from the first read (so the region is the question, the answer and its near tail), and every answer place,
    /// in the sweeps and in refine, draws from its face over the letters; the end never moves. `one_end` draws each answer's
    /// length from the release's first read when none is given ([`Constitution::release`]).
    pub fn sample_runs(&self, problems: &[(&[usize], usize)], sweeps: usize, refine: usize, void: usize, seed: u64, run_bound: i128, near_tail: bool, place_order: bool, lengths: Option<&[usize]>, one_end: bool, realization: &mut dyn Realization, sweep: &mut dyn FnMut(usize, usize) -> bool, observe: &mut dyn FnMut(ReleaseRead)) -> Result<Vec<Vec<usize>>> {
        self.release(problems, sweeps, refine, void, seed, run_bound, near_tail, place_order, lengths, one_end, realization, sweep, observe)
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn release(&self, problems: &[(&[usize], usize)], sweeps: usize, refine: usize, void: usize, seed: u64, run_bound: i128, near_tail: bool, place_order: bool, lengths: Option<&[usize]>, one_end: bool, realization: &mut dyn Realization, sweep: &mut dyn FnMut(usize, usize) -> bool, observe: &mut dyn FnMut(ReleaseRead)) -> Result<Vec<Vec<usize>>> {
        if sweeps == 0 || void >= self.declaration.alphabet || problems.iter().any(|&(_, n)| n == 0) {
            return refuse("a sample needs a sweep, an answer place and a void class in the alphabet");
        }
        let mix = |counter: u64| -> u64 {
            let mut z = seed.wrapping_add(counter.wrapping_mul(0x9E37_79B9_7F4A_7C15));
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        };
        let starts: Vec<usize> = problems.iter().map(|&(q, _)| q.len()).collect();
        let mut classes: Vec<Vec<usize>> = problems.iter().map(|&(q, n)| q.iter().copied().chain(std::iter::repeat_n(void, n)).collect()).collect();
        let mut open: Vec<Vec<bool>> = problems.iter().map(|&(q, n)| (0..q.len() + n).map(|t| t >= q.len()).collect()).collect();
        // [definition; agent-inferred, November 6, the unified-theory reading of 04:03] With `one_end`, **one end, one draw**: at
        // the release's first read (every answer place open, training's fully masked state) a place `d` is the void exactly when
        // the answer is shorter than `d`, so its void mass is the field's `P(L < d | q)`, the length's distribution; the end is
        // one uniform `u` against that profile, the answer's length the places before the first whose void mass passes `u` (an
        // exact integer comparison), and the sweeps then write given it. One `u`, not one draw a place: independent draws
        // multiply survivals, and the earliest void drawn is not the profile's draw.
        //
        // [definition; agent-inferred, November 6, the unified-theory reading of 07:21] **The draw is conditioned on the room**:
        // the answer ends within it, so `P(L ≤ t | L ≤ R) = M(t)/M(R)`, `M` the running maximum of the void mass and `R` the
        // room's last place; the end is the first place whose void mass passes `u M(R)`, read as `m_∅(t) T_R 2^32 > u m_R T_t`
        // on 256-bit products (`m_R/T_R` the profile's largest void mass). Why: unconditioned, every `u` above the void mass at the
        // room's last place landed there, so the opening's shortfall from one was drawn as length (code91: about 22 places of
        // letter mass past 1,200 on held and training alike, where the length law holds under one).
        let drawn_lengths: Option<Vec<usize>> = if one_end && lengths.is_none() {
            let active: Vec<usize> = (0..problems.len()).collect();
            let faces = self.read_active(&starts, &classes, &open, &active, void, near_tail, realization)?;
            Some(
                problems
                    .iter()
                    .enumerate()
                    .map(|(k, &(q, n))| {
                        let u = mix(((k as u64) << 40) ^ 0x0E4D) as u32 as u128;
                        let room: Vec<Option<&TowerFace>> = (0..n).map(|j| faces[k][q.len() + j].as_ref()).collect();
                        one_end_length(&room, void, u)
                    })
                    .collect(),
            )
        } else {
            None
        };
        let lengths = lengths.or(drawn_lengths.as_deref());
        let given = lengths.is_some();
        if let Some(ls) = lengths {
            if ls.len() != problems.len() {
                return refuse("a given length for each problem");
            }
            for (k, &(q, _)) in problems.iter().enumerate() {
                for slot in open[k].iter_mut().skip(q.len() + ls[k]) {
                    *slot = false;
                }
            }
        }
        // [definition; agent-inferred, November 5, §16.47] **The answer is released by octaves of its distance from the
        // question** (the unified-theory reading of 15:04): octave `j` holds the places at distance `[2^j, 2^(j+1))` past
        // the question (the first place at distance one), and its places open to the draws only once every place of the
        // earlier octaves is resolved; within an octave the keyed order. Why: with exact faces every order draws the same
        // joint, but with the field's the order decides what the end reads, and drawn in one keyed order of the whole
        // extent the end was fixed in the first reads while nearly every place was open (95% of the length's drift in
        // reads 1 to 64), so the written length barely heard the problem (its bytes correlated +0.18 with the held); by
        // octaves the end is drawn reading at least half its answer as written.
        let orders: Vec<Vec<usize>> = problems
            .iter()
            .enumerate()
            .map(|(k, &(q, n))| {
                // [definition; agent-inferred, November 6, the unified-theory reading of 00:14] With `place_order`, **the octave
                // law at every byte**: the order decides what each draw reads, and by octaves the end reads at least half its
                // answer as written; measured from the writer's own front the same reason orders every place, so each octave
                // is drawn in place order (the keyed order within an octave was the one grain where the law was dropped, a
                // byte drawn with every neighbour blank coding about 5 bits against 1.4 beside them). Runs stay.
                let mut order: Vec<usize> = (q.len()..q.len() + n).collect();
                if !place_order {
                    order.sort_by_key(|&t| (octave_of(t + 1 - q.len()), mix(((k as u64) << 32) ^ t as u64 ^ (1 << 62)), t));
                }
                order
            })
            .collect();
        // Each problem's place in its order: a sweep draws its next open places, never past its octave (the last sweep
        // draws every place left), so a place the closing law has resolved costs no read.
        let mut cursors = vec![0usize; problems.len()];
        // Each place's entropy at its last draw, for a refine pass's runs (none where the closing law resolved it).
        let mut drawn_entropy: Vec<Vec<Option<i128>>> = classes.iter().map(|c| vec![None; c.len()]).collect();
        let mut swept = sweeps;
        for done in 0..sweeps {
            let last = done + 1 == sweeps || !sweep(done, sweeps);
            let active: Vec<usize> = (0..problems.len()).filter(|&k| open[k].iter().any(|&u| u)).collect();
            let faces = self.read_active(&starts, &classes, &open, &active, void, near_tail, realization)?;
            let (mut bound, passed) = (0i128, 0usize);
            let mut runs: Vec<Vec<usize>> = Vec::with_capacity(problems.len());
            for (k, &(q, n)) in problems.iter().enumerate() {
                let count = if last { n } else { (done + 1) * n / sweeps - done * n / sweeps };
                let mut picked: Vec<usize> = Vec::new();
                while let Some(&t) = orders[k].get(cursors[k]) {
                    if picked.len() == count || (!last && picked.first().is_some_and(|&p| octave_of(p + 1 - q.len()) != octave_of(t + 1 - q.len()))) {
                        break;
                    }
                    cursors[k] += 1;
                    if open[k][t] {
                        picked.push(t);
                    }
                }
                // The run past the free places: the next open places of the octave while their entropies sum within the bound.
                if run_bound > 0 && !last && !picked.is_empty() {
                    let mut held = 0i128;
                    while let Some(&t) = orders[k].get(cursors[k]) {
                        if octave_of(picked[0] + 1 - q.len()) != octave_of(t + 1 - q.len()) {
                            break;
                        }
                        if !open[k][t] {
                            cursors[k] += 1;
                            continue;
                        }
                        let h = entropy(faces[k][t].as_ref().ok_or(TowerError::Refused("a sample's open place without a face"))?);
                        // Strictly within the bound: below one bit the places past the first hold one configuration with more
                        // than half their mass, so the read makes one choice (at one bit a fair coin can stand there).
                        if held + h >= run_bound {
                            break;
                        }
                        held += h;
                        cursors[k] += 1;
                        picked.push(t);
                    }
                    bound += held;
                }
                runs.push(picked);
            }
            observe(ReleaseRead { read: done, pass: 0, classes: &classes, open: &open, faces: Some(&faces), bound, passed });
            // [definition; agent-inferred, November 5, the unified-theory reading of 22:38] **A void never unwrites a letter**: in
            // the sweeps as in refine, a place before the last written letter draws from its face restricted to the letters
            // (the void's mass removed, an exact integer draw against the rest), and only a place past every letter draws
            // from its whole face, so the void is drawn only where it closes nothing written. A read's places are drawn from
            // the farthest in, each beside the letters drawn past it this read. Exact faces are unchanged (the truth's void
            // has no mass before its last letter). A face before the last letter with no letter mass draws its whole face.
            // Why: within an octave the keyed order puts most draws before a written letter (93% in octave 6, 96% in octave
            // 7), the field's void there is a residue of about 1% that costs training 0.014 bits a place, and each such
            // draw ended the answer there: a flat hazard deaf to held (b1's write, one in 110 places at or under held and
            // past it alike, 23 of its 28 short writes cut by a void that unwrote letters).
            let mut draws: Vec<(usize, usize, usize)> = Vec::new();
            for (k, picked) in runs.iter().enumerate() {
                let q = problems[k].0.len();
                let mut last_letter = (q..classes[k].len()).rev().find(|&t| !open[k][t] && classes[k][t] != void);
                let mut far_first = picked.clone();
                far_first.sort_unstable_by(|a, b| b.cmp(a));
                for &t in &far_first {
                    let face = faces[k][t].as_ref().ok_or(TowerError::Refused("a sample's open place without a face"))?;
                    drawn_entropy[k][t] = Some(entropy(face));
                    let u = ((mix(((k as u64) << 40) ^ ((t as u64) << 8) ^ 0xD) as u128) << 64) | mix(((k as u64) << 40) ^ ((t as u64) << 8) ^ 0xE) as u128;
                    let letters = face.total - face.masses[void];
                    let c = if (given || last_letter.is_some_and(|l| t < l)) && letters > 0 {
                        let u = u % letters;
                        let mut acc = 0u128;
                        (0..face.masses.len()).filter(|&c| c != void).find(|&c| {
                            acc += face.masses[c];
                            acc > u
                        })
                    } else {
                        let u = u % face.total;
                        let mut acc = 0u128;
                        face.masses.iter().position(|&m| {
                            acc += m;
                            acc > u
                        })
                    };
                    let c = c.unwrap_or(face.masses.len() - 1);
                    if c != void && last_letter.is_none_or(|l| t > l) {
                        last_letter = Some(t);
                    }
                    draws.push((k, t, c));
                }
            }
            for (k, t, c) in draws {
                classes[k][t] = c;
                open[k][t] = false;
            }
            // [definition; agent-inferred, November 3, §16.35] The void is the class past an answer's end, so a place drawn
            // as the void is the answer's boundary: every place past it is the void, resolved, as in every state training
            // reads (an answer, then its void tail). The boundary only moves in; a letter drawn past it is past the end.
            for (k, &(q, _)) in problems.iter().enumerate() {
                if let Some(end) = (q.len()..classes[k].len()).find(|&t| !open[k][t] && classes[k][t] == void) {
                    for t in end + 1..classes[k].len() {
                        classes[k][t] = void;
                        open[k][t] = false;
                    }
                }
            }
            if last {
                if done + 1 < sweeps {
                    observe(ReleaseRead { read: done + 1, pass: 0, classes: &classes, open: &open, faces: None, bound: 0, passed: 0 });
                    return Ok(problems.iter().enumerate().map(|(k, &(q, _))| classes[k][q.len()..].to_vec()).collect());
                }
                break;
            }
            // Every place resolved: the sweeps are done.
            if open.iter().all(|o| o.iter().all(|&u| !u)) {
                swept = done + 1;
                break;
            }
        }
        // [definition; agent-inferred, November 3, §16.36; November 5, §16.47] **The places keep moving** (the lens of
        // November 1: an answer is a joint field whose parts move together until its faces align, never committed
        // surest-first): after every place is written, `refine` passes revisit the answer, the field's own one-place
        // resampling. Each pass walks each problem's keyed order of all its answer places, one place of each problem a
        // read, passing over a place that stands past the boundary (the first void) when its turn comes, so an end that has
        // moved is met again. A revisited place is opened again, read beside every other place as it now stands, and drawn
        // at temperature one: a place before the last letter from its face restricted to the letters (the void's mass
        // removed, an exact integer draw against the rest), the last letter and the boundary place from their whole faces,
        // so the end moves one place in or out a draw and the closing law holds after every draw. Why (the unified-theory
        // reading of November 5, 14:47): drawn from the whole face, a void inside erased every later letter while a
        // boundary drawn as a letter moved out one place, the new boundary waiting for the next pass, so the passes cut
        // deep and grew by one (segment 2's −4.8 places came all in its third pass, from its 14 short answers). A place
        // before the last letter whose face holds no letter mass keeps the letter it had. No place is chosen by its
        // certainty. [agent-inferred, November 6, the unified-theory reading of 00:13] The passes stop where the answer's
        // redrawn code per byte reaches real text's on this field (the walk helps only while the answer is more surprising to
        // the field than the truth is); the withheld code reads it from above, and on code86's state the passes cross it
        // between passes 3 and 4, so `refine = 3` stands for that stop. A stop on the faces' own level (held letters at least
        // as likely as draws) was built and retired: these faces are no joint's conditionals, so the walk descends
        // without pausing (to spaces and short strings over tens of passes, §16.47's settle93).
        let mut read = swept;
        let total = swept + refine * problems.iter().map(|&(_, n)| n).max().unwrap_or(0);
        let boundary = |classes: &[usize], open: &[bool], q: usize| (q..classes.len()).find(|&t| classes[t] == void && !open[t]).unwrap_or(classes.len());
        let mut pass = 0u64;
        while (pass as usize) < refine {
            pass += 1;
            let orders: Vec<Vec<usize>> = problems
                .iter()
                .enumerate()
                .map(|(k, &(q, _))| {
                    let mut order: Vec<usize> = (q.len()..classes[k].len()).collect();
                    order.sort_by_key(|&t| (mix(((k as u64) << 32) ^ t as u64 ^ (pass << 48) ^ (1 << 62)), t));
                    order
                })
                .collect();
            let mut cursors = vec![0usize; problems.len()];
            loop {
                // Each problem's next place in its order standing at or before its boundary, beside that boundary, and the run
                // past it: the next places at or before the boundary whose entropies at their last draw sum within the bound.
                let mut places: Vec<Option<(Vec<usize>, usize)>> = vec![None; problems.len()];
                for (k, &(q, _)) in problems.iter().enumerate() {
                    let end = boundary(&classes[k], &open[k], q.len());
                    while let Some(&t) = orders[k].get(cursors[k]) {
                        cursors[k] += 1;
                        if t < end || (!given && t == end) {
                            places[k] = Some((vec![t], end));
                            break;
                        }
                    }
                    if let (true, Some((run, _))) = (run_bound > 0, places[k].as_mut()) {
                        let mut held = 0i128;
                        while let Some(&t) = orders[k].get(cursors[k]) {
                            if t > end || (given && t == end) {
                                cursors[k] += 1;
                                continue;
                            }
                            let Some(h) = drawn_entropy[k][t] else { break };
                            if held + h >= run_bound {
                                break;
                            }
                            held += h;
                            cursors[k] += 1;
                            run.push(t);
                        }
                    }
                }
                if places.iter().all(Option::is_none) {
                    break;
                }
                if !sweep(read, total) {
                    observe(ReleaseRead { read, pass: pass as usize, classes: &classes, open: &open, faces: None, bound: 0, passed: 0 });
                    return Ok(problems.iter().enumerate().map(|(k, &(q, _))| classes[k][q.len()..].to_vec()).collect());
                }
                read += 1;
                let mut kept: Vec<Vec<usize>> = vec![Vec::new(); problems.len()];
                for (k, place) in places.iter().enumerate() {
                    if let Some((run, _)) = place {
                        for &t in run {
                            kept[k].push(classes[k][t]);
                            open[k][t] = true;
                            classes[k][t] = void;
                        }
                    }
                }
                let active: Vec<usize> = (0..problems.len()).filter(|&k| places[k].is_some()).collect();
                let faces = self.read_active(&starts, &classes, &open, &active, void, near_tail, realization)?;
                // What the read certifies is its own faces' sum past each run's first place.
                let (mut bound, mut passed) = (0i128, 0usize);
                for (k, place) in places.iter().enumerate() {
                    if let Some((run, _)) = place {
                        let mut held = 0i128;
                        for &t in &run[1..] {
                            held += entropy(faces[k][t].as_ref().ok_or(TowerError::Refused("a sample's open place without a face"))?);
                        }
                        bound += held;
                        passed += usize::from(run_bound > 0 && held >= run_bound);
                    }
                }
                observe(ReleaseRead { read: read - 1, pass: pass as usize, classes: &classes, open: &open, faces: Some(&faces), bound, passed });
                for (k, place) in places.into_iter().enumerate() {
                    let Some((run, end)) = place else { continue };
                    for (&t, &was) in run.iter().zip(&kept[k]) {
                    let face = faces[k][t].as_ref().ok_or(TowerError::Refused("a sample's open place without a face"))?;
                    drawn_entropy[k][t] = Some(entropy(face));
                    let u = ((mix(((k as u64) << 40) ^ ((t as u64) << 8) ^ (pass << 56) ^ 0xD) as u128) << 64) | mix(((k as u64) << 40) ^ ((t as u64) << 8) ^ (pass << 56) ^ 0xE) as u128;
                    let whole = !given && t + 1 >= end;
                    let letters = face.total - face.masses[void];
                    classes[k][t] = if whole {
                        let u = u % face.total;
                        let mut acc = 0u128;
                        face.masses.iter().position(|&m| {
                            acc += m;
                            acc > u
                        }).unwrap_or(face.masses.len() - 1)
                    } else if letters == 0 {
                        was
                    } else {
                        let u = u % letters;
                        let mut acc = 0u128;
                        (0..face.masses.len()).filter(|&c| c != void).find(|&c| {
                            acc += face.masses[c];
                            acc > u
                        }).unwrap_or(was)
                    };
                    open[k][t] = false;
                    }
                    // A run's draws read one boundary: where its last letter was drawn the void, the closing law resolves every
                    // place past it, a boundary drawn as a letter there among them.
                    let q = problems[k].0.len();
                    if let Some(first) = (q..classes[k].len()).find(|&t| classes[k][t] == void && !open[k][t]) {
                        for t in first + 1..classes[k].len() {
                            classes[k][t] = void;
                        }
                    }
                }
            }
        }
        observe(ReleaseRead { read, pass: pass as usize + 1, classes: &classes, open: &open, faces: None, bound: 0, passed: 0 });
        Ok(problems.iter().enumerate().map(|(k, &(q, _))| classes[k][q.len()..].to_vec()).collect())
    }
}

/// [measurement; theory, November 10 01:36] **One pass of the parallel certified settle**, as it ends ([`Constitution::settle`]): its
/// number (0 before the first), the problems still active after it, the exchanges it kept and undid, the answers' code summed
/// over the problems, and of its apply-all re-read's code change (each place's `|c_t − c′_t|`, on the codes' `2^(−20)` bits)
/// the part outside every claimed neighbourhood and the whole; and each problem's answer as it stands (its letters).
#[derive(Clone, Copy, Debug)]
pub struct SettlePass<'a> {
    pub pass: usize,
    pub active: usize,
    pub kept: usize,
    pub undone: usize,
    pub code: i128,
    /// [measurement; theory, November 10 02:03] The faces' summed entropy `Σ_t H(f_t)` at the state ([`ExchangePass::entropy`]).
    pub entropy: i128,
    /// [measurement; theory, November 10 03:55] The answers' summed root charge ([`root_charge`]), the places whose surprise
    /// passes their face's entropy by more than a nat (`v > 1`), and the places.
    pub root: i128,
    pub over: usize,
    /// The places whose `v` passes two nats.
    pub over2: usize,
    pub places: usize,
    /// The pass's proposer (its number modulo the walk's cycle: [`Constitution::redraw`]'s 1 a re-draw, 0 an exchange; 0 before the
    /// first pass).
    pub kind: usize,
    pub outside: i128,
    pub changed: i128,
    pub answers: &'a [Vec<usize>],
}

/// [definition; theory, November 10 01:36] **The settle's exchange proposals** on an answer's letters `x` and its locked faces:
/// every pair with bare gain `g = c_i(x_i) + c_j(x_j) − c_i(x_j) − c_j(x_i)` above `h`, the most first (then the nearer pair,
/// then the earlier), each admitted where its claim (the places within `NEAR − 1` of `i` and of `j`) touches no place already
/// claimed; each the two places and the letters they take, with its gain.
pub fn exchange_proposals(x: &[usize], f: &[TowerFace], h: i128) -> Vec<(Vec<(usize, usize)>, i128)> {
    let (len, reach) = (x.len(), NEAR - 1);
    let c = |i: usize, a: usize| f[i].code(a) as i128;
    let mut pairs: Vec<(i128, usize, usize)> = Vec::new();
    for i in 0..len {
        for j in i + 1..len {
            if x[i] != x[j] {
                let g = c(i, x[i]) + c(j, x[j]) - c(i, x[j]) - c(j, x[i]);
                if g > h {
                    pairs.push((g, i, j));
                }
            }
        }
    }
    pairs.sort_by_key(|&(g, i, j)| (std::cmp::Reverse(g), j - i, i));
    let hood = |p: usize| p.saturating_sub(reach)..=(p + reach).min(len - 1);
    let mut claimed = vec![false; len];
    let mut out = Vec::new();
    for (g, i, j) in pairs {
        if hood(i).chain(hood(j)).any(|t| claimed[t]) {
            continue;
        }
        for t in hood(i).chain(hood(j)) {
            claimed[t] = true;
        }
        out.push((vec![(i, x[j]), (j, x[i])], g));
    }
    out
}

/// [definition; theory, November 10 04:15] **The point re-draw proposals** on an answer's letters `x` and its locked faces:
/// every place with `v_t = c_t(x_t) − H(f_t)` above a nat, the most first (then the earlier), re-drawn to its face's top
/// letter (the most mass, the void never, the earlier on a tie) where that letter's bare price
/// `ln f_t(top) − ln f_t(x_t)` is at least a nat, each admitted where its claim (the places within `NEAR − 1`) touches no
/// place already claimed; each its place and its letter, with its bare gain `c_t(x_t) − c_t(top)` on the codes' bits.
pub fn redraw_proposals(x: &[usize], f: &[TowerFace], void: usize) -> Vec<(Vec<(usize, usize)>, i128)> {
    let (len, reach) = (x.len(), NEAR - 1);
    let ln2 = crate::field::ln2_face();
    let nats = |bits: i128| (bits * ln2) >> 30;
    let v: Vec<i128> = (0..len).map(|t| f[t].code(x[t]) as i128 - entropy(&f[t])).collect();
    let mut order: Vec<usize> = (0..len).filter(|&t| nats(v[t]) > 1 << 20).collect();
    order.sort_by_key(|&t| (std::cmp::Reverse(v[t]), t));
    let mut claimed = vec![false; len];
    let mut out = Vec::new();
    for t in order {
        let Some(top) = (0..f[t].masses.len()).filter(|&b| b != void).max_by_key(|&b| (f[t].masses[b], std::cmp::Reverse(b))) else { continue };
        let gain = f[t].code(x[t]) as i128 - f[t].code(top) as i128;
        if top == x[t] || nats(gain) < 1 << 20 {
            continue;
        }
        let hood = t.saturating_sub(reach)..=(t + reach).min(len - 1);
        if hood.clone().any(|u| claimed[u]) {
            continue;
        }
        for u in hood {
            claimed[u] = true;
        }
        out.push((vec![(t, top)], gain));
    }
    out
}

/// [definition; theory, November 10 03:55] **One problem's certified walk** ([`Constitution::redraw`]): its places, its code at the
/// written answer and at its end, its faces' summed entropy and its root charge at its end, its kept changes and those undone,
/// and how it stopped: at neutrality, at rest (a pass kept nothing), or neither (the walk was stopped).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CertifiedRecord {
    pub places: usize,
    pub start: i128,
    pub end: i128,
    pub entropy: i128,
    pub root: i128,
    pub kept: Vec<CertifiedMove>,
    pub undone: usize,
    pub rested: bool,
    pub neutral: bool,
}

/// [definition; theory, November 10 01:36] **One problem's settle** ([`Constitution::settle`]): its places, its answer's code at the
/// written answer and where the settle ended (on the codes' `2^(−20)` bits), its kept exchanges (each with its proposed gain
/// and the fall attributed to it on the read that certified it), the exchanges undone, and whether it rested (a pass kept
/// nothing).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SettleRecord {
    pub places: usize,
    pub start: i128,
    pub end: i128,
    pub kept: Vec<ExchangeMove>,
    pub undone: usize,
    pub rested: bool,
}

/// [definition; theory, November 9 19:43 and 21:12] **One standing move of the certified exchange walk**
/// ([`Constitution::exchange_walk`]): the two places in the answer exchanged, the gain it was proposed on (read on the faces before
/// it), and its certified fall in the answer's code (read on the faces after it), its heat; on the codes' `2^(−20)` bits.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ExchangeMove {
    pub i: usize,
    pub j: usize,
    pub gain: i128,
    pub fall: i128,
}

/// [definition; theory, November 10 03:25 and 03:55] **An answer's root charge** `Σ_a N(a) log₂(N(a)/F(a))` on the codes'
/// `2^(−20)` bits ([`letter_balance`]; each ratio read through [`crate::ratio::ratio_code`], its smaller side over its larger, both
/// scaled down together to the width its quotient reads: a count on `2^72` passes the `2^66` [`crate::field::face_code`] can shift by
/// its unit, which wrapped and read the November 10 128-problem run's root as −636,886 nats).
pub fn root_charge(x: &[usize], faces: &[TowerFace]) -> i128 {
    let (n, f) = letter_balance(x, faces);
    (0..n.len())
        .filter(|&c| n[c] > 0 && f[c] > 0)
        .map(|c| {
            let (num, den) = (n[c] as u128, f[c] as u128);
            let ratio = if num >= den { crate::ratio::ratio_code(den, num) as i128 } else { -(crate::ratio::ratio_code(num, den) as i128) };
            (n[c] >> 72) * ratio
        })
        .sum()
}

/// [definition; theory, November 10 03:55] **One kept change of a certified walk** ([`Constitution::settle`], [`Constitution::redraw`]): each
/// place it rewrote with its letter before and after, its bare gain, and the fall attributed to it on the read that certified
/// it (on the codes' `2^(−20)` bits).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CertifiedMove {
    pub at: Vec<(usize, usize, usize)>,
    pub gain: i128,
    pub fall: i128,
}
