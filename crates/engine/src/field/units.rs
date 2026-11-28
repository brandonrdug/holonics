//! [definition; the review of November 27 (the formal thread's F1 and the review's build step 1), October's lap law (the record of
//! October 25 §1 and §2), the carry key of the lead's host reads of November 27 (the record of the class hairs §22 to §24);
//! `agent-inferred`] **The level's founded units**: a unit is a closed run of the places' symbols, held whole as a part of the level, so
//! that a recurring span is cut the same way at every meeting.
//!
//! ```text
//! key      χ_j(u) = Π_(d=1..|u|) ζ_j(d, u_(|u|−d))   on J circles, ζ_j(d, a) a turn drawn once a circle, a distance back from the
//!                                                   run's end and a symbol (the gene), so a run's key is read wherever it ends
//! store    E_L, P_k : J circles each        the units' ends (a run of L symbols) and their proper prefixes (k symbols), the marks
//! read     r(F, χ) = Re⟨χ, F⟩ / J           one at a charged key, scattered about zero at √(n / 2J) elsewhere (n the keys charged)
//! charge   F ← F + (1 − r(F, χ)) χ           the delta charge: a key that reads its mark takes no more
//! cut      at place t, over the runs ending there u_d = x_(t−d..t), d = 1..L:
//!          some r(E_d, χ(u_d)) ≥ ½ and no r(P_d, χ(u_d)) ≥ ½ → an anchor at t (a unit closes)
//!          some r(P_d, χ(u_d)) ≥ ½                          → no anchor at t (a founded unit may be running), unless the epoch
//!                                                              already spans L places
//!          otherwise                                         → the news's own anchor, as without units
//!          so where units are founded the cut is the symbols' own, the same at every meeting of the same L places before it
//! found    at a crossing, over a sample read through the state: each closed epoch u of 2 to L symbols, met n̂ times by a leaky count of
//!          its key (a candidate field of its own), with her code c over its places at this meeting, is founded where
//!          (n̂ − 1)(c − log₂(U + 2)) > log₂|P| + 1            (the saving of naming it whole at the meetings after the first, against
//!          the choice among the pool's
//!          |P| candidates and the bit of keeping two paths; the formal thread's charge of 22:55 UTC: the first meeting already spells the
//!          unit by its pieces, so its letters are not charged again); `spelled` charges L log₂ A + log₂|P| beside it, October's form
//! rise     the store of her mean news after a run: for the runs of k = 1, 2 symbols ending at a place, the run's word
//!          w = Σ_d u_(|u|−d) A^(d−1) on two coprime rings (the two largest primes under J), a sum S_k of her news at the place after
//!          the run (on 2^(−20) bits) and a count N_k at each residue, charged at a crossing from a sample's places and leaking by its
//!          fade; read at each depth at the ring whose count is least (an entry shared by the fewest other runs), the depths joined by
//!          their counts, ν̂(t) = Σ_k S_k / Σ_k N_k, a ratio held as its pair; an end stands at t + 1 where ν̂ rises at t and not at
//!          t + 1 (a peak); where the store holds meetings those ends are the cut, and the units are founded between them
//! ```
//!
//! The rise store is the formal thread's law of November 28 00:58 UTC (a span's ends are where its readings agree, a property of its
//! type read as a mean over its meetings) in the form its fallback (a) of 01:29 UTC and its residues of 03:34 UTC give it. Why these
//! depths and this addressing (the lead's host reads of November 28, the record of that day §5): her mean news after runs of one and
//! two octets cuts a recurring word alike in 0.947 of 4,743 meetings at 3.16 places an epoch, against 0.940 at depths 1 to 8; her
//! face's entropy at the meeting in its place reads 0.764; the same mean on J = 4,096 keyed circles keeps only 0.774 of the exact
//! mean's ends (a key's charge spreads over every circle, so the commonest keys' charges set every read's crosstalk), and on the
//! residues of two primes near 4,096 it keeps 0.996 (a key's charge sits at one entry a ring, shared only with the keys at that
//! residue).
//!
//! The cut reads only the places before `t`, so a one-sided stream names its anchors from what has arrived. The marks are never
//! stepped by a deposit: a founded unit stays while it is held and leaves by the store's leak at a crossing (`fade`). Why: on November 27
//! her epochs cut a word met again at the same offsets in 0.559 of 4,743 meetings (the record §24, `epoch_cut_long.txt`), as her news
//! moves the landmarks; the review of that day found that October's founding learner never ran where the line trains.

use super::*;
use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};

/// The store's grain: half the turn's (`2^(−15)`), far under a key's scatter `1/√(2J)` and narrow enough for a word's products.
fn grain() -> u32 {
    MOVE_BITS / 2
}

/// [definition] **The level's founded units** ([module](self)).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Units {
    /// `J`, the circles a key is held on.
    pub circles: usize,
    /// `L`, the longest unit in symbols (the shortest is two).
    pub longest: usize,
    /// The gene: the seed the turns `ζ_j(i, a)` are drawn from.
    pub key: u64,
    /// The units founded, by length (`founded[k]` for a run of `k` symbols, `k ≤ L`).
    pub founded: Vec<u32>,
    /// `E_k` for `k = 0..=L` (empty below two), each `2J` (real parts then imaginary, on the store's grain `2^(−15)`).
    pub ends: Vec<Vec<i64>>,
    /// `P_k` for `k = 0..=L − 1` (empty at zero), each `2J`.
    pub prefixes: Vec<Vec<i64>>,
    /// The rise store's two coprime periods, the two largest primes under `J`.
    pub periods: [usize; 2],
    /// `S_k` for `k = 1..=RISE_DEPTH` (index `k − 1`), a ring each: her news after a run of `k` symbols summed at its word's residue,
    /// on `2^(−20)` bits.
    pub news: Vec<[Vec<i64>; 2]>,
    /// `N_k`, a ring each: the meetings charged at each residue.
    pub meetings: Vec<[Vec<i64>; 2]>,
}

/// The rise store's longest run: two symbols. Why: her mean news after runs of one and two octets cuts a recurring word as her mean
/// news after runs of one to eight does (0.947 and 0.940 of 4,743 meetings, the lead's read of November 28; the formal thread's
/// reading of it at 03:25 UTC: the short depths decide the cut, and the long ones add only the word before).
pub const RISE_DEPTH: usize = 2;

/// The two largest primes under `j` (none where `j` is under four).
fn rise_periods(j: usize) -> Option<[usize; 2]> {
    let prime = |q: usize| q >= 2 && (2..).take_while(|d| d * d <= q).all(|d| q % d != 0);
    let mut it = (2..j).rev().filter(|&q| prime(q));
    Some([it.next()?, it.next()?])
}

type Table = Arc<Vec<i64>>;

fn tables() -> &'static Mutex<HashMap<(u64, usize, usize, usize), Table>> {
    static T: OnceLock<Mutex<HashMap<(u64, usize, usize, usize), Table>>> = OnceLock::new();
    T.get_or_init(|| Mutex::new(HashMap::new()))
}

/// The passage's own mixer ([`crate::passage::mix`], SplitMix64), counted from the gene.
fn mix(z: u64) -> u64 {
    crate::passage::mix(z, 0)
}

impl Units {
    /// A store of `circles` circles for units of 2 to `longest` symbols, its turns drawn from `key`, with nothing founded.
    pub fn new(circles: usize, longest: usize, key: u64) -> Result<Self> {
        if circles == 0 || longest < 2 {
            return refuse("a unit store needs circles and a unit of two symbols or more");
        }
        let Some(periods) = rise_periods(circles) else { return refuse("a unit store whose circles hold no two primes under them") };
        Ok(Self {
            circles,
            longest,
            key,
            founded: vec![0; longest + 1],
            ends: (0..=longest).map(|k| if k >= 2 { vec![0; 2 * circles] } else { Vec::new() }).collect(),
            prefixes: (0..longest).map(|k| if k >= 1 { vec![0; 2 * circles] } else { Vec::new() }).collect(),
            periods,
            news: (0..RISE_DEPTH).map(|_| periods.map(|p| vec![0; p])).collect(),
            meetings: (0..RISE_DEPTH).map(|_| periods.map(|p| vec![0; p])).collect(),
        })
    }

    /// The word of the run of `k` symbols ending at `t`, `Σ_d u_(t−d+1) A^(d−1)`; `None` where the run starts before the row or holds a
    /// class outside the alphabet.
    fn rise_word(classes: &[usize], t: usize, k: usize, alphabet: usize) -> Option<u64> {
        if t + 1 < k {
            return None;
        }
        let mut w = 0u64;
        for d in (1..=k).rev() {
            let a = classes[t + 1 - d];
            if a >= alphabet {
                return None;
            }
            w = w * alphabet as u64 + a as u64;
        }
        Some(w)
    }

    /// [definition] **A crossing's charge of the rise store** ([module](self)): every entry leaks by `fade` thousandths, then each place
    /// `t + 1` of each row (its classes and her code at each place on `2^(−20)` bits) charges, for the runs of 1 and 2 symbols ending at
    /// `t`, its code at the run's residue on each ring and one meeting there.
    pub fn charge_rise(&mut self, rows: &[(&[usize], &[i64])], alphabet: usize, fade: i64) -> Result<()> {
        if !(0..=1000).contains(&fade) {
            return refuse("a rise store's fade outside a thousandth's range");
        }
        for f in self.news.iter_mut().chain(self.meetings.iter_mut()).flat_map(|r| r.iter_mut()) {
            for v in f.iter_mut() {
                *v = (*v as i128 * (1000 - fade) as i128 / 1000) as i64;
            }
        }
        for (classes, codes) in rows {
            if classes.len() != codes.len() {
                return refuse("a rise charge whose codes are not one a place");
            }
            for t in 0..classes.len().saturating_sub(1) {
                for k in 1..=RISE_DEPTH {
                    let Some(w) = Self::rise_word(classes, t, k, alphabet) else { continue };
                    for (i, &p) in self.periods.iter().enumerate() {
                        let at = (w % p as u64) as usize;
                        self.news[k - 1][i][at] += codes[t + 1];
                        self.meetings[k - 1][i][at] += 1;
                    }
                }
            }
        }
        Ok(())
    }

    /// `ν̂(t)` as its pair `(Σ_k S_k, Σ_k N_k)`, each depth read at its least-counted ring; `None` where no run ending at `t` was met.
    fn rise_read(&self, classes: &[usize], t: usize, alphabet: usize) -> Option<(i128, i128)> {
        let (mut num, mut den) = (0i128, 0i128);
        for k in 1..=RISE_DEPTH {
            let Some(w) = Self::rise_word(classes, t, k, alphabet) else { continue };
            let at = |i: usize| (w % self.periods[i] as u64) as usize;
            let i = if self.meetings[k - 1][1][at(1)] < self.meetings[k - 1][0][at(0)] { 1 } else { 0 };
            num += self.news[k - 1][i][at(i)] as i128;
            den += self.meetings[k - 1][i][at(i)] as i128;
        }
        (den > 0).then_some((num, den))
    }

    /// [definition] **The rise cut** ([module](self)): an end at `t + 1` where `ν̂` rises at `t` and does not rise at `t + 1` (a peak),
    /// with the first place's anchor; `None` where the store holds no meeting. Increasing, the first `0`.
    pub fn rise_anchors(&self, classes: &[usize], alphabet: usize) -> Option<Vec<usize>> {
        if self.meetings.iter().all(|r| r[0].iter().all(|&m| m == 0)) {
            return None;
        }
        let n = classes.len();
        let nu: Vec<Option<(i128, i128)>> = (0..n).map(|t| self.rise_read(classes, t, alphabet)).collect();
        let rise: Vec<bool> = (0..n)
            .map(|t| t > 0 && matches!((nu[t], nu[t - 1]), (Some((a, b)), Some((c, d))) if a * d > c * b))
            .collect();
        let mut out = vec![0usize];
        for t in 0..n.saturating_sub(1) {
            if rise[t] && !rise[t + 1] {
                out.push(t + 1);
            }
        }
        Some(out)
    }

    /// The turns `ζ_j(d, a)` on the store's grain for a distance `d = 1..=L` back from a run's end (index `d − 1`), `a < alphabet`,
    /// `j < J`, `[d − 1][a][j][re, im]`, drawn once a store's gene and held for the process (a navigator's resident face).
    fn table(&self, alphabet: usize, pi: i128) -> Table {
        let id = (self.key, self.circles, self.longest, alphabet);
        if let Some(t) = tables().lock().map_err(|_| ()).ok().and_then(|m| m.get(&id).cloned()) {
            return t;
        }
        let (j_, l_) = (self.circles, self.longest);
        let mut v = vec![0i64; l_ * alphabet * j_ * 2];
        for i in 0..l_ {
            for a in 0..alphabet {
                for j in 0..j_ {
                    let phase = (mix(self.key ^ mix(i as u64 ^ mix(a as u64 ^ mix(j as u64)))) & ((1u64 << PACE_BITS) - 1)) as i128;
                    let (re, im) = crate::navigator::turn_phasor(phase, 1, pi);
                    let at = ((i * alphabet + a) * j_ + j) * 2;
                    (v[at], v[at + 1]) = (release(re as i128, MOVE_BITS - grain()) as i64, release(im as i128, MOVE_BITS - grain()) as i64);
                }
            }
        }
        let t = Arc::new(v);
        if let Ok(mut m) = tables().lock() {
            m.insert(id, t.clone());
        }
        t
    }

    /// The carry of `run` (at most `L` symbols), `[re…, im…]` on the store's grain: the product of its symbols' turns at their distances
    /// back from its end, the last symbol first.
    fn carry_with(&self, table: &[i64], alphabet: usize, run: &[usize], out: &mut [i64]) {
        let (j_, k, g) = (self.circles, run.len(), grain());
        out[..j_].fill(1i64 << g);
        out[j_..].fill(0);
        for d in 1..=k {
            self.turn(table, alphabet, d, run[k - d], out);
        }
        let _ = g;
    }

    /// One more symbol `a` at distance `d` back: `χ ← χ ζ(d, a)` on the store's grain.
    fn turn(&self, table: &[i64], alphabet: usize, d: usize, a: usize, chi: &mut [i64]) {
        let (j_, g) = (self.circles, grain());
        let row = &table[((d - 1) * alphabet + a) * j_ * 2..((d - 1) * alphabet + a + 1) * j_ * 2];
        for j in 0..j_ {
            let (zr, zi) = (row[2 * j], row[2 * j + 1]);
            let (re, im) = (chi[j], chi[j_ + j]);
            (chi[j], chi[j_ + j]) = (release((re * zr - im * zi) as i128, g) as i64, release((re * zi + im * zr) as i128, g) as i64);
        }
    }

    /// `r(F, χ) = Re⟨χ, F⟩ / J` on the store's grain.
    fn read(&self, field: &[i64], chi: &[i64]) -> i64 {
        let j_ = self.circles;
        let s: i64 = (0..j_).map(|j| chi[j] * field[j] + chi[j_ + j] * field[j_ + j]).sum();
        (release(s as i128, grain()) / j_ as i128) as i64
    }

    /// The delta charge `F ← F + (target − r(F, χ)) χ`.
    fn charge(&self, field: &mut [i64], chi: &[i64], target: i64) {
        let w = target - self.read(field, chi);
        for (f, &c) in field.iter_mut().zip(chi) {
            *f += release((w * c) as i128, grain()) as i64;
        }
    }

    /// A mark read against its midpoint: one at a charged key, zero where none was charged.
    fn marked(&self, field: &[i64], chi: &[i64]) -> bool {
        self.read(field, chi) >= 1i64 << (grain() - 1)
    }

    /// [definition; the formal thread's law of November 28 00:22 UTC, `agent-inferred` in its constants] **The cut a founded unit holds**
    /// ([module](self)): at each place `t` every run ending there, `s_d = x_(t−d..t)` for `d = 1..L`, is a parse in which a unit began `d`
    /// places back, weighted by that start's own standing `a(t − d)`: one where the news anchored there or a founded unit ended there
    /// (read from the symbols, never from this cut's own decisions), and the news's own rate of anchors elsewhere. Each parse speaks for an
    /// end at `t` with its end mark and for a continuation with its prefix mark, each over the store's background `b` (the scatter a key no
    /// charge met reads, `√(n/2J)` over the `n` keys charged): `end(t) = Σ_d a(t−d) (b + r(E_d, s_d)⁺) + b news(t)` and
    /// `cont(t) = Σ_d a(t−d) (b + r(P_d, s_d)⁺)`, and the cut stands at `t` where `end > cont`. Where no unit speaks every parse reads `b`
    /// both ways and the cut is the news's. Where the rise store holds meetings, the cut is its peaks alone. Increasing, the first `0`.
    pub fn anchors(&self, anchors: &[usize], classes: &[usize], alphabet: usize, pi: i128) -> Vec<usize> {
        let n = classes.len();
        if n == 0 {
            return Vec::new();
        }
        // where the rise store holds meetings its peaks are the cut, and the founded units, founded between those ends, need no parse
        // of their own ([`Units::rise_anchors`]; the formal thread, November 28 01:08 UTC: if the rise cut's ends agree, units founded
        // between them need no prefix test; the lead's read of 04:02 UTC: the parse over the rise cut's ends cut a recurring word alike
        // in 0.872 of 4,743 meetings, where the rise cut alone holds 0.948)
        if let Some(rise) = self.rise_anchors(classes, alphabet) {
            return rise;
        }
        if self.founded.iter().all(|&c| c == 0) {
            return anchors.to_vec();
        }
        let table = self.table(alphabet, pi);
        let mut news = vec![false; n + 1];
        for &a in anchors {
            news[a.min(n)] = true;
        }
        let (j_, g) = (self.circles, grain());
        let one = 1i128 << g;
        // the background: the scatter of a read at a key no charge met, over the keys the store holds (each unit's end and prefixes)
        let keys: i128 = (2..=self.longest).map(|k| self.founded[k] as i128 * k as i128).sum();
        let b = ((keys << (2 * g)) / (2 * j_ as i128)).max(0).isqrt();
        // a start's standing away from the news and the units: the news's own rate of anchors over the region
        let rate = (anchors.len() as i128 * one) / n as i128;
        let mut ended = vec![false; n + 1];
        let mut chi = vec![0i64; 2 * j_];
        let mut out = vec![0usize];
        for t in 1..n {
            chi[..j_].fill(1i64 << g);
            chi[j_..].fill(0);
            let (mut end, mut cont) = (if news[t] { b } else { 0 }, 0i128);
            for d in 1..=self.longest.min(t) {
                let a = classes[t - d];
                if a >= alphabet {
                    break;
                }
                self.turn(&table, alphabet, d, a, &mut chi);
                let start = t - d;
                let w = if start == 0 || news[start] || ended[start] { one } else { rate };
                let re = if d >= 2 && self.founded[d] > 0 { self.read(&self.ends[d], &chi).max(0) as i128 } else { 0 };
                let rp = if d < self.longest && d >= 1 { self.read(&self.prefixes[d], &chi).max(0) as i128 } else { 0 };
                if 2 * re >= one {
                    ended[t] = true;
                }
                end += w * (b + re) >> g;
                cont += w * (b + rp) >> g;
            }
            if end > cont {
                out.push(t);
            }
        }
        out
    }

    /// [definition] **A crossing's founding** ([module](self)) over the closed epochs of a sample read through the state, each `(its
    /// symbols, her code over its places on 2^(−20) bits)` in the sample's order: the units founded and refreshed, and the share of the
    /// epochs that were already held. Each epoch of 2 to `L` symbols is counted on a candidate field of `candidates` circles (a leaky
    /// count of its key over the sample); one already held refreshes its mark; one not held is founded where the saving of naming it whole,
    /// met `n̂` times, passes its description (the module's inequality); the store's crowding is read at the cut, as its background (the
    /// cap by length the first form held is retired for the upkeep band, which is owed at the next crossing). Before the sample, every mark
    /// leaks by `fade` thousandths.
    #[allow(clippy::type_complexity)]
    pub fn found(&mut self, epochs: &[(Vec<usize>, i64)], alphabet: usize, candidates: usize, fade: i64, spelled: bool, pi: i128) -> Result<(usize, usize, usize, Vec<Vec<usize>>, Vec<Vec<usize>>)> {
        if !(0..=1000).contains(&fade) {
            return refuse("a unit store's fade outside a thousandth's range");
        }
        for f in self.ends.iter_mut().chain(self.prefixes.iter_mut()) {
            for v in f.iter_mut() {
                *v = (*v as i128 * (1000 - fade) as i128 / 1000) as i64;
            }
        }
        let table = self.table(alphabet, pi);
        let cand = Units { circles: candidates, ..Units::new(candidates, self.longest, self.key ^ 0xC0FF_EE00_0000_0001)? };
        let ctable = cand.table(alphabet, pi);
        let mut counts: Vec<Vec<i64>> = (0..=self.longest).map(|_| vec![0i64; 2 * candidates]).collect();
        let (mut chi, mut cchi) = (vec![0i64; 2 * self.circles], vec![0i64; 2 * candidates]);
        let (mut founded, mut refreshed, mut held) = (0usize, 0usize, 0usize);
        let mut runs: Vec<Vec<usize>> = Vec::new();
        let mut met: std::collections::HashSet<Vec<usize>> = std::collections::HashSet::new();
        for (run, code) in epochs {
            let k = run.len();
            if k < 2 || k > self.longest || run.iter().any(|&c| c >= alphabet) {
                continue;
            }
            self.carry_with(&table, alphabet, run, &mut chi);
            if self.founded[k] > 0 && self.marked(&self.ends[k], &chi) {
                held += 1;
                refreshed += 1;
                met.insert(run.clone());
                self.charge_unit(&table, alphabet, run, &mut chi);
                continue;
            }
            cand.carry_with(&ctable, alphabet, run, &mut cchi);
            let field = &mut counts[k];
            // the meetings so far, this one included, on the store's grain
            let seen = cand.read(field, &cchi) as i128 + (1i128 << grain());
            for (f, &c) in field.iter_mut().zip(&cchi) {
                *f += c;
            }
            // prequential: the first meeting spells the run by its pieces, so only the meetings after it save; naming it whole costs the
            // choice among the units held and the path of no unit, `log₂(U + 2)`; all on 2^(−20) bits, the saving on 2^(−50)
            let units: u128 = self.founded.iter().map(|&c| c as u128).sum::<u128>() + 2;
            let naming = face_code(1, units) as i128;
            let saving = (seen - (1i128 << grain())).max(0) * (*code as i128 - naming);
            let pool = face_code(1, epochs.len().max(1) as u128) as i128;
            let charge = if spelled { k as i128 * face_code(1, alphabet as u128) as i128 + pool } else { pool + (1i128 << READ_BITS) };
            let charge = charge << grain();
            if saving > charge {
                self.founded[k] += 1;
                founded += 1;
                runs.push(run.clone());
                self.charge_unit(&table, alphabet, run, &mut chi);
            }
        }
        let mut met: Vec<Vec<usize>> = met.into_iter().collect();
        met.sort();
        Ok((founded, refreshed, held, runs, met))
    }

    /// The marks of a unit: its end at its length and each proper prefix.
    fn charge_unit(&mut self, table: &[i64], alphabet: usize, run: &[usize], chi: &mut [i64]) {
        let k = run.len();
        self.carry_with(table, alphabet, run, chi);
        let mut end = std::mem::take(&mut self.ends[k]);
        self.charge(&mut end, chi, 1i64 << grain());
        self.ends[k] = end;
        for p in 1..k {
            self.carry_with(table, alphabet, &run[..p], chi);
            let mut pre = std::mem::take(&mut self.prefixes[p]);
            self.charge(&mut pre, chi, 1i64 << grain());
            self.prefixes[p] = pre;
        }
    }

    /// The text form: `units J L KEY` then the counts by length, then each field's `2J` words, then `rise P₁ P₂` and, a depth at a
    /// time, its sums on each ring and its meetings on each ring.
    pub fn to_text(&self) -> String {
        let mut s = format!("units {} {} {}\n", self.circles, self.longest, self.key);
        s.push_str(&self.founded.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(" "));
        s.push('\n');
        for f in self.ends.iter().skip(2).chain(self.prefixes.iter().skip(1)) {
            s.push_str(&f.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(" "));
            s.push('\n');
        }
        s.push_str(&format!("rise {} {}\n", self.periods[0], self.periods[1]));
        for k in 0..RISE_DEPTH {
            for f in self.news[k].iter().chain(self.meetings[k].iter()) {
                s.push_str(&f.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(" "));
                s.push('\n');
            }
        }
        s
    }

    /// The text form back ([`Units::to_text`]), from its lines.
    pub fn from_lines(lines: &mut dyn Iterator<Item = &str>) -> Result<Self> {
        let head: Vec<&str> = lines.next().ok_or(TowerError::Refused("a unit store with no head"))?.split_whitespace().collect();
        let ["units", j, l, key] = head[..] else { return refuse("a unit store's head that is not `units J L KEY`") };
        let parse = |s: &str| s.parse::<i64>().map_err(|_| TowerError::Refused("a unit store's word that is no integer"));
        let mut u = Units::new(j.parse().map_err(|_| TowerError::Refused("a unit store's circles"))?, l.parse().map_err(|_| TowerError::Refused("a unit store's length"))?, key.parse().map_err(|_| TowerError::Refused("a unit store's key"))?)?;
        u.founded = lines.next().ok_or(TowerError::Refused("a unit store with no counts"))?.split_whitespace().map(|w| w.parse::<u32>().map_err(|_| TowerError::Refused("a unit store's count"))).collect::<Result<_>>()?;
        if u.founded.len() != u.longest + 1 {
            return refuse("a unit store's counts that are not one a length");
        }
        for k in 2..=u.longest {
            u.ends[k] = lines.next().ok_or(TowerError::Refused("a unit store missing a field"))?.split_whitespace().map(parse).collect::<Result<_>>()?;
        }
        for k in 1..u.longest {
            u.prefixes[k] = lines.next().ok_or(TowerError::Refused("a unit store missing a field"))?.split_whitespace().map(parse).collect::<Result<_>>()?;
        }
        if u.ends.iter().skip(2).chain(u.prefixes.iter().skip(1)).any(|f| f.len() != 2 * u.circles) {
            return refuse("a unit store's field that is not 2J words");
        }
        let head: Vec<&str> = lines.next().ok_or(TowerError::Refused("a unit store with no rise store"))?.split_whitespace().collect();
        let ["rise", p0, p1] = head[..] else { return refuse("a rise store's head that is not `rise P₁ P₂`") };
        if [p0, p1] != u.periods.map(|p| p.to_string()).each_ref().map(String::as_str) {
            return refuse("a rise store's periods that are not the two largest primes under its circles");
        }
        for k in 0..RISE_DEPTH {
            for i in 0..4 {
                let f: Vec<i64> = lines.next().ok_or(TowerError::Refused("a rise store missing a ring"))?.split_whitespace().map(parse).collect::<Result<_>>()?;
                if f.len() != u.periods[i % 2] {
                    return refuse("a rise store's ring that is not its period's words");
                }
                if i < 2 {
                    u.news[k][i] = f;
                } else {
                    u.meetings[k][i - 2] = f;
                }
            }
        }
        Ok(u)
    }
}

/// The candidate field's circles: a leaky count of every closed epoch's key over a crossing's sample, its scatter `√(n/2J)` near one at
/// a sample's hundred thousand distinct epochs (`agent-inferred`: a count must stand over its own scatter before a saving is read from it).
pub const CANDIDATE_CIRCLES: usize = 65_536;

impl Constitution {
    /// [definition; the lead, November 27, the review's build step 1; the rise store, November 28] **A crossing's founding on the level**
    /// ([`Units::charge_rise`], [`Units::found`]): the level's unit store founded where it has none (`circles`, `longest`, `key`); its
    /// rise store charged from every place of a sample read through the state (each row's classes, the anchors the level cut on it and
    /// her code at each place); each row cut again by the charged store ([`Units::anchors`], on the host's threads); and its closed
    /// epochs, each with her code over its places, founding units in the sample's order. Refused on a field without a level, or where a
    /// store stands with another shape. Returns the units founded, refreshed and held, the founded runs, the units met already held and
    /// the closed epochs read.
    #[allow(clippy::type_complexity)]
    pub fn found_units(&mut self, rows: &[(Vec<usize>, Vec<usize>, Vec<i64>)], circles: usize, longest: usize, key: u64, fade: i64, spelled: bool) -> Result<(usize, usize, usize, Vec<Vec<usize>>, Vec<Vec<usize>>, usize)> {
        use rayon::prelude::*;
        let (alphabet, pi) = (self.declaration.alphabet, self.pi);
        let Some(s) = self.scale.as_deref_mut() else { return refuse("founded units on a field without a level") };
        let units = match s.units.take() {
            Some(u) if u.circles == circles && u.longest == longest && u.key == key => u,
            Some(_) => return refuse("a unit store founded again with another shape or gene"),
            None => Units::new(circles, longest, key)?,
        };
        let mut units = units;
        let charged: Vec<(&[usize], &[i64])> = rows.iter().map(|(c, _, codes)| (c.as_slice(), codes.as_slice())).collect();
        if let Err(e) = units.charge_rise(&charged, alphabet, fade) {
            s.units = Some(units);
            return Err(e);
        }
        let cuts: Vec<Vec<usize>> = rows.par_iter().map(|(classes, anchors, _)| units.anchors(anchors, classes, alphabet, pi)).collect();
        let mut epochs: Vec<(Vec<usize>, i64)> = Vec::new();
        for ((classes, _, codes), cut) in rows.iter().zip(&cuts) {
            // the closed epochs: each run between two anchors (the last, open at the row's end, is not closed)
            for w in cut.windows(2) {
                epochs.push((classes[w[0]..w[1]].to_vec(), codes[w[0]..w[1]].iter().sum()));
            }
        }
        let out = units.found(&epochs, alphabet, CANDIDATE_CIRCLES, fade, spelled, pi);
        s.units = Some(units);
        out.map(|(f, r, h, runs, met)| (f, r, h, runs, met, epochs.len()))
    }

    /// The level's unit store, where it holds one.
    pub fn units(&self) -> Option<&Units> {
        self.scale.as_deref().and_then(|s| s.units.as_ref())
    }
}

#[cfg(test)]
mod founded_unit_tests {
    use super::*;

    fn pi() -> i128 {
        crate::ratio::half_turn(MOVE_BITS + 16)
    }

    /// A run met often enough at a code it still pays is founded, then held whole by the cut against news anchors inside it, and the
    /// store reads back from its text as itself.
    #[test]
    fn a_recurring_run_is_founded_and_then_cut_whole() {
        let (alphabet, pi) = (12usize, pi());
        let mut u = Units::new(1024, 6, 27).unwrap();
        // the run [1, 2, 3] met ten times at 30 bits, among runs met once
        let mut epochs: Vec<(Vec<usize>, i64)> = Vec::new();
        for k in 0..10usize {
            epochs.push((vec![1, 2, 3], 30i64 << READ_BITS));
            epochs.push((vec![4 + k % 7, 11, 4 + (k * 3) % 7], 30i64 << READ_BITS));
        }
        let (founded, _, _, _, _) = u.found(&epochs, alphabet, 4096, 0, false, pi).unwrap();
        assert!(founded >= 1 && u.founded[3] >= 1, "the recurring run is founded: {founded} {:?}", u.founded);
        // news anchors at 1 (the unit's start), 2 (inside it) and 5; the unit [1, 2, 3] at places 1 to 3 closes at 4
        let classes = [0usize, 1, 2, 3, 0, 8];
        assert_eq!(u.anchors(&[0, 1, 2, 5], &classes, alphabet, pi), vec![0, 1, 4, 5]);
        // a run that is no unit keeps the news's anchors
        assert_eq!(u.anchors(&[0, 2, 4], &[0, 3, 2, 9, 9, 10], alphabet, pi), vec![0, 2, 4]);
        let text = u.to_text();
        let back = Units::from_lines(&mut text.lines()).unwrap();
        assert_eq!(back, u);
    }

    /// The rise store cuts where her mean news after a run peaks: news high after a `2` and low elsewhere puts an end at every place
    /// after a `2`, the same in a row it was never charged from; an empty store leaves her news's anchors; the store reads back as itself.
    #[test]
    fn the_rise_store_cuts_at_the_peak_of_her_mean_news() {
        let (alphabet, pi) = (6usize, pi());
        let mut u = Units::new(64, 4, 27).unwrap();
        assert_eq!(u.periods, [61, 59]);
        let row: Vec<usize> = (0..30).map(|t| t % 3).collect();
        // her code at each place: 10 bits at a place after a `2`, one bit elsewhere
        let codes: Vec<i64> = (0..30).map(|t| if t > 0 && row[t - 1] == 2 { 10i64 << READ_BITS } else { 1i64 << READ_BITS }).collect();
        assert_eq!(u.anchors(&[0, 4], &[0, 1, 2, 0, 1, 2], alphabet, pi), vec![0, 4], "an empty store leaves the news's anchors");
        u.charge_rise(&[(&row, &codes)], alphabet, 0).unwrap();
        assert_eq!(u.rise_anchors(&[0, 1, 2, 0, 1, 2, 0, 1, 2], alphabet), Some(vec![0, 3, 6]));
        assert_eq!(u.anchors(&[0, 4], &[1, 2, 0, 1, 2, 0, 1], alphabet, pi), vec![0, 2, 5], "its peaks are the cut");
        let text = u.to_text();
        assert_eq!(Units::from_lines(&mut text.lines()).unwrap(), u);
        // a leak common to the sums and the counts keeps the mean, and so the cut
        u.charge_rise(&[], alphabet, 500).unwrap();
        assert_eq!(u.rise_anchors(&[0, 1, 2, 0, 1, 2, 0, 1, 2], alphabet), Some(vec![0, 3, 6]));
    }

    /// A run her code already holds cheaply is not founded: its saving does not pass its charge.
    #[test]
    fn a_run_her_code_holds_is_not_founded() {
        let (alphabet, pi) = (12usize, pi());
        let mut u = Units::new(1024, 6, 27).unwrap();
        let epochs: Vec<(Vec<usize>, i64)> = (0..10).map(|_| (vec![1, 2, 3], 1i64 << READ_BITS)).collect();
        let (founded, _, _, _, _) = u.found(&epochs, alphabet, 4096, 0, false, pi).unwrap();
        assert_eq!(founded, 0);
    }
}
