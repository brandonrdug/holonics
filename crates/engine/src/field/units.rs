//! [definition; the review of November 27 (the formal thread's F1 and the review's build step 1), October's lap law (the record of
//! October 25 §1 and §2), the formal thread's laws of November 28 (the rise cut of 00:58 UTC, its residues of 03:34 UTC); the review's
//! check of step 1 (November 28 08:32 UTC); `agent-inferred` in the realization] **The level's founded units and the rise store that
//! cuts them**: a unit is a closed run of the places' symbols, founded whole as a part of the level; the cut is the peaks of her mean news
//! after the runs ending at each place, a property of the runs' types, so a recurring span is cut the same way at every meeting.
//!
//! ```text
//! word     w(u) = Σ_d u_(|u|−d) A^(d−1)              a run's word in the alphabet's base, oldest symbol first
//! rings    two coprime periods p₀, p₁                the two largest primes under J; a run sits at w mod p on each
//! rise     for the runs of k = 1, 2 symbols ending at a place, at each residue a sum S_k of her news at the place after the run (on
//!          2^(−20) bits) and a count N_k, charged at a crossing from a sample's places and leaking by its fade; read at each depth at
//!          the ring whose count is least (an entry shared by the fewest other runs), the depths joined by their counts,
//!          ν̂(t) = Σ_k S_k / Σ_k N_k, a ratio held as its pair; an end stands at t + 1 where ν̂ rises at t and not at t + 1 (a peak),
//!          and where the store holds meetings those ends are the level's cut; elsewhere the cut is her news's
//! marks    for each length k = 2..L, at each residue of each ring: the count c of the units there, the sums of their words and of
//!          their words' squares (wrapping, a quotient: a cell's sums are its units' in any order), and the sums of their evidence
//!          (a leaky count of meetings on 2^(−20)) and of their saving (on 2^(−20) bits)
//! held     u is held where its cell on a ring holds it alone (c = 1, the word sum w) or with one other unit v (c = 2,
//!          v = Σw − w with v² + w² = Σw²), read at the ring whose count is least; a cell empty on either ring holds nothing
//! found    at a crossing, over a sample read through the state: each closed epoch u of 2 to L symbols, met n̂ times on a crossing's
//!          candidate rings (two primes under 65,536, a count at each residue, read at the least: an upper bound on its own count),
//!          with her code c over its places at this meeting, is founded where
//!          (n̂ − 1)(c − log₂(U + 2)) > log₂|P| + 1            (the saving of naming it whole at the meetings after the first, against
//!          the choice among the pool's |P| candidates and the bit of keeping two paths; the formal thread's charge of 22:55 UTC: the
//!          first meeting already spells the unit by its pieces); `spelled` charges L log₂ A + log₂|P| beside it, October's form; a
//!          held unit met again charges one meeting and its saving at its cells
//! ```
//!
//! Why residues for the marks too (the review's check of November 28, 08:32 UTC, read the same day): the marks on 4,096 keyed circles
//! read 988 runs as held at the second crossing that neither crossing had founded and failed 30 that the first had (founded again), and
//! a fade of 368 thousandths left a mark at 0.632 against a midpoint of 0.5; on residues a unit's charge sits at one cell a ring, shared
//! only with the units at that residue, and its word's sums tell it apart from them. Why the rise store's depths and addressing (the
//! record of November 28 §5 to §7): her mean news after runs of one and two octets cuts a recurring word alike in 0.947 of 4,743
//! meetings at 3.16 places an epoch, against 0.940 at depths 1 to 8; on J = 4,096 keyed circles the same mean keeps 0.774 of the exact
//! mean's ends and on the residues of two primes near 4,096 it keeps 0.996. The units' weighted parse of the formal thread's law of
//! 00:22 UTC, which read the units' end and prefix marks into the cut, cut a recurring word alike in 0.872 of those meetings over the
//! store's ends where the store's peaks alone read 0.948 (§8), and left the cut; its law stands in that record.
//!
//! The cut reads only the symbols up to `t + 1`, so a one-sided stream names an end one place after it. Nothing here is stepped by a
//! deposit: the store and the marks change only at a crossing. No law yet releases a unit (the band is owed); a unit stays founded, and
//! its evidence and saving leak by the crossing's fade.

use super::*;

/// The candidate rings' extent: a crossing counts every closed epoch's word on the two largest primes under it (65,521 and 65,519).
/// Why (`agent-inferred`): the first founding sample of November 27 met about 186,000 closed epochs a crossing, so a count at each of
/// 65,521 residues holds about three meetings beside a run's own, the least of two rings fewer.
pub const CANDIDATE_CIRCLES: usize = 65_536;

/// The rise store's longest run: two symbols. Why: her mean news after runs of one and two octets cuts a recurring word as her mean
/// news after runs of one to eight does (0.947 and 0.940 of 4,743 meetings, the lead's read of November 28; the formal thread's
/// reading of it at 03:25 UTC: the short depths decide the cut, and the long ones add only the word before).
pub const RISE_DEPTH: usize = 2;

/// The two largest primes under `j` (none where `j` is under four).
fn periods_under(j: usize) -> Option<[usize; 2]> {
    let prime = |q: usize| q >= 2 && (2..).take_while(|d| d * d <= q).all(|d| q % d != 0);
    let mut it = (2..j).rev().filter(|&q| prime(q));
    Some([it.next()?, it.next()?])
}

/// One ring's cells for the units of one length ([module](self)).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cells {
    /// The units at each residue.
    pub count: Vec<u32>,
    /// The sum of their words, wrapping.
    pub words: Vec<u128>,
    /// The sum of their words' squares, wrapping.
    pub squares: Vec<u128>,
    /// The sum of their evidence, a leaky count of meetings on `2^(−20)`.
    pub evidence: Vec<i64>,
    /// The sum of their saving, on `2^(−20)` bits.
    pub saving: Vec<i64>,
}

impl Cells {
    fn new(p: usize) -> Self {
        Self { count: vec![0; p], words: vec![0; p], squares: vec![0; p], evidence: vec![0; p], saving: vec![0; p] }
    }
}

/// [definition] **The level's founded units** ([module](self)).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Units {
    /// `J`, the extent the rings' periods are read under.
    pub circles: usize,
    /// `L`, the longest unit in symbols (the shortest is two).
    pub longest: usize,
    /// The units founded, by length (`founded[k]` for a run of `k` symbols, `k ≤ L`).
    pub founded: Vec<u32>,
    /// The two coprime periods, the two largest primes under `J`.
    pub periods: [usize; 2],
    /// The marks for `k = 0..=L` (empty below two), a ring each.
    pub cells: Vec<Vec<Cells>>,
    /// The rise store's `S_k` for `k = 1..=RISE_DEPTH` (index `k − 1`), a ring each: her news after a run of `k` symbols summed at its
    /// word's residue, on `2^(−20)` bits.
    pub news: Vec<[Vec<i64>; 2]>,
    /// `N_k`, a ring each: the meetings charged at each residue.
    pub meetings: Vec<[Vec<i64>; 2]>,
}

/// A crossing's founding read ([`Units::found`]): the units founded, the epochs read as held and the founded runs, the distinct
/// units met already held (a receipt, never read by the machine).
pub type Founding = (usize, usize, Vec<Vec<usize>>, Vec<Vec<usize>>);

impl Units {
    /// A store whose periods are the two largest primes under `circles`, for units of 2 to `longest` symbols, with nothing founded.
    pub fn new(circles: usize, longest: usize) -> Result<Self> {
        if longest < 2 {
            return refuse("a unit store needs a unit of two symbols or more");
        }
        let Some(periods) = periods_under(circles) else { return refuse("a unit store whose circles hold no two primes under them") };
        Ok(Self {
            circles,
            longest,
            founded: vec![0; longest + 1],
            periods,
            cells: (0..=longest).map(|k| if k >= 2 { periods.iter().map(|&p| Cells::new(p)).collect() } else { Vec::new() }).collect(),
            news: (0..RISE_DEPTH).map(|_| periods.map(|p| vec![0; p])).collect(),
            meetings: (0..RISE_DEPTH).map(|_| periods.map(|p| vec![0; p])).collect(),
        })
    }

    /// A run's word, oldest symbol first; `None` where a class lies outside the alphabet.
    fn word(run: &[usize], alphabet: usize) -> Option<u128> {
        let mut w = 0u128;
        for &a in run {
            if a >= alphabet {
                return None;
            }
            w = w.wrapping_mul(alphabet as u128).wrapping_add(a as u128);
        }
        Some(w)
    }

    /// The word of the run of `k` symbols ending at `t`; `None` where it starts before the row or holds a class outside the alphabet.
    fn rise_word(classes: &[usize], t: usize, k: usize, alphabet: usize) -> Option<u128> {
        if t + 1 < k {
            return None;
        }
        Self::word(&classes[t + 1 - k..=t], alphabet)
    }

    /// Whether the unit store holds the word `w` among its units of length `k` ([module](self)).
    fn holds(&self, k: usize, w: u128) -> bool {
        let rings = &self.cells[k];
        let at: Vec<usize> = self.periods.iter().map(|&p| (w % p as u128) as usize).collect();
        if rings.iter().zip(&at).any(|(r, &a)| r.count[a] == 0) {
            return false;
        }
        let i = if rings[1].count[at[1]] < rings[0].count[at[0]] { 1 } else { 0 };
        let (c, s1, s2) = (rings[i].count[at[i]], rings[i].words[at[i]], rings[i].squares[at[i]]);
        match c {
            1 => s1 == w && s2 == w.wrapping_mul(w),
            2 => {
                let v = s1.wrapping_sub(w);
                v.wrapping_mul(v).wrapping_add(w.wrapping_mul(w)) == s2
            }
            _ => false,
        }
    }

    /// Charge a unit's cells on both rings: `units` more units there (one at a founding, none at a meeting), its evidence and saving.
    fn charge_cells(&mut self, k: usize, w: u128, units: u32, evidence: i64, saving: i64) {
        for (i, &p) in self.periods.iter().enumerate() {
            let a = (w % p as u128) as usize;
            let r = &mut self.cells[k][i];
            if units > 0 {
                r.count[a] += units;
                r.words[a] = r.words[a].wrapping_add(w);
                r.squares[a] = r.squares[a].wrapping_add(w.wrapping_mul(w));
            }
            r.evidence[a] += evidence;
            r.saving[a] += saving;
        }
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
                        let at = (w % p as u128) as usize;
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
            let at = |i: usize| (w % self.periods[i] as u128) as usize;
            let i = if self.meetings[k - 1][1][at(1)] < self.meetings[k - 1][0][at(0)] { 1 } else { 0 };
            num += self.news[k - 1][i][at(i)] as i128;
            den += self.meetings[k - 1][i][at(i)] as i128;
        }
        (den > 0).then_some((num, den))
    }

    /// Whether the rise store holds any meeting.
    pub fn charged(&self) -> bool {
        self.meetings.iter().any(|r| r[0].iter().any(|&m| m != 0))
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

    /// [definition] **The level's cut** ([module](self)): the rise store's peaks where it holds meetings, her news's `anchors` elsewhere.
    /// Increasing, the first `0`. The cut a crossing founds units between.
    pub fn anchors(&self, anchors: &[usize], classes: &[usize], alphabet: usize) -> Vec<usize> {
        if classes.is_empty() {
            return Vec::new();
        }
        self.rise_anchors(classes, alphabet).unwrap_or_else(|| anchors.to_vec())
    }

    /// [definition; the formal thread, November 28 10:58 UTC] **The rise store's table for the expected peak**: for each previous class
    /// `a` (and a last row, index `A`, for no previous class) and each next class `x`, her mean news after the run `x` and the run `a x`
    /// joined by their counts, `(S₁(x) + S₂(a x)) / (N₁(x) + N₂(a x))` released once at her code's grain (`2^(−20)` bits), each depth
    /// read at its least-counted ring; `−1` where neither run was met. `[(A + 1) A]`, row-major by the previous class.
    pub fn rise_table(&self, alphabet: usize) -> Vec<i64> {
        let mut out = vec![-1i64; (alphabet + 1) * alphabet];
        for prev in 0..=alphabet {
            for x in 0..alphabet {
                let row: Vec<usize> = if prev < alphabet { vec![prev, x] } else { vec![x] };
                if let Some((num, den)) = self.rise_read(&row, row.len() - 1, alphabet) {
                    out[prev * alphabet + x] = div_nearest(num, den) as i64;
                }
            }
        }
        out
    }

    /// [definition; the formal thread, November 28 10:58 UTC (G-Z77 held at 11:30 UTC); the strand's open-news law of November 18] **The
    /// peak named in time**: an end at `t + 1` where `ν̂` rises at `t` and the rise is not expected to continue under her face at `t + 1`,
    /// `E_(p_(t+1)) ν̂(t + 1 | x) ≤ ν̂(t)`, so the end is named from `x_(≤t)` and her face before `x_(t+1)` arrives. `expect[t]` is that
    /// expectation at the face of place `t` as its pair `(Σ_x m_t(x) V(x_(t−1), x), Σ_x m_t(x))` over the `x` the table has met
    /// ([`Units::rise_table`]); a place whose pair has no mass names no end. `None` where the store holds no meeting.
    pub fn expected_anchors(&self, classes: &[usize], alphabet: usize, expect: &[(i128, i128)]) -> Option<Vec<usize>> {
        if self.meetings.iter().all(|r| r[0].iter().all(|&m| m == 0)) || expect.len() != classes.len() {
            return None;
        }
        let n = classes.len();
        let nu: Vec<Option<(i128, i128)>> = (0..n).map(|t| self.rise_read(classes, t, alphabet)).collect();
        let mut out = vec![0usize];
        for t in 1..n.saturating_sub(1) {
            let rises = matches!((nu[t], nu[t - 1]), (Some((a, b)), Some((c, d))) if a * d > c * b);
            let (Some((a, b)), (e, m)) = (nu[t], expect[t + 1]) else { continue };
            // the expectation e/m against ν̂(t) = a/b, both on her code's grain, as pairs
            if rises && m > 0 && e * b <= a * m {
                out.push(t + 1);
            }
        }
        Some(out)
    }

    /// [definition; the formal thread, November 28 08:46 UTC; `agent-inferred` in its realization] **The cut as the level reads it**:
    /// where the rise store holds meetings and the region is read with both sides of each place (`before` false: a region the trainer
    /// owns, or a cavity), each peak's end `a` stands at `a + 1`, so a site at `t` reads only the ends that `x_(<t)` names and stands in
    /// the epoch of the place before it; a one-sided stream (`before` true) already reads each open place in the epoch before its own
    /// (the strand's law of November 18), so its known stream keeps the peaks as they are. Elsewhere [`Units::anchors`]. Why: the peak
    /// at `a` reads the class at `a` (a rise at `a − 1` with none at `a`), so a site read at the peaks' own places reads a phase its own
    /// symbol placed; the store's lap W135r coded the held cavity 0.0235 nats a place under its control and her forward code 0.0085 over
    /// it, most at an epoch's first place (+0.048; the record of November 28 §10).
    /// Where `expect` is given (her face's expectation at every place, [`Units::expected_anchors`]), the store's ends are the peaks named
    /// in time, read as they stand on both sides and on one.
    pub fn read_anchors(&self, anchors: &[usize], classes: &[usize], alphabet: usize, before: bool, expect: Option<&[(i128, i128)]>) -> Vec<usize> {
        if let Some(e) = expect.and_then(|e| self.expected_anchors(classes, alphabet, e)) {
            return e;
        }
        let n = classes.len();
        match self.rise_anchors(classes, alphabet) {
            Some(peaks) if !before => {
                let mut out = vec![0usize];
                out.extend(peaks.into_iter().skip(1).map(|a| a + 1).filter(|&a| a < n));
                out
            }
            _ => self.anchors(anchors, classes, alphabet),
        }
    }

    /// [definition] **A crossing's founding** ([module](self)) over the closed epochs of a sample read through the state, each `(its
    /// symbols, her code over its places on 2^(−20) bits)` in the sample's order. Before the sample every unit's evidence and saving leak
    /// by `fade` thousandths. A held unit met charges one meeting and its saving (her code over it less its naming); a run not held is
    /// counted on the crossing's candidate rings and founded where the saving of naming it whole, met `n̂` times, passes its
    /// description (the module's inequality).
    pub fn found(&mut self, epochs: &[(Vec<usize>, i64)], alphabet: usize, fade: i64, spelled: bool) -> Result<Founding> {
        if !(0..=1000).contains(&fade) {
            return refuse("a unit store's fade outside a thousandth's range");
        }
        for r in self.cells.iter_mut().flat_map(|k| k.iter_mut()) {
            for v in r.evidence.iter_mut().chain(r.saving.iter_mut()) {
                *v = (*v as i128 * (1000 - fade) as i128 / 1000) as i64;
            }
        }
        let cand_periods = periods_under(CANDIDATE_CIRCLES).ok_or(TowerError::Refused("candidate rings with no primes under them"))?;
        let mut cand: Vec<Vec<u32>> = cand_periods.iter().map(|&p| vec![0u32; p]).collect();
        let (mut founded, mut held) = (0usize, 0usize);
        let mut runs: Vec<Vec<usize>> = Vec::new();
        let mut met: std::collections::BTreeSet<Vec<usize>> = std::collections::BTreeSet::new();
        let pool = face_code(1, epochs.len().max(1) as u128) as i128;
        let meeting = 1i64 << READ_BITS;
        for (run, code) in epochs {
            let k = run.len();
            if k < 2 || k > self.longest {
                continue;
            }
            let Some(w) = Self::word(run, alphabet) else { continue };
            // naming it whole costs the choice among the units held and the path of no unit, `log₂(U + 2)`, on 2^(−20) bits
            let units: u128 = self.founded.iter().map(|&c| c as u128).sum::<u128>() + 2;
            let naming = face_code(1, units) as i128;
            if self.founded[k] > 0 && self.holds(k, w) {
                held += 1;
                met.insert(run.clone());
                self.charge_cells(k, w, 0, meeting, (*code as i128 - naming) as i64);
                continue;
            }
            // the meetings so far, this one included: the least of the candidate rings' counts (an upper bound on its own)
            let at: Vec<usize> = cand_periods.iter().map(|&p| (w % p as u128) as usize).collect();
            for (c, &a) in cand.iter_mut().zip(&at) {
                c[a] += 1;
            }
            let seen = cand.iter().zip(&at).map(|(c, &a)| c[a]).min().unwrap_or(1) as i128;
            // prequential: the first meeting spells the run by its pieces, so only the meetings after it save
            let saving = (seen - 1) * (*code as i128 - naming);
            let charge = if spelled { k as i128 * face_code(1, alphabet as u128) as i128 + pool } else { pool + (1i128 << READ_BITS) };
            if saving > charge {
                self.founded[k] += 1;
                founded += 1;
                runs.push(run.clone());
                self.charge_cells(k, w, 1, seen as i64 * meeting, saving.clamp(i64::MIN as i128, i64::MAX as i128) as i64);
            }
        }
        Ok((founded, held, runs, met.into_iter().collect()))
    }

    /// The text form: `units J L`, the counts by length, then for each length from two and each ring its counts, word sums, square
    /// sums, evidence and saving a line each, then `rise P₁ P₂` and, a depth at a time, its sums on each ring and its meetings on each
    /// ring.
    pub fn to_text(&self) -> String {
        fn line<T: std::fmt::Display>(v: &[T]) -> String {
            let mut s = v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ");
            s.push('\n');
            s
        }
        let mut s = format!("units {} {}\n", self.circles, self.longest);
        s.push_str(&line(&self.founded));
        for k in 2..=self.longest {
            for r in &self.cells[k] {
                s.push_str(&line(&r.count));
                s.push_str(&line(&r.words));
                s.push_str(&line(&r.squares));
                s.push_str(&line(&r.evidence));
                s.push_str(&line(&r.saving));
            }
        }
        s.push_str(&format!("rise {} {}\n", self.periods[0], self.periods[1]));
        for k in 0..RISE_DEPTH {
            for f in self.news[k].iter().chain(self.meetings[k].iter()) {
                s.push_str(&line(f));
            }
        }
        s
    }

    /// The text form back ([`Units::to_text`]), from its lines.
    pub fn from_lines(lines: &mut dyn Iterator<Item = &str>) -> Result<Self> {
        fn words<T: std::str::FromStr>(line: Option<&str>, len: usize) -> Result<Vec<T>> {
            let v = line.ok_or(TowerError::Refused("a unit store missing a line"))?.split_whitespace().map(|w| w.parse::<T>().map_err(|_| TowerError::Refused("a unit store's word that is no integer"))).collect::<Result<Vec<T>>>()?;
            if v.len() != len {
                return refuse("a unit store's line that is not its period's words");
            }
            Ok(v)
        }
        let head: Vec<&str> = lines.next().ok_or(TowerError::Refused("a unit store with no head"))?.split_whitespace().collect();
        let ["units", j, l] = head[..] else { return refuse("a unit store's head that is not `units J L`") };
        let mut u = Units::new(j.parse().map_err(|_| TowerError::Refused("a unit store's circles"))?, l.parse().map_err(|_| TowerError::Refused("a unit store's length"))?)?;
        u.founded = words(lines.next(), u.longest + 1)?;
        for k in 2..=u.longest {
            for i in 0..2 {
                let p = u.periods[i];
                u.cells[k][i] = Cells { count: words(lines.next(), p)?, words: words(lines.next(), p)?, squares: words(lines.next(), p)?, evidence: words(lines.next(), p)?, saving: words(lines.next(), p)? };
            }
        }
        let head: Vec<&str> = lines.next().ok_or(TowerError::Refused("a unit store with no rise store"))?.split_whitespace().collect();
        let ["rise", p0, p1] = head[..] else { return refuse("a rise store's head that is not `rise P₁ P₂`") };
        if [p0, p1] != u.periods.map(|p| p.to_string()).each_ref().map(String::as_str) {
            return refuse("a rise store's periods that are not the two largest primes under its circles");
        }
        for k in 0..RISE_DEPTH {
            for i in 0..2 {
                u.news[k][i] = words(lines.next(), u.periods[i])?;
            }
            for i in 0..2 {
                u.meetings[k][i] = words(lines.next(), u.periods[i])?;
            }
        }
        Ok(u)
    }
}

impl Constitution {
    /// [definition; the lead, November 27, the review's build step 1; the rise store and the marks on residues, November 28] **A
    /// crossing's founding on the level** ([`Units::charge_rise`], [`Units::found`]): the level's unit store founded where it has none
    /// (`circles`, `longest`); its rise store charged from every place of a sample read through the state (each row's classes, the
    /// anchors the level cut on it and her code at each place); each row cut again by the charged store ([`Units::anchors`]); and its
    /// closed epochs, each with her code over its places, founding units in the sample's order. Refused on a field without a level, or
    /// where a store stands with another shape. Returns the founding's read and the closed epochs read.
    pub fn found_units(&mut self, rows: &[(Vec<usize>, Vec<usize>, Vec<i64>)], circles: usize, longest: usize, fade: i64, spelled: bool) -> Result<(Founding, usize)> {
        let alphabet = self.declaration.alphabet;
        let Some(s) = self.scale.as_deref_mut() else { return refuse("founded units on a field without a level") };
        let mut units = match s.units.take() {
            Some(u) if u.circles == circles && u.longest == longest => u,
            Some(_) => return refuse("a unit store founded again with another shape"),
            None => Units::new(circles, longest)?,
        };
        let charged: Vec<(&[usize], &[i64])> = rows.iter().map(|(c, _, codes)| (c.as_slice(), codes.as_slice())).collect();
        if let Err(e) = units.charge_rise(&charged, alphabet, fade) {
            s.units = Some(units);
            return Err(e);
        }
        let mut epochs: Vec<(Vec<usize>, i64)> = Vec::new();
        for (classes, anchors, codes) in rows {
            let cut = units.anchors(anchors, classes, alphabet);
            // the closed epochs: each run between two anchors (the last, open at the row's end, is not closed)
            for w in cut.windows(2) {
                epochs.push((classes[w[0]..w[1]].to_vec(), codes[w[0]..w[1]].iter().sum()));
            }
        }
        let out = units.found(&epochs, alphabet, fade, spelled);
        s.units = Some(units);
        out.map(|f| (f, epochs.len()))
    }

    /// The level's unit store, where it holds one.
    pub fn units(&self) -> Option<&Units> {
        self.scale.as_deref().and_then(|s| s.units.as_ref())
    }
}

#[cfg(test)]
mod founded_unit_tests {
    use super::*;

    /// A run met often enough at a code it still pays is founded and then held; a run met beside it at the same residue on both rings
    /// is told apart by its word's sums; the store reads back from its text as itself.
    #[test]
    fn a_recurring_run_is_founded_and_held_on_its_residues() {
        let alphabet = 12usize;
        // periods 7 and 5: [1, 2, 3] has the word 1·144 + 2·12 + 3 = 171, at 3 mod 7 and 1 mod 5
        let mut u = Units::new(8, 6).unwrap();
        assert_eq!(u.periods, [7, 5]);
        let mut epochs: Vec<(Vec<usize>, i64)> = Vec::new();
        for k in 0..10usize {
            epochs.push((vec![1, 2, 3], 30i64 << READ_BITS));
            epochs.push((vec![4 + k % 7, 11, 4 + (k * 3) % 7], 30i64 << READ_BITS));
        }
        let (founded, _, runs, _) = u.found(&epochs, alphabet, 0, false).unwrap();
        assert!(founded >= 1 && runs.contains(&vec![1, 2, 3]), "the recurring run is founded: {runs:?}");
        assert!(u.holds(3, Units::word(&[1, 2, 3], alphabet).unwrap()));
        // a run at the same residues on both rings (171 + 35 = 206: 3 mod 7 and 1 mod 5) that was never founded is not held
        assert!(!u.holds(3, 206));
        let (_, held, _, met) = u.found(&[(vec![1, 2, 3], 30i64 << READ_BITS)], alphabet, 0, false).unwrap();
        assert_eq!((held, met), (1, vec![vec![1, 2, 3]]), "a held unit met again is read held, not founded again");
        let text = u.to_text();
        assert_eq!(Units::from_lines(&mut text.lines()).unwrap(), u);
    }

    /// Two units at one cell on both rings are each held, and a third word there is not.
    #[test]
    fn two_units_at_one_cell_are_told_apart_by_their_sums() {
        let mut u = Units::new(8, 4).unwrap();
        // 171 and 206 share 3 mod 7 and 1 mod 5; 241 shares them too
        u.charge_cells(3, 171, 1, 0, 0);
        u.charge_cells(3, 206, 1, 0, 0);
        u.founded[3] = 2;
        assert!(u.holds(3, 171) && u.holds(3, 206));
        assert!(!u.holds(3, 241));
    }

    /// A run her code already holds cheaply is not founded: its saving does not pass its charge.
    #[test]
    fn a_run_her_code_holds_is_not_founded() {
        let mut u = Units::new(1024, 6).unwrap();
        let epochs: Vec<(Vec<usize>, i64)> = (0..10).map(|_| (vec![1, 2, 3], 1i64 << READ_BITS)).collect();
        let (founded, _, _, _) = u.found(&epochs, 12, 0, false).unwrap();
        assert_eq!(founded, 0);
    }

    /// The rise store cuts where her mean news after a run peaks: news high after a `2` and low elsewhere puts an end at every place
    /// after a `2`, the same in a row it was never charged from; an empty store leaves her news's anchors; the store reads back as itself.
    #[test]
    fn the_rise_store_cuts_at_the_peak_of_her_mean_news() {
        let alphabet = 6usize;
        let mut u = Units::new(64, 4).unwrap();
        assert_eq!(u.periods, [61, 59]);
        let row: Vec<usize> = (0..30).map(|t| t % 3).collect();
        // her code at each place: 10 bits at a place after a `2`, one bit elsewhere
        let codes: Vec<i64> = (0..30).map(|t| if t > 0 && row[t - 1] == 2 { 10i64 << READ_BITS } else { 1i64 << READ_BITS }).collect();
        assert_eq!(u.anchors(&[0, 4], &[0, 1, 2, 0, 1, 2], alphabet), vec![0, 4], "an empty store leaves the news's anchors");
        u.charge_rise(&[(&row, &codes)], alphabet, 0).unwrap();
        assert_eq!(u.rise_anchors(&[0, 1, 2, 0, 1, 2, 0, 1, 2], alphabet), Some(vec![0, 3, 6]));
        assert_eq!(u.anchors(&[0, 4], &[1, 2, 0, 1, 2, 0, 1], alphabet), vec![0, 2, 5], "its peaks are the cut");
        assert_eq!(u.read_anchors(&[0, 4], &[1, 2, 0, 1, 2, 0, 1], alphabet, false, None), vec![0, 3, 6], "read with both sides, a place late");
        assert_eq!(u.read_anchors(&[0, 4], &[1, 2, 0, 1, 2, 0, 1], alphabet, true, None), vec![0, 2, 5], "a one-sided stream keeps the peaks");
        // the peak named in time: a face that expects a `0` after every `2` (the low news there) names the end after each `2` before it
        // arrives; a face that expects a `2` after a `1` (the high news after it) names none after the `1`
        let table = u.rise_table(alphabet);
        let classes = [1usize, 2, 0, 1, 2, 0, 1];
        let expect: Vec<(i128, i128)> = (0..classes.len())
            .map(|t| if t == 0 { (0, 0) } else {
                let x = match classes[t - 1] { 2 => 0, 1 => 2, _ => 1 };
                (table[classes[t - 1] * alphabet + x] as i128, 1)
            })
            .collect();
        assert_eq!(u.expected_anchors(&classes, alphabet, &expect), Some(vec![0, 2, 5]));
        assert_eq!(u.read_anchors(&[0, 4], &classes, alphabet, false, Some(&expect)), vec![0, 2, 5], "named in time, read as it stands");
        let text = u.to_text();
        assert_eq!(Units::from_lines(&mut text.lines()).unwrap(), u);
        // a leak common to the sums and the counts keeps the mean, and so the cut
        u.charge_rise(&[], alphabet, 500).unwrap();
        assert_eq!(u.rise_anchors(&[0, 1, 2, 0, 1, 2, 0, 1, 2], alphabet), Some(vec![0, 3, 6]));
    }
}
