//! [definition; the review of November 27 (the formal thread's F1 and the review's build step 1), October's lap law (the record of
//! October 25 §1 and §2), the carry key of the lead's host reads of November 27 (the record of the class hairs §22 to §24);
//! `agent-inferred`] **The level's founded units**: a unit is a closed run of the places' symbols, held whole as a part of the level, so
//! that a recurring span is cut the same way at every meeting.
//!
//! ```text
//! key      χ_j(u) = Π_i ζ_j(i, u_i)        on J circles, ζ_j(i, a) a turn drawn once a circle, a place in the run and a symbol (the gene)
//! store    E_L, P_k : J circles each        the units' ends (a run of L symbols) and their proper prefixes (k symbols), the marks
//! read     r(F, χ) = Re⟨χ, F⟩ / J           one at a charged key, scattered about zero at √(n / 2J) elsewhere (n the keys charged)
//! charge   F ← F + (1 − r(F, χ)) χ           the delta charge: a key that reads its mark takes no more
//! cut      at place t, with the run since the epoch's anchor u = x_(a..t):
//!          r(E_|u|, χ(u)) ≥ ½ and r(P_|u|, χ(u)) < ½ → an anchor at t (the unit closes)
//!          r(P_|u|, χ(u)) ≥ ½                         → no anchor at t (the run is a founded unit's prefix)
//!          otherwise                                   → the news's own anchor, as without units
//! found    at a crossing, over a sample read through the state: each closed epoch u of 2 to L symbols, met n̂ times by a leaky count of
//!          its key (a candidate field of its own), with her code c over its places at this meeting, is founded where
//!          (n̂ − 1)(c − log₂(U + 2)) > log₂|P| + 1            (the saving of naming it whole at the meetings after the first, against
//!          the choice among the pool's
//!          |P| candidates and the bit of keeping two paths; the formal thread's charge of 22:55 UTC: the first meeting already spells the
//!          unit by its pieces, so its letters are not charged again); `spelled` charges L log₂ A + log₂|P| beside it, October's form
//! ```
//!
//! The cut reads only the places before `t`, so a one-sided stream names its anchors from what has arrived. The marks are never
//! stepped by a deposit: a founded unit stays while it is held and leaves by the store's leak at a crossing (`fade`). Why: on November 27
//! her epochs cut a word met again at the same offsets in 0.559 of 4,743 meetings (the record §24, `epoch_cut_long.txt`), as her news
//! moves the landmarks; the review of that day found that October's founding learner never ran where the line trains.

use super::*;
use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};

/// A founded unit's mark is read against its midpoint: one at a charged key, zero where none was charged.
const HALF: i64 = 1i64 << (MOVE_BITS - 1);

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
    /// `E_k` for `k = 0..=L` (empty below two), each `2J` (real parts then imaginary, on `2^(−30)`).
    pub ends: Vec<Vec<i64>>,
    /// `P_k` for `k = 0..=L − 1` (empty at zero), each `2J`.
    pub prefixes: Vec<Vec<i64>>,
}

type Table = Arc<Vec<i32>>;

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
        Ok(Self {
            circles,
            longest,
            key,
            founded: vec![0; longest + 1],
            ends: (0..=longest).map(|k| if k >= 2 { vec![0; 2 * circles] } else { Vec::new() }).collect(),
            prefixes: (0..longest).map(|k| if k >= 1 { vec![0; 2 * circles] } else { Vec::new() }).collect(),
        })
    }

    /// The turns `ζ_j(i, a)` on `2^(−30)` for `i < L`, `a < alphabet`, `j < J`, `[i][a][j][re, im]`, drawn once a store's gene and held for
    /// the process (a navigator's resident face).
    fn table(&self, alphabet: usize, pi: i128) -> Table {
        let id = (self.key, self.circles, self.longest, alphabet);
        if let Some(t) = tables().lock().map_err(|_| ()).ok().and_then(|m| m.get(&id).cloned()) {
            return t;
        }
        let (j_, l_) = (self.circles, self.longest);
        let mut v = vec![0i32; l_ * alphabet * j_ * 2];
        for i in 0..l_ {
            for a in 0..alphabet {
                for j in 0..j_ {
                    let phase = (mix(self.key ^ mix(i as u64 ^ mix(a as u64 ^ mix(j as u64)))) & ((1u64 << PACE_BITS) - 1)) as i128;
                    let (re, im) = crate::navigator::turn_phasor(phase, 1, pi);
                    let at = ((i * alphabet + a) * j_ + j) * 2;
                    (v[at], v[at + 1]) = (re as i32, im as i32);
                }
            }
        }
        let t = Arc::new(v);
        if let Ok(mut m) = tables().lock() {
            m.insert(id, t.clone());
        }
        t
    }

    /// The carry of `run` (at most `L` symbols), `[re…, im…]` on `2^(−30)`: the product of its symbols' turns at their places.
    fn carry_with(&self, table: &[i32], alphabet: usize, run: &[usize], out: &mut [i64]) {
        let j_ = self.circles;
        for j in 0..j_ {
            let (mut re, mut im) = (1i128 << MOVE_BITS, 0i128);
            for (i, &a) in run.iter().enumerate() {
                let at = ((i * alphabet + a) * j_ + j) * 2;
                let (zr, zi) = (table[at] as i128, table[at + 1] as i128);
                (re, im) = (release(re * zr - im * zi, MOVE_BITS), release(re * zi + im * zr, MOVE_BITS));
            }
            (out[j], out[j_ + j]) = (re as i64, im as i64);
        }
    }

    /// `r(F, χ) = Re⟨χ, F⟩ / J` on `2^(−30)`.
    fn read(&self, field: &[i64], chi: &[i64]) -> i64 {
        let j_ = self.circles;
        let s: i128 = (0..j_).map(|j| chi[j] as i128 * field[j] as i128 + chi[j_ + j] as i128 * field[j_ + j] as i128).sum();
        (release(s, MOVE_BITS) / j_ as i128) as i64
    }

    /// The delta charge `F ← F + (target − r(F, χ)) χ`.
    fn charge(&self, field: &mut [i64], chi: &[i64], target: i64) {
        let w = (target - self.read(field, chi)) as i128;
        for (f, &c) in field.iter_mut().zip(chi) {
            *f += release(w * c as i128, MOVE_BITS) as i64;
        }
    }

    /// [definition] **The cut a founded unit holds** ([module](self)): the news's `anchors` of a run of `classes`, with each founded unit
    /// closed at its end and held whole (no anchor inside it), read place by place from what has arrived. Increasing, the first `0`.
    pub fn anchors(&self, anchors: &[usize], classes: &[usize], alphabet: usize, pi: i128) -> Vec<usize> {
        let n = classes.len();
        if n == 0 {
            return Vec::new();
        }
        if self.founded.iter().all(|&c| c == 0) {
            return anchors.to_vec();
        }
        let table = self.table(alphabet, pi);
        let mut news = vec![false; n + 1];
        for &a in anchors {
            news[a.min(n)] = true;
        }
        let j_ = self.circles;
        let one = 1i64 << MOVE_BITS;
        let mut chi = vec![0i64; 2 * j_];
        let (mut out, mut start) = (vec![0usize], 0usize);
        // the run's carry, one symbol's turn a place (the same products, in the same order, as [`Units::carry_with`]); `live` while the run
        // since the anchor is still a founded unit's prefix, after which no longer run can be one and nothing is read until the next anchor
        let reset = |chi: &mut [i64]| {
            chi[..j_].fill(one);
            chi[j_..].fill(0);
        };
        reset(&mut chi);
        let mut live = true;
        for t in 1..n {
            let k = t - start;
            let (mut end, mut prefix) = (false, false);
            if live && k <= self.longest && classes[t - 1] < alphabet {
                let a = classes[t - 1];
                for j in 0..j_ {
                    let at = (((k - 1) * alphabet + a) * j_ + j) * 2;
                    let (zr, zi) = (table[at] as i128, table[at + 1] as i128);
                    let (re, im) = (chi[j] as i128, chi[j_ + j] as i128);
                    (chi[j], chi[j_ + j]) = (release(re * zr - im * zi, MOVE_BITS) as i64, release(re * zi + im * zr, MOVE_BITS) as i64);
                }
                end = k >= 2 && self.founded[k] > 0 && self.read(&self.ends[k], &chi) >= HALF;
                prefix = k < self.longest && self.prefixes[k].iter().any(|&v| v != 0) && self.read(&self.prefixes[k], &chi) >= HALF;
                live = prefix;
            } else {
                live = false;
            }
            let here = match (end, prefix) {
                (true, false) => true,
                (_, true) => false,
                (false, false) => news[t],
            };
            if here {
                out.push(t);
                start = t;
                reset(&mut chi);
                live = true;
            }
        }
        out
    }

    /// [definition] **A crossing's founding** ([module](self)) over the closed epochs of a sample read through the state, each `(its
    /// symbols, her code over its places on 2^(−20) bits)` in the sample's order: the units founded and refreshed, and the share of the
    /// epochs that were already held. Each epoch of 2 to `L` symbols is counted on a candidate field of `candidates` circles (a leaky
    /// count of its key over the sample); one already held refreshes its mark; one not held is founded where the saving of naming it whole,
    /// met `n̂` times, passes its description (the module's inequality), while its length's field holds fewer units than its own scatter
    /// allows (`n ≤ J/18`, so a stray key reads under a sixth of a mark). Before the sample, every mark leaks by `fade` thousandths.
    pub fn found(&mut self, epochs: &[(Vec<usize>, i64)], alphabet: usize, candidates: usize, fade: i64, spelled: bool, pi: i128) -> Result<(usize, usize, usize)> {
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
        let cap = self.circles / 18;
        let (mut chi, mut cchi) = (vec![0i64; 2 * self.circles], vec![0i64; 2 * candidates]);
        let (mut founded, mut refreshed, mut held) = (0usize, 0usize, 0usize);
        for (run, code) in epochs {
            let k = run.len();
            if k < 2 || k > self.longest || run.iter().any(|&c| c >= alphabet) {
                continue;
            }
            self.carry_with(&table, alphabet, run, &mut chi);
            if self.founded[k] > 0 && self.read(&self.ends[k], &chi) >= HALF {
                held += 1;
                refreshed += 1;
                self.charge_unit(&table, alphabet, run, &mut chi);
                continue;
            }
            cand.carry_with(&ctable, alphabet, run, &mut cchi);
            let field = &mut counts[k];
            // the meetings so far, this one included, on 2^(−30)
            let seen = cand.read(field, &cchi) as i128 + (1i128 << MOVE_BITS);
            for (f, &c) in field.iter_mut().zip(&cchi) {
                *f += c;
            }
            // prequential: the first meeting spells the run by its pieces, so only the meetings after it save; naming it whole costs the
            // choice among the units held and the path of no unit, `log₂(U + 2)`; all on 2^(−20) bits, the saving on 2^(−50)
            let units: u128 = self.founded.iter().map(|&c| c as u128).sum::<u128>() + 2;
            let naming = face_code(1, units) as i128;
            let saving = (seen - (1i128 << MOVE_BITS)).max(0) * (*code as i128 - naming);
            let pool = face_code(1, epochs.len().max(1) as u128) as i128;
            let charge = if spelled { k as i128 * face_code(1, alphabet as u128) as i128 + pool } else { pool + (1i128 << READ_BITS) };
            let charge = charge << MOVE_BITS;
            if saving > charge && (self.founded[k] as usize) < cap {
                self.founded[k] += 1;
                founded += 1;
                self.charge_unit(&table, alphabet, run, &mut chi);
            }
        }
        Ok((founded, refreshed, held))
    }

    /// The marks of a unit: its end at its length and each proper prefix.
    fn charge_unit(&mut self, table: &[i32], alphabet: usize, run: &[usize], chi: &mut [i64]) {
        let k = run.len();
        self.carry_with(table, alphabet, run, chi);
        let mut end = std::mem::take(&mut self.ends[k]);
        self.charge(&mut end, chi, 1i64 << MOVE_BITS);
        self.ends[k] = end;
        for p in 1..k {
            self.carry_with(table, alphabet, &run[..p], chi);
            let mut pre = std::mem::take(&mut self.prefixes[p]);
            self.charge(&mut pre, chi, 1i64 << MOVE_BITS);
            self.prefixes[p] = pre;
        }
    }

    /// The text form: `units J L KEY` then the counts by length, then each field's `2J` words.
    pub fn to_text(&self) -> String {
        let mut s = format!("units {} {} {}\n", self.circles, self.longest, self.key);
        s.push_str(&self.founded.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(" "));
        s.push('\n');
        for f in self.ends.iter().skip(2).chain(self.prefixes.iter().skip(1)) {
            s.push_str(&f.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(" "));
            s.push('\n');
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
        Ok(u)
    }
}

/// The candidate field's circles: a leaky count of every closed epoch's key over a crossing's sample, its scatter `√(n/2J)` near one at
/// a sample's hundred thousand distinct epochs (`agent-inferred`: a count must stand over its own scatter before a saving is read from it).
pub const CANDIDATE_CIRCLES: usize = 65_536;

impl Constitution {
    /// [definition; the lead, November 27, the review's build step 1] **A crossing's founding on the level** ([`Units::found`]): the level's
    /// unit store founded where it has none (`circles`, `longest`, `key`), then charged from the closed epochs of a sample read through the
    /// state, in the sample's order. Refused on a field without a level, or where a store stands with another shape.
    pub fn found_units(&mut self, epochs: &[(Vec<usize>, i64)], circles: usize, longest: usize, key: u64, fade: i64, spelled: bool) -> Result<(usize, usize, usize)> {
        let (alphabet, pi) = (self.declaration.alphabet, self.pi);
        let Some(s) = self.scale.as_deref_mut() else { return refuse("founded units on a field without a level") };
        let units = match s.units.take() {
            Some(u) if u.circles == circles && u.longest == longest && u.key == key => u,
            Some(_) => return refuse("a unit store founded again with another shape or gene"),
            None => Units::new(circles, longest, key)?,
        };
        let mut units = units;
        let out = units.found(epochs, alphabet, CANDIDATE_CIRCLES, fade, spelled, pi);
        s.units = Some(units);
        out
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
        let (founded, _, _) = u.found(&epochs, alphabet, 4096, 0, false, pi).unwrap();
        assert!(founded >= 1 && u.founded[3] >= 1, "the recurring run is founded: {founded} {:?}", u.founded);
        // news anchors at 1 (the unit's start), 2 (inside it) and 5; the unit [1, 2, 3] at places 1 to 3 closes at 4
        let classes = [0usize, 1, 2, 3, 0, 8];
        assert_eq!(u.anchors(&[0, 1, 2, 5], &classes, alphabet, pi), vec![0, 1, 4, 5]);
        // a run that is no unit keeps the news's anchors
        assert_eq!(u.anchors(&[0, 2, 4], &[0, 3, 2, 1, 9, 10], alphabet, pi), vec![0, 2, 4]);
        let text = u.to_text();
        let back = Units::from_lines(&mut text.lines()).unwrap();
        assert_eq!(back, u);
    }

    /// A run her code already holds cheaply is not founded: its saving does not pass its charge.
    #[test]
    fn a_run_her_code_holds_is_not_founded() {
        let (alphabet, pi) = (12usize, pi());
        let mut u = Units::new(1024, 6, 27).unwrap();
        let epochs: Vec<(Vec<usize>, i64)> = (0..10).map(|_| (vec![1, 2, 3], 1i64 << READ_BITS)).collect();
        let (founded, _, _) = u.found(&epochs, alphabet, 4096, 0, false, pi).unwrap();
        assert_eq!(founded, 0);
    }
}
