//! **The continuing body** (#404, #407; record
//! `2026-10-29_THE_CONTINUING_BODY_RESTS_WITH_ITS_CURRENTS_AND_ONE_OPEN_SECTION_AND_AN_ANSWER_READS_ITS_PARTICIPATION`).
//!
//! [definition; agent-inferred, October 29] The body is the learner, its currents and one open
//! section a current:
//!
//! ```text
//! B = (L, (c_s)_(s<S), c_∘, k)        c = (σ, π),  π = ((u_0, q_0), …, (u_m, q_m)),  1 ≤ |π| ≤ T
//! ```
//!
//! `L` is the learner (the material, its moments and its rate). A current is its state σ, carried
//! to its last section's close, and its pending classes π, each with whether it is compared; `u_0`
//! is the pending class, heard as a target and not yet read. `T` is the section (participation's,
//! on a participating tower). The hearing currents `c_s` read a passage's parts in parallel, as the
//! race's streams read theirs; the conversation's current `c_∘` hears the asks and their answers.
//! `k` is the draw state, the keys drawn so far. The clocks ride in σ: the news phase, and
//! participation's open section, empty at a close.
//!
//! **The section law.** Whenever `|π| ≥ T + 1` the current reads `u_0 … u_(T−1)` and the face after
//! `u_i` is compared with `u_(i+1)` wherever `q_(i+1)`; σ moves to the close and `π ← π[T..]`. A
//! section with a compared place is learned ([`TowerLearner::section_realized`], the certified
//! deposit); one with none is read ([`Tower::advance_realized`]) and the moments do not move, so a
//! question heard alone does not age the statistics. Co-present sections read the material they
//! opened on: the read sections are read before the learned ones deposit. A learned section opens
//! at a close, which is where the card reads a participating section from.
//!
//! **Retention.** π is the open section's present terrain, at most `T` classes, released at its
//! close as participation's sites are. Nothing else of a passage is held; an answer's release
//! belongs to its fork and is released with it. The body is accepted = published + pending
//! (`hnn.observed-stream-transaction`) on the tower: the quotient `(Θ, moments, currents)` and one
//! open interval a current.
//!
//! **Provenance.** At an answer's opening (the end letter after its prompt) each level's heads
//! read the open section's admitted sites, each labelled with the arrival that admitted it
//! ([`Tower::participation_read`]); what lies before the section's opening is carried by the modes
//! and has no site. The reading runs on the host from the
//! carried state, which every realization returns to the bit, and decides nothing.
use super::realization::PassRealization;
use super::*;
use crate::receiver::release::{agreeing_class, KeyStream};

/// The bytes of one key: `k / 2^64`, as the class release draws.
pub const KEY_BYTES: usize = 8;
/// The lines of a state's text ([`TowerState::to_text`]).
pub const STATE_LINES: usize = 10;

/// A current: its state at its last section's close and the classes it has heard since, the first
/// the pending class; each with whether it is compared.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Current {
    pub state: TowerState,
    pub pending: Vec<(usize, bool)>,
}

/// [definition; agent-inferred, October 29] **The continuing body** (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TowerBody {
    pub learner: TowerLearner,
    section: usize,
    currents: Vec<Current>,
    conversation: Current,
    drawn: usize,
}

/// What a hearing's closes did: the learned sections (each one [`TowerLearner::section_realized`]
/// over the currents that held one) and the read ones, the deposits, and the learned sections'
/// compared cells and their code before and after, on `2^(−20)` bits.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Hearing {
    pub learned: usize,
    pub read: usize,
    pub deposits: usize,
    pub cells: usize,
    pub code_before: i64,
    pub code_after: i64,
}

impl Hearing {
    /// Two hearings' closes together.
    pub fn join(&mut self, other: Hearing) {
        self.learned += other.learned;
        self.read += other.read;
        self.deposits += other.deposits;
        self.cells += other.cells;
        self.code_before += other.code_before;
        self.code_after += other.code_after;
    }
}

/// An ask's return: the classes released (the last the end letter when `ended`), the classes the
/// open section read to the answer's opening (its last the end letter that opens it), and, on a
/// participating tower, each level's heads' participation over those sites at the opening. The
/// prompt's closes are in `hearing`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Answer {
    pub released: Vec<usize>,
    pub ended: bool,
    pub read: Vec<usize>,
    pub participation: Option<ParticipationRead>,
    pub hearing: Hearing,
}

impl TowerBody {
    /// The body founded on `learner`: `currents` hearing currents and the conversation, each at
    /// rest with the end letter pending, as a section of a passage is entered after the end letter
    /// of the one before it.
    pub fn found(learner: TowerLearner, currents: usize, section: usize) -> Result<Self> {
        if currents == 0 || section == 0 {
            return refuse("a body hears on at least one current over a section of at least one class");
        }
        if learner.tower.participation().is_some_and(|p| p.section != section) {
            return refuse("a participating body's section is its participation's");
        }
        let current = Current { state: learner.tower.rest(), pending: vec![(learner.tower.declaration.alphabet - 1, false)] };
        Ok(Self { section, currents: vec![current.clone(); currents], conversation: current, drawn: 0, learner })
    }

    pub fn section(&self) -> usize {
        self.section
    }

    pub fn currents(&self) -> &[Current] {
        &self.currents
    }

    pub fn conversation(&self) -> &Current {
        &self.conversation
    }

    /// The keys drawn so far: the next ask draws from the declared stream's key of this index.
    pub fn drawn(&self) -> usize {
        self.drawn
    }

    fn end(&self) -> usize {
        self.learner.tower.declaration.alphabet - 1
    }

    /// The passage heard: cut into one contiguous part a hearing current,
    /// `passage[⌊sn/S⌋, ⌊(s+1)n/S⌋)`, each part compared, and every whole section closed.
    pub fn hear(&mut self, passage: &[usize], realization: &mut dyn PassRealization) -> Result<Hearing> {
        self.learner.tower.admit_read(&[passage], &[])?;
        let (n, s) = (passage.len(), self.currents.len());
        for (i, c) in self.currents.iter_mut().enumerate() {
            c.pending.extend(passage[i * n / s..(i + 1) * n / s].iter().map(|&u| (u, true)));
        }
        close(&mut self.learner, self.section, &mut self.currents, realization)
    }

    /// The prompt asked: heard on the conversation with its end letter, neither compared, and a
    /// fork of the conversation reads its open section to the answer's opening and releases at most
    /// `count` classes, each drawn by `agree` agreeing draws from the declared key stream (`keys`,
    /// eight bytes a key) at the body's draw state and read back before the next draw. The material
    /// does not move.
    pub fn ask(&mut self, prompt: &[usize], keys: &[u8], count: usize, agree: u32, realization: &mut dyn PassRealization) -> Result<Answer> {
        let end = self.end();
        if prompt.is_empty() || prompt.contains(&end) || count == 0 || agree == 0 {
            return refuse("an ask is a nonempty prompt without the end letter, released by at least one draw of at least one class");
        }
        self.learner.tower.admit_read(&[prompt], &[])?;
        let unread = keys.get(self.drawn * KEY_BYTES..).ok_or(TowerError::Refused("fewer keys than the body has drawn"))?;
        let mut stream = KeyStream::new(unread.to_vec(), KEY_BYTES).map_err(|_| TowerError::Refused("a key stream of no width"))?;
        self.conversation.pending.extend(prompt.iter().map(|&u| (u, false)).chain([(end, false)]));
        let hearing = close(&mut self.learner, self.section, std::slice::from_mut(&mut self.conversation), realization)?;
        let tower = &self.learner.tower;
        let read: Vec<usize> = self.conversation.pending.iter().map(|&(u, _)| u).collect();
        let participation = match tower.participation() {
            Some(_) => tower.participation_read(&mut self.conversation.state.clone(), &read)?,
            None => None,
        };
        let mut fork = vec![self.conversation.state.clone()];
        let mut face = tower.advance_realized(&mut fork, &[&read], realization)?.0.pop().ok_or(TowerError::Refused("a fork returned no face"))?;
        let (mut released, mut ended) = (Vec::new(), false);
        while released.len() < count {
            let key = stream.next_key().ok_or(TowerError::Refused("fewer keys than the release draws"))?;
            let class = agreeing_class(&face.masses, agree, &key).map_err(|_| TowerError::Refused("a face the draw refuses"))?;
            released.push(class);
            if class == end {
                ended = true;
                break;
            }
            if released.len() < count {
                face = tower.advance_realized(&mut fork, &[&[class]], realization)?.0.pop().ok_or(TowerError::Refused("a fork returned no face"))?;
            }
        }
        self.drawn += stream.keys_read();
        Ok(Answer { released, ended, read, participation, hearing })
    }

    /// The answer heard as the target of the last ask: heard on the conversation with its end
    /// letter, both compared (source END target END), and every whole section closed.
    pub fn answer(&mut self, answer: &[usize], realization: &mut dyn PassRealization) -> Result<Hearing> {
        let end = self.end();
        if answer.is_empty() || answer.contains(&end) {
            return refuse("an answer is nonempty and without the end letter");
        }
        self.learner.tower.admit_read(&[answer], &[])?;
        self.conversation.pending.extend(answer.iter().map(|&u| (u, true)).chain([(end, true)]));
        close(&mut self.learner, self.section, std::slice::from_mut(&mut self.conversation), realization)
    }

    /// [definition; agent-inferred, October 29] **The body grown by `factor`** at rest
    /// ([`TowerLearner::widened`], record `2026-10-29_THE_BODY_GROWS_BY_COPIES_…`): the learner
    /// widened, its differences drawn from the declared founding keys, and every current's state
    /// widened ([`Tower::widen_state`]), its pending classes, the section and the draw state kept.
    /// The grown body reads the faces the body read, so its next ask releases what the body's
    /// would.
    pub fn grow(&mut self, factor: usize, keys: &[u8]) -> Result<()> {
        let learner = self.learner.widened(factor, keys)?;
        let tower = &self.learner.tower;
        let widen = |c: &Current| -> Result<Current> { Ok(Current { state: tower.widen_state(&c.state, factor)?, pending: c.pending.clone() }) };
        let currents = self.currents.iter().map(widen).collect::<Result<Vec<_>>>()?;
        let conversation = widen(&self.conversation)?;
        *self = Self { learner, section: self.section, currents, conversation, drawn: self.drawn };
        Ok(())
    }

    /// The body at rest: the learner's text, the body's line (hearing currents, section, keys
    /// drawn), then each current (the hearing currents, the conversation last) as its state's text
    /// and its pending line, `pending u,q …`.
    pub fn to_text(&self) -> String {
        let mut s = self.learner.to_text();
        s.push_str(&format!("tower-body {} {} {}\n", self.currents.len(), self.section, self.drawn));
        for c in self.currents.iter().chain([&self.conversation]) {
            s.push_str(&c.state.to_text());
            s.push_str("pending");
            for &(u, q) in &c.pending {
                s.push_str(&format!(" {u},{}", u8::from(q)));
            }
            s.push('\n');
        }
        s
    }

    /// The body from its text, refused unless every current restores whole.
    pub fn from_text(text: &str) -> Result<Self> {
        let lines: Vec<&str> = text.lines().collect();
        let n = Tower::text_lines(text) + 3;
        if lines.len() <= n {
            return refuse("a body's text is its learner's, its line and its currents");
        }
        let learner = TowerLearner::from_text(&lines[..n].iter().map(|l| format!("{l}\n")).collect::<String>())?;
        let head: Vec<&str> = lines[n].split(' ').collect();
        let count = |w: &str| w.parse::<usize>().map_err(|_| TowerError::Refused("a body's count that is not a count"));
        if head.len() != 4 || head[0] != "tower-body" {
            return refuse("not a body's line");
        }
        let (currents, section, drawn) = (count(head[1])?, count(head[2])?, count(head[3])?);
        let mut body = Self::found(learner, currents, section)?;
        body.drawn = drawn;
        let rest = &lines[n + 1..];
        if rest.len() != (currents + 1) * (STATE_LINES + 1) {
            return refuse("a body's currents are its count and the conversation, each a state and a pending line");
        }
        let alphabet = body.learner.tower.declaration.alphabet;
        let mut parsed = Vec::with_capacity(currents + 1);
        for c in rest.chunks(STATE_LINES + 1) {
            let state = body.learner.tower.state_from_text(&c[..STATE_LINES])?;
            let mut words = c[STATE_LINES].split(' ');
            if words.next() != Some("pending") {
                return refuse("not a current's pending line");
            }
            let pending = words
                .map(|w| {
                    let (u, q) = w.split_once(',').ok_or(TowerError::Refused("a pending class without its comparison"))?;
                    let u = count(u)?;
                    match (u < alphabet, q) {
                        (true, "0") => Ok((u, false)),
                        (true, "1") => Ok((u, true)),
                        _ => refuse("a pending class outside the alphabet or a comparison that is not 0 or 1"),
                    }
                })
                .collect::<Result<Vec<_>>>()?;
            if pending.is_empty() || pending.len() > section {
                return refuse("a current holds its pending class and at most one open section");
            }
            parsed.push(Current { state, pending });
        }
        body.conversation = parsed.pop().ok_or(TowerError::Refused("a body without its conversation"))?;
        body.currents = parsed;
        Ok(body)
    }
}

/// Every whole section of `currents` closed (the section law): in rounds, each current that holds
/// one closes one. A round reads the sections with no compared place first, then learns the others
/// in one section over their currents.
fn close(learner: &mut TowerLearner, t: usize, currents: &mut [Current], realization: &mut dyn PassRealization) -> Result<Hearing> {
    let mut hearing = Hearing::default();
    loop {
        let ready: Vec<usize> = (0..currents.len()).filter(|&s| currents[s].pending.len() > t).collect();
        if ready.is_empty() {
            return Ok(hearing);
        }
        let (learning, reading): (Vec<usize>, Vec<usize>) = ready.iter().partition(|&&s| currents[s].pending[1..=t].iter().any(|&(_, q)| q));
        if !reading.is_empty() {
            let classes: Vec<Vec<usize>> = reading.iter().map(|&s| currents[s].pending[..t].iter().map(|&(u, _)| u).collect()).collect();
            let slices: Vec<&[usize]> = classes.iter().map(Vec::as_slice).collect();
            let mut states: Vec<TowerState> = reading.iter().map(|&s| currents[s].state.clone()).collect();
            learner.tower.advance_realized(&mut states, &slices, realization)?;
            for (&s, state) in reading.iter().zip(states) {
                currents[s].state = state;
            }
            hearing.read += 1;
        }
        if !learning.is_empty() {
            let classes: Vec<Vec<usize>> = learning.iter().map(|&s| currents[s].pending[..=t].iter().map(|&(u, _)| u).collect()).collect();
            let compared: Vec<Vec<Option<usize>>> = learning.iter().map(|&s| currents[s].pending[..=t].iter().map(|&(u, q)| q.then_some(u)).collect()).collect();
            let slices: Vec<&[usize]> = classes.iter().map(Vec::as_slice).collect();
            let masks: Vec<&[Option<usize>]> = compared.iter().map(Vec::as_slice).collect();
            let mut states: Vec<TowerState> = learning.iter().map(|&s| currents[s].state.clone()).collect();
            let receipt = learner.section_realized(&mut states, &slices, Some(&masks), realization)?;
            for (&s, state) in learning.iter().zip(states) {
                currents[s].state = state;
            }
            hearing.join(Hearing { learned: 1, read: 0, deposits: usize::from(receipt.deposited), cells: receipt.cells, code_before: receipt.code_before, code_after: receipt.code_after });
        }
        for &s in &ready {
            currents[s].pending.drain(..t);
        }
    }
}

/// A text line: its label and its entries.
fn line<T: std::fmt::Display>(label: &str, entries: impl IntoIterator<Item = T>) -> String {
    let mut s = String::from(label);
    for v in entries {
        s.push(' ');
        s.push_str(&v.to_string());
    }
    s.push('\n');
    s
}

/// A text line's entries, refused unless its label is `label` and it holds `count` of them.
fn entries<T: std::str::FromStr>(text: &str, label: &str, count: usize) -> Result<Vec<T>> {
    let mut words = text.split(' ');
    if words.next() != Some(label) {
        return refuse("a state's line that is not the one its place declares");
    }
    let v = words.map(|w| w.parse::<T>().map_err(|_| TowerError::Refused("a state's entry that is not an integer"))).collect::<Result<Vec<_>>>()?;
    if v.len() != count {
        return refuse("a state's line of the wrong extent");
    }
    Ok(v)
}

fn flatten(out: &mut Vec<i64>, pairs: &[(i64, i64)]) {
    out.extend(pairs.iter().flat_map(|&(a, b)| [a, b]));
}

fn paired(v: &[i64]) -> Vec<(i64, i64)> {
    v.chunks(2).map(|p| (p[0], p[1])).collect()
}

impl TowerState {
    /// [definition; agent-inferred, October 29] **The state as text**, ten lines: `state
    /// previous reversed news`, then the modes (level-major, `re im`), the ring, its hands, the
    /// strands, the credit (`-` when the stream carries none; per level its push, along, around,
    /// gate bias and gate moments), the open face (`-` without one; its total, then its masses),
    /// participation's open sections (`-` without participation; per level its site count, the
    /// frame, the met dissipation, the held current and each site's key, value and heads'
    /// dissipation), the open packets (`-` without packets; the levels the clock holds,
    /// level-major, `re im`) and the open traces (`-` without the heading; the levels the clock
    /// holds, level-major).
    pub fn to_text(&self) -> String {
        let mut s = format!("state {} {} {}\n", self.previous, u8::from(self.reversed), self.news);
        let mut modes = Vec::new();
        for level in &self.modes {
            flatten(&mut modes, level);
        }
        s.push_str(&line("modes", modes));
        s.push_str(&line("ring", self.ring.iter().flat_map(|&(a, b)| [a, b])));
        s.push_str(&line("hands", self.hands.iter().map(|&h| u8::from(h))));
        s.push_str(&line("strands", self.strands.iter()));
        match &self.credit {
            None => s.push_str("credit -\n"),
            Some(levels) => {
                let mut v = Vec::new();
                for c in levels {
                    for part in [&c.push, &c.along, &c.around, &c.gate_bias, &c.gate] {
                        flatten(&mut v, part);
                    }
                }
                s.push_str(&line("credit", v));
            }
        }
        match &self.open {
            None => s.push_str("open -\n"),
            Some(face) => s.push_str(&line("open", std::iter::once(face.total).chain(face.masses.iter().copied()))),
        }
        match self.sites.first() {
            None => s.push_str("sites -\n"),
            Some(_) => {
                let mut v = Vec::new();
                for level in &self.sites {
                    v.push(level.len() as i64);
                    flatten(&mut v, &level.frame);
                    v.extend(&level.met);
                    flatten(&mut v, &level.current);
                    for j in 0..level.len() {
                        flatten(&mut v, &level.keys[j]);
                        flatten(&mut v, &level.values[j]);
                        v.extend(&level.dissipation[j]);
                    }
                }
                s.push_str(&line("sites", v));
            }
        }
        if self.packets.is_empty() {
            s.push_str("packets -\n");
        } else {
            let mut v = Vec::new();
            for level in &self.packets {
                flatten(&mut v, level);
            }
            s.push_str(&line("packets", v));
        }
        if self.traces.is_empty() {
            s.push_str("traces -\n");
        } else {
            s.push_str(&line("traces", self.traces.iter().flatten()));
        }
        s
    }
}

impl Tower {
    /// A stream's state from its text ([`TowerState::to_text`]), refused unless every part has the
    /// extent this tower's rested state gives it.
    pub fn state_from_text(&self, lines: &[&str]) -> Result<TowerState> {
        if lines.len() != STATE_LINES {
            return refuse("a state's text is ten lines");
        }
        let d = &self.declaration;
        let rest = self.rest();
        let head: Vec<&str> = lines[0].split(' ').collect();
        if head.len() != 4 || head[0] != "state" {
            return refuse("not a state's line");
        }
        let previous = head[1].parse::<usize>().map_err(|_| TowerError::Refused("a previous class that is not a class"))?;
        let reversed = match head[2] {
            "0" => false,
            "1" => true,
            _ => return refuse("an orientation that is not 0 or 1"),
        };
        let news = head[3].parse::<u64>().map_err(|_| TowerError::Refused("a news phase that is not a count"))?;
        if previous > d.alphabet {
            return refuse("a previous class outside the alphabet and its start");
        }
        let modes = entries::<i64>(lines[1], "modes", 2 * d.levels * d.modes)?.chunks(2 * d.modes).map(paired).collect();
        let ring = entries::<i128>(lines[2], "ring", 2 * rest.ring.len())?.chunks(2).map(|p| (p[0], p[1])).collect();
        let hands = entries::<u8>(lines[3], "hands", rest.hands.len())?
            .into_iter()
            .map(|h| match h {
                0 => Ok(false),
                1 => Ok(true),
                _ => refuse("a hand that is not 0 or 1"),
            })
            .collect::<Result<Vec<_>>>()?;
        let strands = entries::<u32>(lines[4], "strands", rest.strands.len())?;
        let credit = match lines[5] {
            "credit -" => None,
            text => {
                let template = self.rest_with_credit().credit.unwrap_or_default();
                let shape = |c: &LevelCredit| [c.push.len(), c.along.len(), c.around.len(), c.gate_bias.len(), c.gate.len()];
                let total: usize = template.iter().map(|c| 2 * shape(c).iter().sum::<usize>()).sum();
                let v = entries::<i64>(text, "credit", total)?;
                let mut at = 0;
                let mut take = |n: usize| {
                    let part = paired(&v[at..at + 2 * n]);
                    at += 2 * n;
                    part
                };
                Some(
                    template
                        .iter()
                        .map(|c| {
                            let [p, a, r, gb, g] = shape(c);
                            LevelCredit { push: take(p), along: take(a), around: take(r), gate_bias: take(gb), gate: take(g) }
                        })
                        .collect(),
                )
            }
        };
        let open = match lines[6] {
            "open -" => None,
            text => {
                let v = entries::<u128>(text, "open", d.alphabet + 1)?;
                Some(TowerFace { total: v[0], masses: v[1..].to_vec() })
            }
        };
        let sites = match (lines[7], self.participation()) {
            ("sites -", None) => Vec::new(),
            (text, Some(p)) if text != "sites -" => {
                let (n, h) = (d.modes, p.heads.len());
                let mut words = text.split(' ');
                if words.next() != Some("sites") {
                    return refuse("not a line of sites");
                }
                let v = words.map(|w| w.parse::<i64>().map_err(|_| TowerError::Refused("an entry of sites that is not an integer"))).collect::<Result<Vec<_>>>()?;
                let mut at = 0;
                let mut take = |k: usize| -> Result<Vec<i64>> {
                    let part = v.get(at..at + k).ok_or(TowerError::Refused("a line of sites shorter than its counts"))?.to_vec();
                    at += k;
                    Ok(part)
                };
                let levels = (0..d.levels)
                    .map(|_| {
                        let count = usize::try_from(take(1)?[0]).map_err(|_| TowerError::Refused("a site count that is not a count"))?;
                        if count >= p.section {
                            return refuse("an open section holds fewer sites than its section");
                        }
                        let frame = paired(&take(2 * n)?);
                        let met = take(n)?;
                        let current = paired(&take(2 * n)?);
                        let mut level = LevelSites { frame, met, keys: Vec::new(), values: Vec::new(), dissipation: Vec::new(), current };
                        for _ in 0..count {
                            level.keys.push(paired(&take(2 * n)?));
                            level.values.push(paired(&take(2 * n)?));
                            level.dissipation.push(take(h)?);
                        }
                        Ok(level)
                    })
                    .collect::<Result<Vec<_>>>()?;
                if at != v.len() {
                    return refuse("a line of sites longer than its counts");
                }
                levels
            }
            _ => return refuse("participation's open section on a participating tower alone"),
        };
        let packets = match (lines[8], rest.packets.is_empty()) {
            ("packets -", true) => Vec::new(),
            (text, false) if text != "packets -" => {
                let held: usize = rest.packets.iter().map(Vec::len).sum();
                let v = entries::<i64>(text, "packets", 2 * held)?;
                let mut at = 0;
                rest.packets
                    .iter()
                    .map(|level| {
                        let part = paired(&v[at..at + 2 * level.len()]);
                        at += 2 * level.len();
                        part
                    })
                    .collect()
            }
            _ => return refuse("open packets on a tower with packets alone"),
        };
        let traces = match (lines[9], rest.traces.is_empty()) {
            ("traces -", true) => Vec::new(),
            (text, false) if text != "traces -" => {
                let held: usize = rest.traces.iter().map(Vec::len).sum();
                let v = entries::<i64>(text, "traces", held)?;
                let mut at = 0;
                rest.traces
                    .iter()
                    .map(|level| {
                        let part = v[at..at + level.len()].to_vec();
                        at += level.len();
                        part
                    })
                    .collect()
            }
            _ => return refuse("open traces on a tower with the heading alone"),
        };
        Ok(TowerState { modes, previous, credit, ring, hands, strands, reversed, open, news, sites, packets, traces })
    }
}

#[cfg(test)]
mod tests {
    use super::super::tests::{keys, tiny_clocked_participating, tiny_contacts, tiny_participating};
    use super::*;
    use crate::hnn::tower::realization::HostPass;

    /// The fixture body: the tiny participating tower (section sixteen) learning at `2^(−6)`, on
    /// three hearing currents.
    fn tiny_body() -> TowerBody {
        TowerBody::found(TowerLearner::new(tiny_participating(ContactLaw::Rectifying, true), 6), 3, 16).expect("founded")
    }

    fn passage(n: usize, seed: usize) -> Vec<usize> {
        (0..n).map(|i| (i * 7 + seed * 5 + i / 3) % 3).collect()
    }

    fn bounded(body: &TowerBody) {
        for c in body.currents().iter().chain([body.conversation()]) {
            assert!(!c.pending.is_empty() && c.pending.len() <= body.section(), "a current holds {} pending classes", c.pending.len());
        }
    }

    /// The body's whole life: two hearings, an ask, its answer and the ask again.
    fn live(body: &mut TowerBody, rest_between: bool) -> (TowerBody, Vec<Answer>) {
        let k = keys(4096);
        let pass = &mut HostPass::default();
        body.hear(&passage(150, 1), pass).expect("heard");
        bounded(body);
        let mut body = if rest_between {
            let text = body.to_text();
            let restored = TowerBody::from_text(&text).expect("restored");
            assert_eq!(restored.to_text(), text, "the body's text re-encodes equal");
            restored
        } else {
            body.clone()
        };
        let pass = &mut HostPass::default();
        body.hear(&passage(97, 2), pass).expect("heard");
        bounded(&body);
        let first = body.ask(&[1, 2, 0, 1, 1, 2], &k, 24, 1, pass).expect("asked");
        bounded(&body);
        body.answer(&[2, 2, 1, 0, 2, 1, 1, 0, 2, 2, 1], pass).expect("answered");
        bounded(&body);
        let second = body.ask(&[1, 2, 0, 1, 1, 2], &k, 24, 1, pass).expect("asked");
        bounded(&body);
        (body, vec![first, second])
    }

    /// Acceptance 1 and 3: a body read back from its text between two hearings, which then hears,
    /// asks and answers, is the never-stopped sibling in its whole text and its releases, and every
    /// current holds its pending class and at most one open section after every operation.
    #[test]
    fn a_body_rested_between_hearings_is_the_sibling_that_never_stopped() {
        let (never, a) = live(&mut tiny_body(), false);
        let (rested, b) = live(&mut tiny_body(), true);
        assert_eq!(rested.to_text(), never.to_text());
        assert_eq!(a, b);
        assert!(never.drawn() > 0 && never.learner.to_text() != tiny_body().learner.to_text());
        // The learner's swell is the last section's receipt reading, not material, and its text
        // does not carry it; the text is the body's rest.
        assert_eq!(TowerBody::from_text(&never.to_text()).expect("restored").to_text(), never.to_text());
    }

    /// Acceptance 4 and 5: an ask moves no material and returns the participation at its opening
    /// over the open section's sites; an answer's sections compare its places and its end letter
    /// alone, so its code counts exactly them.
    #[test]
    fn an_ask_moves_no_material_and_an_answer_is_compared_at_its_target() {
        let mut body = tiny_body();
        let pass = &mut HostPass::default();
        body.hear(&passage(150, 1), pass).expect("heard");
        let material = body.learner.to_text();
        let asked = body.ask(&[1, 2, 0, 1, 1, 2, 0, 0, 1], &keys(4096), 30, 2, pass).expect("asked");
        assert_eq!(body.learner.to_text(), material, "an ask moves no material");
        assert_eq!(asked.hearing.learned, 0, "a prompt is heard, never compared");
        let read = asked.participation.expect("participating");
        assert_eq!(read.levels.len(), body.learner.tower.declaration.levels);
        for (heads, arrivals) in read.levels.iter().zip(&read.arrivals) {
            for part in heads {
                assert_eq!(part.weights.len(), asked.read.len(), "one weight a site of the open section, the opening's own last");
            }
            let every: Vec<Option<usize>> = (0..asked.read.len()).map(Some).collect();
            assert_eq!(arrivals, &every, "without a clock each arrival admits one site");
        }
        assert_eq!(asked.read.last(), Some(&3));
        // The answer closes the conversation's section: of its sixteen read places, the answer's
        // eleven and its end letter are compared.
        let pending = body.conversation().pending.len();
        let answer: Vec<usize> = vec![2, 2, 1, 0, 2, 1, 1, 0, 2, 2, 1];
        let heard = body.answer(&answer, pass).expect("answered");
        assert_eq!(heard.learned, (pending + answer.len() + 1 - 1) / 16);
        let compared = (pending - 1 + answer.len() + 1).min(16) - (pending - 1).min(16);
        assert_eq!(heard.cells, compared);
        assert_ne!(body.learner.to_text(), material, "an answer deposits");
        let plain = TowerBody::found(TowerLearner::new(tiny_contacts(2, 4, 4, true, false, false, ContactLaw::Rectifying), 6), 2, 16).expect("founded");
        let mut plain = plain;
        assert_eq!(plain.ask(&[1, 2], &keys(512), 4, 1, pass).expect("asked").participation, None);
        assert!(plain.ask(&[1, 3], &keys(512), 4, 1, pass).is_err(), "a prompt holding the end letter");
    }

    /// The growth's acceptance 5: a grown body's ask releases what the body's releases, each head
    /// copy's participation the old head's, its text re-encodes, and it hears on.
    #[test]
    fn a_grown_body_releases_what_the_body_releases() {
        let mut body = tiny_body();
        let pass = &mut HostPass::default();
        body.hear(&passage(150, 1), pass).expect("heard");
        let mut grown = body.clone();
        grown.grow(2, &keys(1 << 16)).expect("grown");
        assert_eq!(grown.learner.tower.declaration.modes, 2 * body.learner.tower.declaration.modes);
        let k = keys(4096);
        let (old, new) = (body.ask(&[1, 2, 0, 1, 1, 2], &k, 24, 1, pass).expect("asked"), grown.ask(&[1, 2, 0, 1, 1, 2], &k, 24, 1, pass).expect("asked"));
        assert_eq!((&new.released, new.ended, &new.read), (&old.released, old.ended, &old.read));
        let (old_levels, new_levels) = (old.participation.expect("participating").levels, new.participation.expect("participating").levels);
        for (o, g) in old_levels.iter().zip(&new_levels) {
            assert_eq!(g.len(), 2 * o.len());
            for (h, part) in g.iter().enumerate() {
                assert_eq!(part, &o[h % o.len()], "a head copy reads the old head's sites");
            }
        }
        let text = grown.to_text();
        assert_eq!(TowerBody::from_text(&text).expect("restored").to_text(), text);
        let heard = grown.hear(&passage(97, 2), pass).expect("heard");
        assert!(heard.learned > 0);
    }

    /// A state's text restores every part, a credit-carrying stream's moments and an open face and
    /// section among them, and is refused at the wrong extent.
    #[test]
    fn a_states_text_restores_it_whole() {
        let tower = tiny_participating(ContactLaw::Rectifying, true);
        let mut state = tower.rest_with_credit();
        for &u in &[1, 2, 0, 1, 1] {
            tower.advance(&mut state, u).expect("advance");
        }
        state.open = Some(TowerFace { masses: vec![1, 2, 3, 4], total: 10 });
        assert!(state.sites.iter().all(|s| s.len() == 5));
        let text = state.to_text();
        let lines: Vec<&str> = text.lines().collect();
        assert_eq!(tower.state_from_text(&lines).expect("restored"), state);
        let mut short = lines.clone();
        short[1] = "modes 1 2";
        assert!(tower.state_from_text(&short).is_err());
    }

    /// [agent-inferred, October 29] Acceptance 5 of the record
    /// `2026-10-29_A_COARSE_LEVELS_SITES_ARE_ITS_OWN_TICKS…`: under a news clock each level carries
    /// its own count of open sites and its held current, and the state's text restores them whole.
    #[test]
    fn a_clocked_states_text_restores_each_levels_sites_and_held_current() {
        let tower = tiny_clocked_participating(ContactLaw::Rectifying, false, 3);
        let mut state = tower.rest();
        for &u in &[1, 2, 0, 1, 1, 3, 2, 2, 0, 1, 2, 1, 0, 0, 3, 1, 2, 2, 1, 0, 1, 2] {
            tower.advance(&mut state, u).expect("advance");
        }
        assert_ne!(state.sites[0].len(), state.sites[1].len(), "the levels' counts differ");
        assert!(state.sites.iter().all(|s| s.current.iter().any(|&c| c != (0, 0))), "each level holds a current");
        let text = state.to_text();
        let lines: Vec<&str> = text.lines().collect();
        assert_eq!(tower.state_from_text(&lines).expect("restored"), state);
    }
}
