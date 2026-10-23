//! The founded units' tower joined to the passage's copy contact: read a held-out text, then
//! release a continuation.
//!
//! [definition; agent-inferred, October 23] The units' tower (`holonics::hnn::tower`, reading the
//! founded units of `holonics::hnn::units`) predicts the next unit from its modes, whose memory
//! fades: its samples drift off the question's subject and open new problems. The passage tree
//! (`holonics::hnn::passage`) holds what the passage itself just said: decayed counts of what
//! followed each recent context, and the lock, the class that followed the deepest visited
//! context's last visit (the located equality). The tower's face is read in the cell chart
//! (`TowerFace::cell_masses`: a unit index in six base-four cells, high first), and at each cell
//! the keyed join (`holonics::hnn::keyed_modes` with no modes) reads
//!
//! ```text
//! p̂(d) ∝ q_d 2^(α_e f_d + α_b [d = ĉ])
//! ```
//!
//! `q` the tower's cell face, `f` the passage's news over it at its evidence depth `e`, `ĉ` the
//! lock in its bin `b` (the octave of the run of correct locks and the quarter of the locating
//! depth). The weights open at zero, where the joined face is the tower's, and take the keyed
//! join's Newton step every 1,024 cells. The reading is prequential: each cell's face is read
//! before its class arrives; then the weights receive the comparison and the passage counts the
//! class. A sample forks the frozen tower and the frozen weights: the passage opens at the prompt
//! and receives it, and each released cell is drawn exactly and not received (a release read back
//! as evidence is reafference: the passage then repeats what it released).
//!
//! [definition; agent-inferred, October 23] **The located copy at the letters.** A unit hides the
//! equalities of the letters it is made of: `?\n` and `\n\n` are two units, so the answer's
//! opening (after `?\n`) meets no unit context that its question's opening (after `\n\n`) also
//! met, and the units' lock cannot carry the question's subject into its answer. A second passage
//! tree reads the same passage at the letters (each byte in four base-four cells, eight bytes deep),
//! and the copy is its lock run forward through its own kept classes: the located continuation,
//! letter after letter, to one byte past the units' longest piece. Read in the units
//! (`Units::parse`), its first unit `û` is the copy's proposal for the next unit, and `û`'s cells are
//! the lock at each cell whose prefix agrees with `û`'s. Of the two locks the one located on the
//! longer equality, measured in letters, stands (the deepest located equality across the two charts,
//! as each tree takes its own deepest node). The copy's weight sits in a bin of the run of correct
//! copied cells, the visits of the context it located (one visit locates one place; a plural context
//! keeps only its latest continuation) and the tower's surprise at `û` (`⌊−log₂ p(û)⌋`, by octave): a
//! copy is worth what the tower does not already say. A passage opens at each problem on the frame
//! the prepared text puts before every question (the exterior codec's problem separator), so a
//! question's opening is a located context for its answer's opening, and the weights learn in the
//! read under the opening a sample meets.
//!
//! [definition; agent-inferred, October 23] **The passage is trusted where the tower is unsure.**
//! Half the held-out answers open on a capitalized word of their own question (378 of 747, 151 of
//! them its first word), mostly a name, while the tower opens with a name of its own: it holds that
//! a name comes, not which. At a cell whose context is the unit's own prefix the passage's face is
//! its count of the units this problem said, and its news over the tower is large exactly at such a
//! name. The news weight `α_e` sits in a slot of the evidence depth and the tower's uncertainty at
//! the unit's opening (the surprise octave of its own likeliest unit), so the passage can weigh
//! heavily where the tower spreads its face over many units and lightly where the tower is sure.

use super::modes_train::{lock_bin, lock_bins, run_octave, LOCK_OCTAVES};
use super::tower_train::{agreement, agreement_face, per, region_line, roles_of};
use super::*;
use holonics::hnn::keyed_modes::{Declaration, Grains, JoinedFace, KeyedLearner, KeyedModes, Lock, PassageReading};
use holonics::hnn::passage::{log2_face, PassageDeclaration, PassageTree};
use holonics::hnn::tower::{cell_phases, code_of, unit_of, Tower, TowerFace, TowerLearner};
use holonics::hnn::units::Units;

const COPY_MAGIC: &str = "complete-language-unit-copy-v3";
/// A tower state's read ceiling, `2^30` bytes.
const STATE_BUDGET: usize = 1 << 30;
/// The cells a section of the join's weights holds (agent-inferred: the byte join's 1,024).
const SECTION_CELLS: usize = 1024;
/// The passage's backoff, one occurrence of the parent's face (as the byte route).
const PASSAGE_BACKOFF: u64 = 1;
/// The frame the prepared text puts before every question (the exterior codec's problem
/// separator, checked at every question of a read): a passage opens on it.
const FRAME: &[u8] = b"\n\n";
/// The letters' depth in bytes (the node-lock record: context past eight characters adds nothing).
const LETTER_BYTES: usize = 8;
/// The surprise octaves: `⌊−log₂ p⌋` on the face's `2^(−62)` grain is at most 62, six bits.
const SURPRISE_OCTAVES: usize = 7;

/// The tower's cell face on `2^(−62)`: each cell's share of its prefix's mass, at least one grain
/// where the cell holds a class of the alphabet and none where it holds none, so no release
/// reaches past the alphabet.
fn cell_face(face: &TowerFace, prefix: usize, phase: usize, phases: usize) -> Result<[u128; 4]> {
    let cells = face.cell_masses(prefix, phase).map_err(|e| e.to_string())?;
    let total: u128 = cells.iter().sum();
    let low = 2 * (phases - 1 - phase);
    let mut q = [0u128; 4];
    for (d, slot) in q.iter_mut().enumerate() {
        if ((prefix << 2) | d) << low < face.masses.len() {
            *slot = unit_of(cells[d], total);
        }
    }
    Ok(q)
}

/// The octave of the tower's surprise at `u`: the bit length of `⌊−log₂ p(u)⌋`.
fn surprise_octave(face: &TowerFace, u: usize) -> usize {
    let p = unit_of(face.masses[u], face.total).max(1);
    let bits = 127 - p.leading_zeros() as usize; // ⌊log₂ p⌋ on 2^(−62), at most 62
    (usize::BITS - (62 - bits).leading_zeros()) as usize
}

/// The octave of the tower's uncertainty at a unit's opening: its surprise at its own likeliest
/// unit (zero where the tower is sure; high where many units share the face, as names and
/// quantities do).
fn uncertainty_octave(face: &TowerFace) -> usize {
    let likeliest = (0..face.masses.len()).max_by_key(|&u| face.masses[u]).unwrap_or(0);
    surprise_octave(face, likeliest)
}

/// A weight on `2^(−30)` written to thousandths.
fn weight(a: i128) -> String {
    let t = (a * 1000) >> 30;
    format!("{}{}.{:03}", if t < 0 { "-" } else { "" }, t.abs() / 1000, t.abs() % 1000)
}

/// [definition; agent-inferred] **The letters' copy at a unit's opening**: the proposed unit `û`,
/// the letters it located on, that context's visits and the tower's surprise octave at `û`.
#[derive(Clone, Copy)]
struct Copied {
    unit: usize,
    located: usize,
    visits: u64,
    surprise: usize,
}

/// [definition; agent-inferred] **The copy contact**: the keyed join's weights, the units' passage
/// and the letters' passage, their last cells (oldest first), the units taken (newest last), the
/// cells taken in each chart, the runs of correct locks and the copy at the next unit's opening.
struct Contact {
    learner: KeyedLearner,
    passage: PassageTree,
    letters: PassageTree,
    depth: usize,
    horizon: u32,
    phases: usize,
    register: Vec<usize>,
    spelled: Vec<usize>,
    taken: Vec<usize>,
    position: usize,
    spelled_position: usize,
    run: u64,
    copy_run: u64,
    copy: Option<Copied>,
    uncertainty: usize,
    longest: usize,
}

/// One cell's reading: the tower's cell face, the passage's reading over it, the joined face, the
/// units' lock and the copy's class at this cell.
struct CellReading {
    q: [u128; 4],
    passage: PassageReading,
    joined: JoinedFace,
    unit_lock: Option<usize>,
    copied: Option<usize>,
}

fn opened_passage(depth: usize, horizon: u32, phases: usize) -> Result<PassageTree> {
    Ok(PassageTree::new(PassageDeclaration { alphabet: 4, phases, depth, horizon, backoff: PASSAGE_BACKOFF })?)
}

/// The cells of a byte, base four.
fn letter_cells() -> usize {
    cell_phases(256)
}

impl Contact {
    fn open(learner: KeyedLearner, depth: usize, horizon: u32, phases: usize, longest: usize) -> Result<Self> {
        if learner.modes.declaration.locks != Self::bins(depth) || learner.modes.declaration.evidence != Self::slots(depth) {
            return Err("the copy's lock bins or evidence slots are not its declaration's".into());
        }
        Ok(Self {
            learner,
            passage: opened_passage(depth, horizon, phases)?,
            letters: opened_passage(LETTER_BYTES * letter_cells(), horizon, letter_cells())?,
            depth,
            horizon,
            phases,
            register: Vec::with_capacity(depth + 1),
            spelled: Vec::with_capacity(LETTER_BYTES * letter_cells() + 1),
            taken: Vec::new(),
            position: 0,
            spelled_position: 0,
            run: 0,
            copy_run: 0,
            copy: None,
            uncertainty: 0,
            longest,
        })
    }

    /// The lock bins: the units' (run octave by depth quarter), then the copy's (run octave by
    /// visits octave by surprise octave).
    fn bins(depth: usize) -> usize {
        lock_bins(depth) + LOCK_OCTAVES * LOCK_OCTAVES * SURPRISE_OCTAVES
    }

    /// The evidence slots: the passage's evidence depth by the tower's uncertainty octave.
    fn slots(depth: usize) -> usize {
        (depth + 2) * SURPRISE_OCTAVES
    }

    fn founded(depth: usize, horizon: u32, phases: usize, longest: usize) -> Result<Self> {
        let modes = KeyedModes::new(Declaration { modes: 0, alphabet: 4, evidence: Self::slots(depth), locks: Self::bins(depth), grains: Grains::DECLARED })?;
        Self::open(KeyedLearner::new(modes), depth, horizon, phases, longest)
    }

    /// Both passages open again, empty; the weights, the clocks and the cell phases continue.
    fn reopen(&mut self) -> Result<()> {
        self.passage = opened_passage(self.depth, self.horizon, self.phases)?;
        self.letters = opened_passage(LETTER_BYTES * letter_cells(), self.horizon, letter_cells())?;
        self.register.clear();
        self.spelled.clear();
        self.taken.clear();
        (self.run, self.copy_run, self.copy) = (0, 0, None);
        Ok(())
    }

    /// The passages open on the frame: its units and letters are received, unread.
    fn frame(&mut self, units: &Units, learning: bool) -> Result<()> {
        self.reopen()?;
        for u in units.parse(FRAME).map_err(|e| e.to_string())? {
            for d in self.cells(u as usize).collect::<Vec<_>>() {
                self.take(None, d, learning, true)?;
            }
            self.spell(units, u as usize, true)?;
        }
        Ok(())
    }

    fn context(&self) -> Vec<usize> {
        self.register.iter().rev().copied().collect()
    }

    /// The letters a unit lock located on: the whole units behind the located cells.
    fn unit_span(&self, located: usize, phase: usize, units: &Units) -> usize {
        let whole = located.saturating_sub(phase) / self.phases;
        self.taken.iter().rev().take(whole).map(|&u| units.piece(u).len()).sum()
    }

    fn read(&self, q: [u128; 4], prefix: usize, phase: usize, units: &Units) -> Result<CellReading> {
        let local = self.passage.face(self.position % self.phases, &self.context(), self.position as u64, &q)?;
        let exponent = self.learner.modes.declaration.grains.exponent;
        let low = 2 * (self.phases - phase);
        let copy = self.copy.filter(|c| c.unit >> low == prefix);
        let copied = copy.map(|c| (c.unit >> (low - 2)) & 3);
        let unit_lock = local.lock.map(|(class, d)| (class, d));
        // The lock on the longer located equality stands, in letters; the copy at a tie.
        let lock = match (copy, unit_lock) {
            (Some(c), Some((_, d))) if self.unit_span(d, phase, units) > c.located => unit_lock.map(|(class, d)| Lock { class, bin: lock_bin(self.run, self.depth, d) }),
            (Some(c), _) => Some(Lock {
                class: copied.expect("a copy at its prefix"),
                bin: lock_bins(self.depth) + (run_octave(self.copy_run) * LOCK_OCTAVES + run_octave(c.visits)) * SURPRISE_OCTAVES + c.surprise,
            }),
            (None, _) => unit_lock.map(|(class, d)| Lock { class, bin: lock_bin(self.run, self.depth, d) }),
        };
        // The passage's term is its log ratio to the tower: p̂ ∝ q (p_loc / q)^α. A cell past the
        // alphabet holds no class, so the passage has no news there (a shallow node counts cells of
        // other prefixes, and its share past the alphabet would otherwise outweigh every class).
        let passage = PassageReading {
            logs: local
                .probabilities
                .iter()
                .zip(&q)
                .map(|(&p, &t)| if t == 0 { 0 } else { log2_face(p.max(1), exponent) - log2_face(t, exponent) })
                .collect(),
            evidence: local.evidence * SURPRISE_OCTAVES + self.uncertainty,
            lock,
        };
        let joined = self.learner.face(&q, Some(&passage))?;
        Ok(CellReading { q, passage, joined, unit_lock: unit_lock.map(|(class, _)| class), copied })
    }

    /// The class arrives: with `learning`, the weights receive the comparison its reading made
    /// (a cell taken without a reading moves only the passage); the passage counts it when it was
    /// `received` from the world; a section closes every [`SECTION_CELLS`] cells.
    fn take(&mut self, reading: Option<CellReading>, class: usize, learning: bool, received: bool) -> Result<()> {
        if let Some(reading) = reading {
            self.run = if reading.unit_lock == Some(class) { self.run + 1 } else { 0 };
            self.copy_run = if reading.copied == Some(class) { self.copy_run + 1 } else { 0 };
            if learning {
                self.learner.receive(reading.q.to_vec(), Some(reading.passage), &reading.joined, class);
            }
        }
        let now = self.position as u64;
        if received {
            self.passage.deposit(self.position % self.phases, &self.context(), class, now)?;
        }
        if (self.position + 1) % (1 << self.horizon) == 0 {
            self.passage.release(now);
        }
        self.register.push(class);
        if self.register.len() > self.depth {
            self.register.remove(0);
        }
        self.position += 1;
        if learning && self.position % SECTION_CELLS == 0 {
            self.learner.close()?;
        }
        Ok(())
    }

    /// The unit `u` complete: its letters enter the letters' passage, counted when `received`.
    fn spell(&mut self, units: &Units, u: usize, received: bool) -> Result<()> {
        let (cells, depth) = (letter_cells(), LETTER_BYTES * letter_cells());
        for &byte in units.piece(u) {
            for k in 0..cells {
                let class = (byte as usize >> (2 * (cells - 1 - k))) & 3;
                let now = self.spelled_position as u64;
                if received {
                    let context: Vec<usize> = self.spelled.iter().rev().copied().collect();
                    self.letters.deposit(self.spelled_position % cells, &context, class, now)?;
                }
                if (self.spelled_position + 1) % (1 << self.horizon) == 0 {
                    self.letters.release(now);
                }
                self.spelled.push(class);
                if self.spelled.len() > depth {
                    self.spelled.remove(0);
                }
                self.spelled_position += 1;
            }
        }
        self.taken.push(u);
        if self.taken.len() > self.depth {
            self.taken.remove(0);
        }
        Ok(())
    }

    /// The copy at the next unit's opening, under the tower's `face`: the letters' lock run forward
    /// through its own kept classes to one byte past the longest piece, read in the units; and the
    /// tower's uncertainty there, which keys the passage's evidence weight.
    fn locate(&mut self, units: &Units, face: &TowerFace) -> Result<()> {
        self.uncertainty = uncertainty_octave(face);
        let (cells, depth) = (letter_cells(), LETTER_BYTES * letter_cells());
        let now = self.spelled_position as u64;
        let mut context: Vec<usize> = self.spelled.iter().rev().copied().collect();
        let (mut bytes, mut opening) = (Vec::with_capacity(self.longest + 1), None);
        'copy: while bytes.len() <= self.longest {
            let mut byte = 0usize;
            for k in 0..cells {
                let Some((class, located, visits)) = self.letters.lock((self.spelled_position + k) % cells, &context, now)? else {
                    break 'copy;
                };
                opening.get_or_insert((located, visits));
                byte = (byte << 2) | class;
                context.insert(0, class);
                context.truncate(depth);
            }
            bytes.push(byte as u8);
        }
        self.copy = match (bytes.is_empty(), opening) {
            (false, Some((located, visits))) => units.parse(&bytes).map_err(|e| e.to_string())?.first().map(|&u| Copied {
                unit: u as usize,
                located: located / cells,
                visits,
                surprise: surprise_octave(face, u as usize),
            }),
            _ => None,
        };
        Ok(())
    }

    /// The unit `u`'s cells, high first.
    fn cells(&self, u: usize) -> impl Iterator<Item = usize> + '_ {
        (0..self.phases).map(move |k| (u >> (2 * (self.phases - 1 - k))) & 3)
    }
}

fn rested_tower(path: &str, sha: &str, units: &Units) -> Result<Tower> {
    let text = pinned_read(path, sha, STATE_BUDGET)?;
    let tower = TowerLearner::from_text(std::str::from_utf8(&text)?).map_err(|e| e.to_string())?.tower;
    if tower.declaration.alphabet != units.len() {
        return Err("the tower's alphabet is not the units'".into());
    }
    Ok(tower)
}

fn read_units(path: &str, sha: &str) -> Result<Units> {
    Ok(Units::from_text(std::str::from_utf8(&pinned_read(path, sha, READ_BUDGET as usize)?)?).map_err(|e| e.to_string())?)
}

/// `read-unit-copy UNITS UNITS_SHA TOWER TOWER_SHA TEXT TEXT_SHA ROLES ROLES_SHA DEPTH HORIZON
/// OUT`: the frozen tower reads the text in the units from rest; the copy contact's passages open on
/// the frame at each question (a question that does not open a unit after the frame is refused);
/// its weights open at zero and learn along the reading. Each unit after the first is coded by the
/// tower's face alone and by the joined face, per region of its first byte and over the bytes it
/// decodes to, and at each answer's opening (the first unit past its question) the copy's proposal
/// is read beside the unit that came. The weights rest in `OUT/COPY`.
pub(super) fn read(args: &[String]) -> Result<()> {
    if args.len() != 12 {
        return Err("read-unit-copy UNITS UNITS_SHA TOWER TOWER_SHA TEXT TEXT_SHA ROLES ROLES_SHA DEPTH HORIZON OUT".into());
    }
    let started = Instant::now();
    let units = read_units(&args[1], &args[2])?;
    let tower = rested_tower(&args[3], &args[4], &units)?;
    let text = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let byte_roles = roles_of(&args[7], &args[8], text.len())?;
    let depth: usize = args[9].parse()?;
    let horizon: u32 = args[10].parse()?;
    let out = Path::new(&args[11]);
    std::fs::create_dir(out)?;
    let classes: Vec<usize> = units.parse(&text).map_err(|e| e.to_string())?.into_iter().map(|u| u as usize).collect();
    if classes.len() < 2 {
        return Err("a reading needs two units".into());
    }
    let questions: Vec<usize> = (0..text.len()).filter(|&i| byte_roles[i] == 0 && (i == 0 || byte_roles[i - 1] != 0)).collect();
    if questions.first() != Some(&0) || questions[1..].iter().any(|&q| q < FRAME.len() || &text[q - FRAME.len()..q] != FRAME) {
        return Err("a read opens at a question, and every later question follows the frame".into());
    }
    let longest = longest_piece(&units);
    let phases = cell_phases(units.len());
    let mut contact = Contact::founded(depth, horizon, phases, longest)?;
    println!(
        "COPY_READ_OPEN units={} text_bytes={} text_units={} questions={} cells_a_unit={phases} depth={depth} letters={LETTER_BYTES} longest={longest} horizon=2^{horizon} section_cells={SECTION_CELLS}",
        units.len(), text.len(), classes.len(), questions.len()
    );
    // [tower, joined] per region on 2^(−20) bits, and the bytes coded.
    let mut codes = [[(0i64, 0usize); 4]; 2];
    let (mut window, mut window_bytes, mut window_units) = ([0i64; 2], 0usize, 0u128);
    let (mut locked, mut locked_right, mut read_cells, mut copy_locks, mut copy_right) = (0u64, 0u64, 0u64, 0u64, 0u64);
    // At the answers' openings: their count, the copy's proposal that was the unit that came, and
    // the [tower, joined] code of the opening units.
    let (mut openings, mut named, mut opening_codes) = (0usize, 0usize, [0i64; 2]);
    let mut state = tower.rest();
    contact.frame(&units, true)?;
    for d in contact.cells(classes[0]).collect::<Vec<_>>() {
        contact.take(None, d, true, true)?;
    }
    contact.spell(&units, classes[0], true)?;
    let (mut at, mut next_question) = (units.piece(classes[0]).len(), 1usize);
    let mut face = tower.advance(&mut state, classes[0]).map_err(|e| e.to_string())?;
    contact.locate(&units, &face)?;
    let mut window_started = Instant::now();
    for (i, &u) in classes.iter().enumerate().skip(1) {
        let region = byte_roles[at] as usize;
        let opening = region != 0 && byte_roles[at - 1] == 0;
        if opening {
            openings += 1;
            named += usize::from(contact.copy.is_some_and(|c| c.unit == u));
        }
        let bytes = units.piece(u).len();
        let mut prefix = 0usize;
        for (phase, d) in contact.cells(u).collect::<Vec<_>>().into_iter().enumerate() {
            let q = cell_face(&face, prefix, phase, phases)?;
            let reading = contact.read(q, prefix, phase, &units)?;
            let alone = code_of(q[d], q.iter().sum());
            let joined = code_of(reading.joined.masses[d], reading.joined.total);
            codes[0][region].0 += alone;
            codes[1][region].0 += joined;
            window[0] += alone;
            window[1] += joined;
            if opening {
                opening_codes[0] += alone;
                opening_codes[1] += joined;
            }
            read_cells += 1;
            if let Some(lock) = reading.passage.lock {
                locked += 1;
                locked_right += u64::from(lock.class == d);
                if lock.bin >= lock_bins(depth) {
                    copy_locks += 1;
                    copy_right += u64::from(lock.class == d);
                }
            }
            contact.take(Some(reading), d, true, true)?;
            prefix = (prefix << 2) | d;
        }
        contact.spell(&units, u, true)?;
        codes[0][region].1 += bytes;
        codes[1][region].1 += bytes;
        window_bytes += bytes;
        window_units += 1;
        at += bytes;
        face = tower.advance(&mut state, u).map_err(|e| e.to_string())?;
        if next_question < questions.len() && at >= questions[next_question] {
            if at != questions[next_question] {
                return Err("a question that opens inside a unit".into());
            }
            contact.frame(&units, true)?;
            next_question += 1;
        }
        contact.locate(&units, &face)?;
        if i % 8192 == 0 || i + 1 == classes.len() {
            println!(
                "COPY_READ units={}/{} window_tower={} window_joined={} locked={} lock_right={} copy_locks={} copy_right={} passage_nodes={} letter_nodes={} us_a_unit={} elapsed_ms={}",
                i + 1, classes.len(), per(window[0], window_bytes), per(window[1], window_bytes),
                per((locked as i64) << 20, read_cells as usize), per((locked_right as i64) << 20, locked.max(1) as usize),
                per((copy_locks as i64) << 20, read_cells as usize), per((copy_right as i64) << 20, copy_locks.max(1) as usize),
                contact.passage.len(), contact.letters.len(), window_started.elapsed().as_micros() / window_units, started.elapsed().as_millis()
            );
            window = [0; 2];
            window_bytes = 0;
            window_units = 0;
            window_started = Instant::now();
        }
    }
    contact.learner.close()?;
    for (name, c) in ["tower", "joined"].iter().zip(&codes) {
        let total = c.iter().fold((0i64, 0usize), |a, r| (a.0 + r.0, a.1 + r.1));
        println!("COPY_READ_CODE {name} bits_a_byte={} regions {}", per(total.0, total.1), region_line(c));
    }
    println!(
        "COPY_READ_OPENINGS answers={openings} copy_named={named} tower_bits_an_opening={} joined_bits_an_opening={}",
        per(opening_codes[0], openings.max(1)), per(opening_codes[1], openings.max(1))
    );
    let modes = &contact.learner.modes;
    let evidence: Vec<String> = modes.passage.chunks(SURPRISE_OCTAVES).map(|depth| depth.iter().map(|a| weight(a.re)).collect::<Vec<_>>().join(",")).collect();
    let quarters = depth / 4 + 1;
    let (unit_locks, copy_bins) = modes.lock.split_at(lock_bins(depth));
    let locks: Vec<String> = unit_locks.chunks(quarters).map(|octave| octave.iter().map(|a| weight(a.re)).collect::<Vec<_>>().join(",")).collect();
    println!("COPY_WEIGHTS evidence_by_uncertainty=[{}] lock=[{}]", evidence.join(";"), locks.join(";"));
    for (row, surprises) in copy_bins.chunks(SURPRISE_OCTAVES).enumerate() {
        if surprises.iter().any(|a| a.re != 0) {
            let line: Vec<String> = surprises.iter().map(|a| weight(a.re)).collect();
            println!("COPY_LETTER_WEIGHTS run_octave={} visits_octave={} by_surprise_octave=[{}]", row / LOCK_OCTAVES, row % LOCK_OCTAVES, line.join(","));
        }
    }
    let text = format!("{COPY_MAGIC}\n{depth} {horizon} {phases} {LETTER_BYTES} {longest}\n{}", contact.learner.to_text()?);
    write_new(&out.join("COPY"), text.as_bytes())?;
    println!("COPY_DONE copy_bytes={} copy_sha256={} elapsed_ms={}", text.len(), sha256(text.as_bytes())?, started.elapsed().as_millis());
    Ok(())
}

/// The units' longest piece, in bytes.
fn longest_piece(units: &Units) -> usize {
    (0..units.len()).map(|u| units.piece(u).len()).max().unwrap_or(1)
}

/// `sample-unit-copy UNITS UNITS_SHA TOWER TOWER_SHA COPY COPY_SHA PROMPT PROMPT_SHA KEYS KEYS_SHA
/// BYTES OUT [AGREE]`: the tower and the weights frozen, the passages opened on the frame, then the
/// prompt, which they receive; then units are released cell by cell, each cell drawn exactly from the
/// joined face (at `AGREE` agreeing draws) and not received, until the declared bytes are released.
pub(super) fn sample(args: &[String]) -> Result<()> {
    if args.len() != 13 && args.len() != 14 {
        return Err("sample-unit-copy UNITS UNITS_SHA TOWER TOWER_SHA COPY COPY_SHA PROMPT PROMPT_SHA KEYS KEYS_SHA BYTES OUT [AGREE]".into());
    }
    let agree = agreement(args.get(13))?;
    let started = Instant::now();
    let units = read_units(&args[1], &args[2])?;
    let tower = rested_tower(&args[3], &args[4], &units)?;
    let copy = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let mut lines = std::str::from_utf8(&copy)?.splitn(3, '\n');
    if lines.next() != Some(COPY_MAGIC) {
        return Err("not a unit copy state".into());
    }
    let declared: Vec<usize> = lines.next().ok_or("the copy's declaration")?.split_whitespace().map(str::parse).collect::<std::result::Result<_, _>>()?;
    let [depth, horizon, phases, letters, longest] = declared[..] else { return Err("the copy's declaration".into()) };
    if phases != cell_phases(units.len()) || letters != LETTER_BYTES || longest != longest_piece(&units) {
        return Err("the copy's charts are not the units'".into());
    }
    let learner = KeyedLearner::from_text(lines.next().ok_or("the copy's weights")?)?;
    let mut contact = Contact::open(learner, depth, u32::try_from(horizon)?, phases, longest)?;
    let prompt = pinned_read(&args[7], &args[8], QUERY_BYTE_BUDGET)?;
    let keys = pinned_read(&args[9], &args[10], READ_BUDGET as usize)?;
    let count: usize = args[11].parse()?;
    let out = Path::new(&args[12]);
    std::fs::create_dir(out)?;
    let classes: Vec<usize> = units.parse(&prompt).map_err(|e| e.to_string())?.into_iter().map(|u| u as usize).collect();
    let (&first, rest) = classes.split_first().ok_or("an empty prompt")?;
    let mut state = tower.rest();
    contact.frame(&units, false)?;
    for d in contact.cells(first).collect::<Vec<_>>() {
        contact.take(None, d, false, true)?;
    }
    contact.spell(&units, first, true)?;
    let mut face = tower.advance(&mut state, first).map_err(|e| e.to_string())?;
    contact.locate(&units, &face)?;
    // The prompt's later units are read, so the runs of correct locks are the prompt's own.
    for &u in rest {
        let mut prefix = 0usize;
        for (phase, d) in contact.cells(u).collect::<Vec<_>>().into_iter().enumerate() {
            let reading = contact.read(cell_face(&face, prefix, phase, phases)?, prefix, phase, &units)?;
            contact.take(Some(reading), d, false, true)?;
            prefix = (prefix << 2) | d;
        }
        contact.spell(&units, u, true)?;
        face = tower.advance(&mut state, u).map_err(|e| e.to_string())?;
        contact.locate(&units, &face)?;
    }
    let mut key_stream = KeyStream::new(keys, 8)?;
    let mut released = Vec::with_capacity(count);
    let (mut released_units, mut locked_draws, mut copied_draws) = (0usize, 0usize, 0usize);
    while released.len() < count {
        let mut prefix = 0usize;
        for phase in 0..phases {
            let key = key_stream.next_key().ok_or("fewer keys than the release's cells")?;
            let reading = contact.read(cell_face(&face, prefix, phase, phases)?, prefix, phase, &units)?;
            let d = holonics::receiver::release::draw_exact(&agreement_face(&reading.joined.masses, agree), &key)?
                .drawn_class()
                .ok_or("an unresolved draw at an exact face")?;
            if let Some(lock) = reading.passage.lock.filter(|l| l.class == d) {
                locked_draws += 1;
                copied_draws += usize::from(lock.bin >= lock_bins(depth));
            }
            contact.take(Some(reading), d, false, false)?;
            prefix = (prefix << 2) | d;
        }
        if prefix >= units.len() {
            return Err("a release past the units' alphabet".into());
        }
        contact.spell(&units, prefix, false)?;
        released.extend_from_slice(units.piece(prefix));
        released_units += 1;
        face = tower.advance(&mut state, prefix).map_err(|e| e.to_string())?;
        contact.locate(&units, &face)?;
    }
    write_new(&out.join("OUTPUT.bin"), &released)?;
    println!(
        "COPY_SAMPLE prompt_units={} units={} bytes={} cells_on_the_lock={}/{} of_them_copied={} agree={} elapsed_ms={}",
        classes.len(), released_units, released.len(), locked_draws, released_units * phases, copied_draws, agree, started.elapsed().as_millis()
    );
    println!("COPY_SAMPLE_TEXT {:?}", String::from_utf8_lossy(&released));
    Ok(())
}
