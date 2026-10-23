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
use super::modes_train::{lock_bin, lock_bins};
use super::tower_train::{agreement, agreement_face, per, region_line, roles_of};
use super::*;
use holonics::hnn::keyed_modes::{Declaration, Grains, JoinedFace, KeyedLearner, KeyedModes, Lock, PassageReading};
use holonics::hnn::passage::{log2_face, PassageDeclaration, PassageTree};
use holonics::hnn::tower::{cell_phases, code_of, unit_of, Tower, TowerFace, TowerLearner};
use holonics::hnn::units::Units;

const COPY_MAGIC: &str = "complete-language-unit-copy-v1";
/// A tower state's read ceiling, `2^30` bytes.
const STATE_BUDGET: usize = 1 << 30;
/// The cells a section of the join's weights holds (agent-inferred: the byte join's 1,024).
const SECTION_CELLS: usize = 1024;
/// The passage's backoff, one occurrence of the parent's face (as the byte route).
const PASSAGE_BACKOFF: u64 = 1;

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

/// A weight on `2^(−30)` written to thousandths.
fn weight(a: i128) -> String {
    let t = (a * 1000) >> 30;
    format!("{}{}.{:03}", if t < 0 { "-" } else { "" }, t.abs() / 1000, t.abs() % 1000)
}

/// [definition; agent-inferred] **The copy contact**: the keyed join's weights, the passage tree,
/// the last `depth` cells (oldest first), the cells taken and the run of correct locks.
struct Contact {
    learner: KeyedLearner,
    passage: PassageTree,
    depth: usize,
    phases: usize,
    register: Vec<usize>,
    position: usize,
    run: u64,
}

/// One cell's reading: the tower's cell face, the passage's reading over it and the joined face.
struct CellReading {
    q: [u128; 4],
    passage: PassageReading,
    joined: JoinedFace,
}

fn opened_passage(depth: usize, horizon: u32, phases: usize) -> Result<PassageTree> {
    Ok(PassageTree::new(PassageDeclaration { alphabet: 4, phases, depth, horizon, backoff: PASSAGE_BACKOFF })?)
}

impl Contact {
    fn open(learner: KeyedLearner, depth: usize, horizon: u32, phases: usize) -> Result<Self> {
        Ok(Self { learner, passage: opened_passage(depth, horizon, phases)?, depth, phases, register: Vec::with_capacity(depth + 1), position: 0, run: 0 })
    }

    fn founded(depth: usize, horizon: u32, phases: usize) -> Result<Self> {
        let modes = KeyedModes::new(Declaration { modes: 0, alphabet: 4, evidence: depth + 2, locks: lock_bins(depth), grains: Grains::DECLARED })?;
        Self::open(KeyedLearner::new(modes), depth, horizon, phases)
    }

    fn context(&self) -> Vec<usize> {
        self.register.iter().rev().copied().collect()
    }

    fn read(&self, q: [u128; 4]) -> Result<CellReading> {
        let local = self.passage.face(self.position % self.phases, &self.context(), self.position as u64, &q)?;
        let exponent = self.learner.modes.declaration.grains.exponent;
        // The passage's term is its log ratio to the tower: p̂ ∝ q (p_loc / q)^α.
        let passage = PassageReading {
            logs: local.probabilities.iter().zip(&q).map(|(&p, &t)| log2_face(p.max(1), exponent) - log2_face(t.max(1), exponent)).collect(),
            evidence: local.evidence,
            lock: local.lock.map(|(class, d)| Lock { class, bin: lock_bin(self.run, self.depth, d) }),
        };
        let joined = self.learner.face(&q, Some(&passage))?;
        Ok(CellReading { q, passage, joined })
    }

    /// The class arrives: with `learning`, the weights receive the comparison its reading made
    /// (a cell taken without a reading moves only the passage); the passage counts it when it was
    /// `received` from the world; a section closes every [`SECTION_CELLS`] cells.
    fn take(&mut self, reading: Option<CellReading>, class: usize, learning: bool, received: bool) -> Result<()> {
        if let Some(reading) = reading {
            self.run = match reading.passage.lock {
                Some(lock) if lock.class == class => self.run + 1,
                _ => 0,
            };
            if learning {
                self.learner.receive(reading.q.to_vec(), Some(reading.passage), &reading.joined, class);
            }
        }
        let now = self.position as u64;
        if received {
            self.passage.deposit(self.position % self.phases, &self.context(), class, now)?;
        }
        if (self.position + 1) % (1 << self.passage.declaration.horizon) == 0 {
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
/// OUT`: the frozen tower reads the text in the units from rest, the copy contact's weights open
/// at zero and learn along the reading, and each unit after the first is coded by the tower's face
/// alone and by the joined face, per region of its first byte and over the bytes it decodes to.
/// The weights rest in `OUT/COPY`.
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
    let phases = cell_phases(units.len());
    let mut contact = Contact::founded(depth, horizon, phases)?;
    println!(
        "COPY_READ_OPEN units={} text_bytes={} text_units={} cells_a_unit={phases} depth={depth} horizon=2^{horizon} section_cells={SECTION_CELLS}",
        units.len(), text.len(), classes.len()
    );
    // [tower, joined] per region on 2^(−20) bits, and the bytes coded.
    let mut codes = [[(0i64, 0usize); 4]; 2];
    let (mut window, mut window_bytes, mut window_units) = ([0i64; 2], 0usize, 0u128);
    let (mut locked, mut locked_right, mut read_cells) = (0u64, 0u64, 0u64);
    let mut state = tower.rest();
    let mut at = 0usize;
    for d in contact.cells(classes[0]).collect::<Vec<_>>() {
        contact.take(None, d, true, true)?;
    }
    at += units.piece(classes[0]).len();
    let mut face = tower.advance(&mut state, classes[0]).map_err(|e| e.to_string())?;
    let mut window_started = Instant::now();
    for (i, &u) in classes.iter().enumerate().skip(1) {
        let region = byte_roles[at] as usize;
        let bytes = units.piece(u).len();
        let mut prefix = 0usize;
        for (phase, d) in contact.cells(u).collect::<Vec<_>>().into_iter().enumerate() {
            let q = cell_face(&face, prefix, phase, phases)?;
            let reading = contact.read(q)?;
            let alone = code_of(q[d], q.iter().sum());
            let joined = code_of(reading.joined.masses[d], reading.joined.total);
            codes[0][region].0 += alone;
            codes[1][region].0 += joined;
            window[0] += alone;
            window[1] += joined;
            read_cells += 1;
            if let Some(lock) = reading.passage.lock {
                locked += 1;
                locked_right += u64::from(lock.class == d);
            }
            contact.take(Some(reading), d, true, true)?;
            prefix = (prefix << 2) | d;
        }
        codes[0][region].1 += bytes;
        codes[1][region].1 += bytes;
        window_bytes += bytes;
        window_units += 1;
        at += bytes;
        face = tower.advance(&mut state, u).map_err(|e| e.to_string())?;
        if i % 8192 == 0 || i + 1 == classes.len() {
            println!(
                "COPY_READ units={}/{} window_tower={} window_joined={} locked={} lock_right={} passage_nodes={} us_a_unit={} elapsed_ms={}",
                i + 1, classes.len(), per(window[0], window_bytes), per(window[1], window_bytes),
                per((locked as i64) << 20, read_cells as usize), per((locked_right as i64) << 20, locked.max(1) as usize),
                contact.passage.len(), window_started.elapsed().as_micros() / window_units, started.elapsed().as_millis()
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
    let modes = &contact.learner.modes;
    let evidence: Vec<String> = modes.passage.iter().map(|a| weight(a.re)).collect();
    let quarters = depth / 4 + 1;
    let locks: Vec<String> = modes.lock.chunks(quarters).map(|octave| octave.iter().map(|a| weight(a.re)).collect::<Vec<_>>().join(",")).collect();
    println!("COPY_WEIGHTS evidence=[{}] lock=[{}]", evidence.join(","), locks.join(";"));
    let text = format!("{COPY_MAGIC}\n{depth} {horizon} {phases}\n{}", contact.learner.to_text()?);
    write_new(&out.join("COPY"), text.as_bytes())?;
    println!("COPY_DONE copy_bytes={} copy_sha256={} elapsed_ms={}", text.len(), sha256(text.as_bytes())?, started.elapsed().as_millis());
    Ok(())
}

/// `sample-unit-copy UNITS UNITS_SHA TOWER TOWER_SHA COPY COPY_SHA PROMPT PROMPT_SHA KEYS KEYS_SHA
/// BYTES OUT [AGREE]`: the tower and the weights frozen, the passage opened at the prompt, which
/// it receives; then units are released cell by cell, each cell drawn exactly from the joined face
/// (at `AGREE` agreeing draws) and not received, until the declared bytes are released.
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
    let [depth, horizon, phases] = declared[..] else { return Err("the copy's declaration".into()) };
    if phases != cell_phases(units.len()) {
        return Err("the copy's cell chart is not the units'".into());
    }
    let learner = KeyedLearner::from_text(lines.next().ok_or("the copy's weights")?)?;
    let mut contact = Contact::open(learner, depth, u32::try_from(horizon)?, phases)?;
    let prompt = pinned_read(&args[7], &args[8], QUERY_BYTE_BUDGET)?;
    let keys = pinned_read(&args[9], &args[10], READ_BUDGET as usize)?;
    let count: usize = args[11].parse()?;
    let out = Path::new(&args[12]);
    std::fs::create_dir(out)?;
    let classes: Vec<usize> = units.parse(&prompt).map_err(|e| e.to_string())?.into_iter().map(|u| u as usize).collect();
    let (&first, rest) = classes.split_first().ok_or("an empty prompt")?;
    let mut state = tower.rest();
    for d in contact.cells(first).collect::<Vec<_>>() {
        contact.take(None, d, false, true)?;
    }
    let mut face = tower.advance(&mut state, first).map_err(|e| e.to_string())?;
    // The prompt's later units are read, so the run of correct locks is the prompt's own.
    for &u in rest {
        let mut prefix = 0usize;
        for (phase, d) in contact.cells(u).collect::<Vec<_>>().into_iter().enumerate() {
            let reading = contact.read(cell_face(&face, prefix, phase, phases)?)?;
            contact.take(Some(reading), d, false, true)?;
            prefix = (prefix << 2) | d;
        }
        face = tower.advance(&mut state, u).map_err(|e| e.to_string())?;
    }
    let mut key_stream = KeyStream::new(keys, 8)?;
    let mut released = Vec::with_capacity(count);
    let (mut released_units, mut locked_draws) = (0usize, 0usize);
    while released.len() < count {
        let mut prefix = 0usize;
        for phase in 0..phases {
            let key = key_stream.next_key().ok_or("fewer keys than the release's cells")?;
            let reading = contact.read(cell_face(&face, prefix, phase, phases)?)?;
            let d = holonics::receiver::release::draw_exact(&agreement_face(&reading.joined.masses, agree), &key)?
                .drawn_class()
                .ok_or("an unresolved draw at an exact face")?;
            locked_draws += usize::from(reading.passage.lock.is_some_and(|l| l.class == d));
            contact.take(Some(reading), d, false, false)?;
            prefix = (prefix << 2) | d;
        }
        if prefix >= units.len() {
            return Err("a release past the units' alphabet".into());
        }
        released.extend_from_slice(units.piece(prefix));
        released_units += 1;
        face = tower.advance(&mut state, prefix).map_err(|e| e.to_string())?;
    }
    write_new(&out.join("OUTPUT.bin"), &released)?;
    println!(
        "COPY_SAMPLE prompt_units={} units={} bytes={} cells_on_the_lock={}/{} agree={} elapsed_ms={}",
        classes.len(), released_units, released.len(), locked_draws, released_units * phases, agree, started.elapsed().as_millis()
    );
    println!("COPY_SAMPLE_TEXT {:?}", String::from_utf8_lossy(&released));
    Ok(())
}
