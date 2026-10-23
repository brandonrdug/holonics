//! The keyed-modes route's exterior commands: train on text, then release a keyed continuation.
//!
//! [definition; agent-inferred, October 23] The route joins three owners at the receiver's face:
//! the native route's receiving tree (`Landmarks`, declared as the native route declares it, the
//! field's receiver behind the cell's source framing path, at a declared depth), the passage tree
//! (`holonics::hnn::passage`, the same contexts' counts at the passage's horizon) and the keyed
//! modes (`holonics::hnn::keyed_modes`): `p̂(c) ∝ q(c) 2^(w_c)` with
//! `w_c = (the modes' read) + α_e f_c`, `f_c = log₂ p_loc(c) − log₂ q(c)` the passage's news over
//! the tree's face (the passage backs off to the tree's face, not to a flat one). Text enters as
//! base-four cells (`Base4Bytes`), the exterior byte chart. Each cell's face is read before its
//! class arrives (the prequential code); the trees then receive the class at the context its face
//! was read at, and the modes take the class's keyed move. A section of the native route's width
//! closes with a deposit. The state rests at the corpus end. A sample is a fork of the rested
//! state: the tree and the bank are frozen, the passage opens at the prompt and receives it, and
//! each cell is released by an exact draw and is not received (reading its own release back as
//! evidence is reafference: measured, the passage then repeats what it released).
//!
//! Measured October 23 on GSM8K (online code, bits a cell): the tree alone at depths 6, 8, 12, 16,
//! 24 cells codes 0.864, 0.769, 0.650, 0.613, 0.605 on 100 problems; at depth 24 on 1,000 problems
//! 0.507, where 32 keyed modes, with or without the square law, add nothing (0.509): their memory
//! sits inside the tree's horizon. The passage's news, its weights set by the curvature step,
//! brings the 1,000 problems to 0.469 (record
//! `2026-10-23_ON_GSM8K_THE_TREE_DEPTH_CARRIES_THE_CODE_AND_THE_PASSAGE_ADDS_ITS_NEWS`).
use super::*;
use holonics::compression::landmark::context::{
    address, Landmarks, Letter, ObservationPath, ObservedAddress, TreeStanding,
};
use holonics::hnn::keyed_modes::{Declaration, Grains, JoinedFace, KeyedLearner, KeyedModes, PassageReading};
use holonics::hnn::passage::{log2_face, PassageDeclaration, PassageTree};

const STATE_MAGIC: &str = "complete-language-keyed-modes-v1";
/// The face numerators' common grain, `2^(−62)` (the modes' joined face reads `q ≤ 2^62`).
const FACE_BITS: u32 = 62;
/// The reading grain of a code length, `2^(−20)` bits (a reading beside the training).
const READ_BITS: u32 = 20;
/// A rested state's read ceiling, `2^32` bytes: the state is the tree's standing as text (215 MB
/// measured at 1,000 GSM8K problems and depth 24), so the ceiling follows the host's memory, not
/// the command budget for small inputs.
const STATE_BUDGET: usize = 1 << 32;

/// The passage tree's horizon `m`, `γ = 1 − 2^(−13)` (agent-inferred): about four GSM8K problems of
/// some 2,200 cells, the horizon the mathematics thread's online measurement placed best of
/// `2^11`, `2^13` and `2^15` (0.5019, 0.5003, 0.5068 bits a cell at depth 24).
const PASSAGE_HORIZON: u32 = 13;
/// The passage tree's backoff `β`, one occurrence of the parent's face (agent-inferred): the
/// located weight `α_e` sets how far the passage's face is trusted.
const PASSAGE_BACKOFF: u64 = 1;

/// The native route's receiving tree at the declared `depth` (the native route declares 6), its
/// grain and its section width, from the same field.
fn opening_tree(population: u64, depth: usize) -> Result<(Landmarks, u64, usize)> {
    let (field, _, _) = declaration_with_input_context(population, true, true)?;
    let receiver = field.receivers().first().ok_or("one declared receiver")?.clone();
    let partition = field.receiving_context(receiver.ring).ok_or("the receiver's framing")?;
    let mut declaration = holonics::hnn::receiving::landmark_declaration(&field, &receiver)?;
    declaration.depth = depth;
    let tree = Landmarks::new_observed(
        declaration,
        partition.outcome_bits(&field, receiver.ring),
        partition.role(),
    )?;
    let grain = holonics::hnn::field::receiver_grain(&receiver.tolerance)?;
    let width = field.rings()[..receiver.ring].iter().map(|r| r.period()).product::<u64>();
    Ok((tree, grain, usize::try_from(width)?))
}

/// The tree address of the cell at `position`: its source framing (the cell's place in its byte,
/// `position mod 4`, two bits) behind the preceding cells, newest first. `register` holds the last
/// `depth` cells (fewer before the passage reaches the depth: `Boundary` stands in).
fn tree_address(register: &[usize], position: usize, depth: usize) -> Result<ObservedAddress> {
    let part = position % 4;
    let path = ObservationPath::from_source_framing_bits(vec![part & 2 != 0, part & 1 != 0])?;
    let causal: Vec<Letter> = address(register, register.len(), depth);
    Ok(ObservedAddress::new(path, causal))
}

/// The tree's face as numerators on `2^(−62)`: each dyadic mass re-based (released below
/// `2^(−62)` to the nearest numerator where its denominator is finer).
fn tree_masses(face: &[Rat]) -> Result<Vec<u128>> {
    face.iter()
        .map(|q| {
            let den = q.denom();
            let bits = den.bits() - 1;
            if den != &(num_bigint::BigInt::from(1) << bits) {
                return Err("a dyadic tree face".into());
            }
            let num = q.numer().to_biguint().ok_or("a nonnegative tree face")?;
            let value = if bits <= u64::from(FACE_BITS) {
                num << (u64::from(FACE_BITS) - bits)
            } else {
                let shift = bits - u64::from(FACE_BITS);
                (num + (num_bigint::BigUint::from(1u8) << (shift - 1))) >> shift
            };
            u128::try_from(value).map_err(|_| "a tree mass above one".into())
        })
        .collect()
}

/// `⌊log₂ x · 2^20⌋`, by the binary digits of repeated squaring (integers only).
fn log2_reading(x: u128) -> i64 {
    let whole = 127 - x.leading_zeros() as i64;
    // mantissa m in [1, 2) on 2^(−62)
    let mut m: u128 = if whole >= 62 { x >> (whole - 62) } else { x << (62 - whole) };
    let mut frac: i64 = 0;
    for _ in 0..READ_BITS {
        m = (m * m) >> 62;
        frac <<= 1;
        if m >= 2u128 << 62 {
            m >>= 1;
            frac |= 1;
        }
    }
    (whole << READ_BITS) + frac
}

/// `−log₂(u/U)` on `2^(−20)` bits.
fn code_reading(mass: u128, total: u128) -> i64 {
    log2_reading(total) - log2_reading(mass)
}

fn thousandths(code: i64, cells: i64) -> String {
    let t = (code * 1000) / (cells.max(1) << READ_BITS);
    format!("{}{}.{:03}", if t < 0 { "-" } else { "" }, t.abs() / 1000, t.abs() % 1000)
}

fn declared_modes(modes: usize, depth: usize) -> Result<KeyedModes> {
    Ok(KeyedModes::new(Declaration { modes, alphabet: 4, evidence: depth + 2, grains: Grains::DECLARED })?)
}

fn declared_passage(depth: usize) -> Result<PassageTree> {
    Ok(PassageTree::new(PassageDeclaration {
        alphabet: 4,
        phases: 4,
        depth,
        horizon: PASSAGE_HORIZON,
        backoff: PASSAGE_BACKOFF,
    })?)
}

/// [definition; agent-inferred] **The route at one cell**: the trees, the bank, the last `depth`
/// cells (oldest first) and how many cells were received.
struct Route {
    tree: Landmarks,
    grain: u64,
    depth: usize,
    population: u64,
    learner: KeyedLearner,
    passage: PassageTree,
    register: Vec<usize>,
    position: usize,
}

/// One cell's reading: the tree's face, the passage tree's reading and the joined face.
struct Reading {
    address: ObservedAddress,
    q: Vec<u128>,
    passage: PassageReading,
    joined: JoinedFace,
}

impl Route {
    fn open(population: u64, depth: usize, modes: usize) -> Result<Self> {
        let (tree, grain, _) = opening_tree(population, depth)?;
        Ok(Self {
            tree,
            grain,
            depth,
            population,
            learner: KeyedLearner::new(declared_modes(modes, depth)?),
            passage: declared_passage(depth)?,
            register: Vec::with_capacity(depth + 1),
            position: 0,
        })
    }

    fn context(&self) -> Vec<usize> {
        self.register.iter().rev().copied().collect()
    }

    fn read(&self) -> Result<Reading> {
        let address = tree_address(&self.register, self.position, self.depth)?;
        let q = tree_masses(&self.tree.face_observed(&address, self.grain)?.probabilities)?;
        let local = self.passage.face(self.position % 4, &self.context(), self.position as u64, &q)?;
        let exponent = self.learner.modes.declaration.grains.exponent;
        // The passage's term is its log ratio to the tree: p̂ ∝ q (p_loc / q)^α.
        let passage = PassageReading {
            logs: local
                .probabilities
                .iter()
                .zip(&q)
                .map(|(&p, &t)| log2_face(p.max(1), exponent) - log2_face(t.max(1), exponent))
                .collect(),
            evidence: local.evidence,
        };
        let joined = self.learner.face(&q, Some(&passage))?;
        Ok(Reading { address, q, passage, joined })
    }

    /// The class arrives: with `learning`, the tree deposits it and the bank receives the
    /// comparison; the bank takes its keyed move; and the passage tree counts it when it was
    /// `received` from the world (a cell the route released itself is not evidence of the passage).
    fn take(&mut self, reading: Reading, class: usize, learning: bool, received: bool) -> Result<()> {
        if learning {
            self.tree.deposit_observed(&reading.address, class)?;
            self.learner.receive(reading.q, Some(reading.passage), &reading.joined, class);
        } else {
            self.learner.follow(class);
        }
        let now = self.position as u64;
        if received {
            self.passage.deposit(self.position % 4, &self.context(), class, now)?;
        }
        if (self.position + 1) % (1 << PASSAGE_HORIZON) == 0 {
            self.passage.release(now);
        }
        self.register.push(class);
        if self.register.len() > self.depth {
            self.register.remove(0);
        }
        self.position += 1;
        Ok(())
    }

    fn to_text(&self, provenance: &str) -> Result<String> {
        let mut standing = String::new();
        self.tree.standing().write(&mut standing);
        let modes = self.learner.to_text()?;
        let passage = self.passage.to_text();
        let cells = self.register.iter().map(usize::to_string).collect::<Vec<_>>().join(" ");
        Ok(format!(
            "{STATE_MAGIC}\n{} {} {} {} {} {}\n{standing}{modes}{passage}{cells}\n{provenance}\n",
            self.population,
            self.position,
            self.depth,
            standing.len(),
            modes.len(),
            passage.len()
        ))
    }

    fn from_text(text: &str) -> Result<Self> {
        let mut lines = text.splitn(3, '\n');
        if lines.next() != Some(STATE_MAGIC) {
            return Err("not a keyed-modes state".into());
        }
        let sizes: Vec<u64> = lines.next().ok_or("state sizes")?.split_whitespace().map(str::parse).collect::<std::result::Result<_, _>>()?;
        let [population, position, depth, standing, modes, passage] = sizes[..] else { return Err("state sizes".into()) };
        let body = lines.next().ok_or("state body")?;
        let (standing_text, rest) = body.split_at(usize::try_from(standing)?);
        let (modes_text, rest) = rest.split_at(usize::try_from(modes)?);
        let (passage_text, rest) = rest.split_at(usize::try_from(passage)?);
        let depth = usize::try_from(depth)?;
        let (opened, grain, _) = opening_tree(population, depth)?;
        let tree = opened.with_standing(&TreeStanding::read(&mut standing_text.lines())?)?;
        let learner = KeyedLearner::from_text(modes_text)?;
        let passage = PassageTree::from_lines(&mut passage_text.lines())?;
        let register: Vec<usize> = rest.lines().next().unwrap_or("").split_whitespace().map(str::parse).collect::<std::result::Result<_, _>>()?;
        let position = usize::try_from(position)?;
        if register.len() != position.min(depth) || passage.declaration.depth != depth {
            return Err("the state's register and passage depth".into());
        }
        Ok(Self { tree, grain, depth, population, learner, passage, register, position })
    }
}

pub(super) fn train(args: &[String]) -> Result<()> {
    if args.len() != 7 {
        return Err("train-modes CORPUS SHA POPULATION DEPTH MODES OUT".into());
    }
    let started = Instant::now();
    let data = pinned_read(&args[1], &args[2], 1 << 26)?;
    let cells = digits(&data);
    let population: u64 = args[3].parse()?;
    if u64::try_from(cells.len())? > population {
        return Err("declared population cannot hold the corpus".into());
    }
    let depth: usize = args[4].parse()?;
    let modes: usize = args[5].parse()?;
    let out = Path::new(&args[6]);
    std::fs::create_dir(out)?;
    let provenance = format!("corpus_sha256={} bytes={} cells={} depth={depth} modes={modes}", args[2], data.len(), cells.len());
    let mut route = Route::open(population, depth, modes)?;
    let (_, _, width) = opening_tree(population, depth)?;
    println!(
        "MODES_TRAIN_OPEN bytes={} cells={} section_cells={width} depth={depth} modes={modes} passage_horizon=2^{PASSAGE_HORIZON} opening_ms={}",
        data.len(), cells.len(), started.elapsed().as_millis()
    );
    let (mut joined_total, mut tree_total) = (0i64, 0i64);
    let mut by_digit = [(0i64, 0i64); 4];
    let (mut joined_chunk, mut tree_chunk, mut chunk_cells) = (0i64, 0i64, 0i64);
    let mut chunk_started = Instant::now();
    let (mut read_ns, mut take_ns, mut close_ns) = (0u128, 0u128, 0u128);
    let report_every = width * 100;
    for (position, &class) in cells.iter().enumerate() {
        let t0 = Instant::now();
        let reading = route.read()?;
        let code = code_reading(reading.joined.masses[class], reading.joined.total);
        let tree_code = code_reading(reading.q[class], reading.q.iter().sum());
        let t1 = Instant::now();
        route.take(reading, class, true, true)?;
        read_ns += (t1 - t0).as_nanos();
        take_ns += t1.elapsed().as_nanos();
        joined_total += code;
        tree_total += tree_code;
        by_digit[position % 4].0 += code;
        by_digit[position % 4].1 += 1;
        joined_chunk += code;
        tree_chunk += tree_code;
        chunk_cells += 1;
        if (position + 1) % width == 0 || position + 1 == cells.len() {
            let t3 = Instant::now();
            route.learner.close()?;
            close_ns += t3.elapsed().as_nanos();
        }
        if (position + 1) % report_every == 0 || position + 1 == cells.len() {
            let n = (position + 1) as i64;
            let digit = by_digit.iter().map(|(c, n)| thousandths(*c, *n)).collect::<Vec<_>>().join(",");
            let weights: Vec<String> = route.learner.modes.passage.iter().map(|a| thousandths(a.re as i64, 1i64 << (30 - READ_BITS))).collect();
            println!(
                "MODES_TRAIN cells={}/{} chunk_bits_per_cell={} tree_only={} total={} tree_total={} by_digit=[{digit}] passage_nodes={} passage_weights=[{}] us_per_cell={} read_us={} take_us={} close_us={} elapsed_ms={}",
                position + 1, cells.len(), thousandths(joined_chunk, chunk_cells), thousandths(tree_chunk, chunk_cells),
                thousandths(joined_total, n), thousandths(tree_total, n), route.passage.len(), weights.join(","),
                chunk_started.elapsed().as_micros() / chunk_cells.max(1) as u128,
                read_ns / 1000 / n as u128, take_ns / 1000 / n as u128, close_ns / 1000 / n as u128,
                started.elapsed().as_millis()
            );
            joined_chunk = 0;
            tree_chunk = 0;
            chunk_cells = 0;
            chunk_started = Instant::now();
        }
    }
    let text = route.to_text(&provenance)?;
    write_new(&out.join("STATE"), text.as_bytes())?;
    let n = cells.len() as i64;
    println!(
        "MODES_TRAIN_DONE cells={} code_bits_per_cell={} tree_only={} by_digit=[{}] state_bytes={} state_sha256={} elapsed_ms={}",
        cells.len(), thousandths(joined_total, n), thousandths(tree_total, n),
        by_digit.iter().map(|(c, n)| thousandths(*c, *n)).collect::<Vec<_>>().join(","),
        text.len(), sha256(text.as_bytes())?, started.elapsed().as_millis()
    );
    Ok(())
}

pub(super) fn sample(args: &[String]) -> Result<()> {
    if args.len() != 9 {
        return Err("sample-modes STATE STATE_SHA PROMPT PROMPT_SHA KEYS KEYS_SHA CELLS OUT".into());
    }
    let started = Instant::now();
    let state = pinned_read(&args[1], &args[2], STATE_BUDGET)?;
    let prompt = pinned_read(&args[3], &args[4], QUERY_BYTE_BUDGET)?;
    let count: usize = args[7].parse()?;
    let keys = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    if keys.len() < count.checked_mul(8).ok_or("key extent overflow")? {
        return Err("fewer eight-byte keys than declared cells".into());
    }
    let out = Path::new(&args[8]);
    std::fs::create_dir(out)?;
    let mut route = Route::from_text(std::str::from_utf8(&state)?)?;
    if route.position % 4 != 0 {
        return Err("the state ends inside a byte".into());
    }
    // The sample's passage opens at its prompt: the trained passage belongs to the training
    // stream's own recent past, which the sample does not continue.
    route.passage = declared_passage(route.depth)?;
    let mut prompt_code = 0i64;
    for &class in &digits(&prompt) {
        let reading = route.read()?;
        prompt_code += code_reading(reading.joined.masses[class], reading.joined.total);
        route.take(reading, class, false, true)?;
    }
    let mut key_stream = KeyStream::new(keys, 8)?;
    let mut released = Vec::new();
    while released.len() < count {
        let key = key_stream.next_key().ok_or("fewer keys than declared cells")?;
        let reading = route.read()?;
        let total = num_bigint::BigInt::from(reading.joined.total);
        let face: Vec<Rat> = reading.joined.masses.iter().map(|&u| Rat::new(num_bigint::BigInt::from(u), total.clone())).collect();
        let class = holonics::receiver::release::draw_exact(&face, &key)?
            .drawn_class()
            .ok_or("an unresolved draw at an exact face")?;
        // A released cell is not received: counting it would read the sample's own output back
        // as evidence (reafference), which the passage then repeats.
        route.take(reading, class, false, false)?;
        released.push(class);
    }
    let boundary = Base4Bytes::decode(&released, released.len())?;
    write_new(&out.join("OUTPUT.bin"), &boundary.bytes)?;
    println!("MODES_SAMPLE prompt_bits_per_cell={} cells={} elapsed_ms={}", thousandths(prompt_code, digits(&prompt).len() as i64), released.len(), started.elapsed().as_millis());
    println!("MODES_SAMPLE_TEXT {:?}", String::from_utf8_lossy(&boundary.bytes));
    Ok(())
}
