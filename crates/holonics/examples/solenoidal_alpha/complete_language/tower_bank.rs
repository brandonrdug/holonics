//! [definition; agent-inferred, October 26] **The binding bank's exterior commands.** The bank
//! (`hnn::tower::bank`) binds the news at its antecedent's key and reads it at the present face; these
//! commands found a tower on a class alphabet, join a bank onto any learner (a fresh tower, or one
//! trained on prose), and train and read a learner on a class passage cut into sections, each read
//! from rest and compared only where the exterior's mark file says.
//!
//! - `found-tower-classes ALPHABET KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS LAW RATE_BITS OUT`
//!   founds a learner (`LAW` a comma list of `gated`, `turned`, `pumped`, and `pair` or
//!   `pair-linear` for the contact; rectifying contacts otherwise) and writes it create-new.
//! - `join-tower-bank STATE STATE_SHA KEYS KEYS_SHA OUT [level=L] [sides=8x8] [values=V]` joins a
//!   bank (`BankDeclaration::first` unless declared) and writes the learner create-new. The bankless
//!   learner it was joined on is its foil: with the join at zero the two code every passage
//!   bit-identically.
//! - `train-sections-tower-classes STATE STATE_SHA TRAIN TRAIN_SHA TRAIN_MARKS TRAIN_MARKS_SHA DEV
//!   DEV_SHA DEV_MARKS DEV_MARKS_SHA SECTION STREAMS PASSES OUT` trains on the passage's sections,
//!   `STREAMS` sections a certified deposit, each section from rest and its face compared at the
//!   marked cells after its first. After each pass the learner rests as `STATE.p` beside the run and
//!   reads every held-out section from rest: at its marked cells, the code and how many faces name
//!   the class that arrives first.
//!
//! - `found-tower-clock STATE STATE_SHA TEXT TEXT_SHA UNITS UNITS_SHA STREAMS SECTION OUT` reads
//!   the pool of every class's reset clock (`hnn::tower::clock`) at the copy's port over the
//!   training passage, frozen, in the training pass's partition (`STREAMS` streams from rest,
//!   sections of `SECTION` cells), prints the sixteen largest drops, the rest's clock and the shares
//!   down the whole ranking, joins the clock of the largest drop among the classes not yet clocked
//!   (a clocked class's drop is printed beside it), opens the new copy's moments on the same
//!   sections (`TowerLearner::open_moments`) and writes the learner create-new. The learner it was joined on
//!   is its twin; the founding is certified by one training pass from each, its code below the
//!   twin's by more than `log₂` of the pool.
//! - `read-tower-clock-cells STATE STATE_SHA TEXT TEXT_SHA UNITS UNITS_SHA STREAMS REQUESTS
//!   REQUESTS_SHA OUT` prints each clock's copy and writes, at the reads an observer requests, the
//!   coded class's strongest rival on the face and each clock's held class, its raise and its code
//!   (`Tower::read_clocks`).
//! - `read-tower-clock-covectors STATE STATE_SHA TEXT TEXT_SHA UNITS UNITS_SHA STREAMS SECTION
//!   REQUESTS REQUESTS_SHA` reads, in the training pass's partition, each place's covector on the
//!   copies and the readout, and what the learner's step along it does to the name's mass at the
//!   answers' openings ([`read_clock_covectors`]).
//!
//! On the MQAR terrain (`tools/listener/mqar.py`, the record's generator) a section is one passage of
//! 64 classes and the marks are its 16 answers, so the held-out reading is acceptance §3.4's count of
//! the 16,000 answer cells named. Nothing here is MQAR-specific: a section is a stretch of classes
//! and a mark is where the exterior compares.
use super::tower_train::{count, per, positive, STATE_BUDGET};
use super::*;
use holonics::hnn::tower::bank::BankDeclaration;
use holonics::hnn::tower::clock::{ClockDrop, ClockPool};
use holonics::hnn::tower::{ContactLaw, Tower, TowerDeclaration, TowerLearner, TurnLadder, COVECTOR_BITS};
use holonics::hnn::units::Units;
use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use rayon::prelude::*;
use std::time::Instant;

fn classes_of(bytes: &[u8], alphabet: usize) -> Result<Vec<usize>> {
    if bytes.len() % 2 != 0 {
        return Err("a class file holds two bytes a class".into());
    }
    let classes: Vec<usize> = bytes.chunks(2).map(|b| u16::from_be_bytes([b[0], b[1]]) as usize).collect();
    if classes.iter().any(|&c| c >= alphabet) {
        return Err("a class outside the declared alphabet".into());
    }
    Ok(classes)
}

fn learner_of(path: &str, sha: &str) -> Result<TowerLearner> {
    TowerLearner::from_text(std::str::from_utf8(&pinned_read(path, sha, STATE_BUDGET)?)?).map_err(|e| e.to_string().into())
}

fn write_learner(out: &Path, learner: &TowerLearner) -> Result<String> {
    let text = learner.to_text();
    write_new(out, text.as_bytes())?;
    sha256(text.as_bytes())
}

pub(super) fn found(args: &[String]) -> Result<()> {
    let usage = "found-tower-classes ALPHABET KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS LAW RATE_BITS OUT";
    if args.len() != 11 {
        return Err(usage.into());
    }
    let keys = pinned_read(&args[2], &args[3], READ_BUDGET as usize)?;
    let law: Vec<&str> = args[8].split(',').collect();
    if law.iter().any(|l| !["gated", "turned", "pumped", "pair", "pair-linear"].contains(l)) {
        return Err(usage.into());
    }
    let contact = if law.contains(&"pair") {
        ContactLaw::Pair
    } else if law.contains(&"pair-linear") {
        ContactLaw::PairLinear
    } else {
        ContactLaw::Rectifying
    };
    let declaration = TowerDeclaration {
        alphabet: count(&args[1])?,
        width: count(&args[4])?,
        modes: count(&args[5])?,
        contacts: count(&args[6])?,
        levels: count(&args[7])?,
        gated: law.contains(&"gated"),
        turned: law.contains(&"turned"),
        pumped: law.contains(&"pumped"),
        contact,
    };
    let learner = TowerLearner::new(Tower::found_on(declaration, &keys, TurnLadder::Fixed).map_err(|e| e.to_string())?, args[9].parse()?);
    let sha = write_learner(Path::new(&args[10]), &learner)?;
    println!("TOWER_FOUNDED material={} state_sha256={sha}", learner.tower.theta.len());
    Ok(())
}

pub(super) fn join(args: &[String]) -> Result<()> {
    let usage = "join-tower-bank STATE STATE_SHA KEYS KEYS_SHA OUT [level=L] [sides=8x8] [values=V]";
    if args.len() < 6 {
        return Err(usage.into());
    }
    let mut learner = learner_of(&args[1], &args[2])?;
    let keys = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let mut bank = BankDeclaration::first(&learner.tower.declaration);
    for option in &args[6..] {
        if let Some(l) = option.strip_prefix("level=") {
            bank.level = l.parse()?;
        } else if let Some(s) = option.strip_prefix("sides=") {
            bank.harmonics = s.split('x').map(str::parse).collect::<std::result::Result<_, _>>()?;
        } else if let Some(v) = option.strip_prefix("values=") {
            bank.values = v.parse()?;
        } else {
            return Err(usage.into());
        }
    }
    let line = bank.to_text();
    learner.join_bank(bank, &keys).map_err(|e| e.to_string())?;
    let sha = write_learner(Path::new(&args[5]), &learner)?;
    println!("TOWER_BANK_JOINED {} material={} state_sha256={sha}", line.trim_end(), learner.tower.theta.len());
    Ok(())
}

/// [agent-inferred, October 26; records
/// `2026-10-26_THE_ROLE_KEY_IS_A_RESET_CLOCK_THE_POOL_FOUNDS_AND_ITS_ACCEPTANCE_IS_FIXED_BEFORE_THE_BUILD.md`
/// §§2–4 and
/// `2026-10-26_THE_CLOCK_GAINS_ONLY_WHERE_ITS_ARRIVAL_RECURS_SO_ITS_JOIN_BECOMES_A_COPY_AT_THE_OUTPUT_AND_ITS_ACCEPTANCE_IS_FIXED_BEFORE_THE_BUILD.md`
/// §4] The reset clocks' pool over the training passage and the founding of its largest drop. Each
/// stream reads its share of the passage from rest, as the training pass's stream does
/// (`Tower::read_clock_pool`: the readout's covector needs no reverse scan, so the sections do not
/// part the read); the streams' pools add exactly. The clock founded is the largest drop's, whatever
/// class it is.
pub(super) fn found_clock(args: &[String]) -> Result<()> {
    let usage = "found-tower-clock STATE STATE_SHA TEXT TEXT_SHA UNITS UNITS_SHA STREAMS SECTION OUT";
    if args.len() != 10 {
        return Err(usage.into());
    }
    let started = Instant::now();
    let mut learner = learner_of(&args[1], &args[2])?;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let units = Units::from_text(std::str::from_utf8(&pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?).map_err(|e| e.to_string())?;
    let (streams, section) = (positive(&args[7])?, positive(&args[8])?);
    let out = Path::new(&args[9]);
    let tower = &learner.tower;
    let (alphabet, width) = (tower.declaration.alphabet, tower.declaration.width);
    if units.len() != alphabet {
        return Err("the units are not the tower's alphabet".into());
    }
    let classes: Vec<usize> = units.parse(&text).map_err(|e| e.to_string())?.into_iter().map(|u| u as usize).collect();
    // The training pass's partition: `chunk` classes a stream, `(chunk − 1) / section` sections.
    let chunk = classes.len() / streams;
    if chunk < section + 1 {
        return Err("the text must hold one section a stream".into());
    }
    let read = (chunk - 1) / section * section + 1;
    let pools: Vec<ClockPool> = (0..streams)
        .into_par_iter()
        .map(|s| {
            let mut pool = ClockPool::new(alphabet, width);
            let mut stream = pool.open_stream();
            let mut state = tower.rest();
            tower.read_clock_pool(&mut state, &classes[s * chunk..s * chunk + read], &mut pool, &mut stream).map_err(|e| e.to_string())?;
            println!("TOWER_CLOCK_STREAM stream={s} cells={} elapsed_ms={}", pool.cells, started.elapsed().as_millis());
            Ok(pool)
        })
        .collect::<std::result::Result<_, String>>()?;
    let mut pool = ClockPool::new(alphabet, width);
    for p in pools {
        pool.absorb(p).map_err(|e| e.to_string())?;
    }
    let read_ms = started.elapsed().as_millis();
    let drops = pool.drops().map_err(|e| e.to_string())?;
    if drops.is_empty() {
        return Err("the pool read no clock".into());
    }
    // A reading beside the drop: its share of the readout covectors' energy (`Σ_t ‖δz_t‖²` on
    // `2^(−48)`) in parts a million.
    println!(
        "TOWER_CLOCK_POOL clocks={} cells={} energy={} grain_bits={} read_ms={read_ms} drops_ms={}",
        drops.len(),
        pool.cells,
        pool.energy,
        2 * COVECTOR_BITS,
        started.elapsed().as_millis() - read_ms
    );
    let name = |class: usize| if class == alphabet { "rest".to_string() } else { format!("{:?}", String::from_utf8_lossy(units.piece(class))) };
    let share = |d: &ClockDrop| &d.drop_numerator * 1_000_000u32 / (&d.drop_denominator * pool.energy);
    let line = |rank: usize, d: &ClockDrop| format!("rank={rank} class={} piece={} drop={} drop_ppm={} rank_c={} cells={}", d.class, name(d.class), &d.drop_numerator / &d.drop_denominator, share(d), d.rank, d.cells);
    for (rank, d) in drops.iter().take(16).enumerate() {
        println!("TOWER_CLOCK_DROP {}", line(rank + 1, d));
    }
    // Readings beside the ranking: the rest's clock, which holds one arrival a stream, and the
    // shares down the whole ranking.
    if let Some((rank, d)) = drops.iter().enumerate().find(|(_, d)| d.class == alphabet) {
        println!("TOWER_CLOCK_REST {}", line(rank + 1, d));
    }
    let at = |q: usize| share(&drops[((drops.len() - 1) * q / 100).min(drops.len() - 1)]);
    println!(
        "TOWER_CLOCK_SPREAD clocks={} ppm_at_rank_share_0={} 10={} 25={} 50={} 75={} 90={} 100={}",
        drops.len(),
        at(0),
        at(10),
        at(25),
        at(50),
        at(75),
        at(90),
        at(100)
    );
    // A class already clocked keeps its copy, which its own steps go on fitting: a second copy of
    // the same held class is the same face. Its drop is read beside, and the founding is the top
    // drop among the classes not yet clocked.
    let clocked = tower.clock().map_or(Vec::new(), |c| c.classes.clone());
    for (rank, d) in drops.iter().enumerate().filter(|(_, d)| clocked.contains(&d.class)) {
        println!("TOWER_CLOCK_JOINED {}", line(rank + 1, d));
    }
    let class = drops.iter().find(|d| !clocked.contains(&d.class)).ok_or("every class of the pool is clocked")?.class;
    learner.join_clock(class).map_err(|e| e.to_string())?;
    // The copy's moments, opened on the passage it was founded on, in the training pass's
    // partition (`TowerLearner::open_moments`, section k of stream s reading `[s·chunk + k·section,
    // s·chunk + (k + 1)·section]`): a family opened at zero inside an opened learner moves at the
    // full rate from its first section (`hnn.tower-founded-moments`).
    let moments_started = Instant::now();
    let sections: Vec<Vec<&[usize]>> = (0..(chunk - 1) / section)
        .map(|k| (0..streams).map(|s| &classes[s * chunk + k * section..s * chunk + (k + 1) * section + 1]).collect())
        .collect();
    // The new clock's copy is the last row and bias of the clocks' range; the clocks founded
    // before keep the moments their passes left.
    let joined = learner.tower.clock_join().ok_or("a founded tower has a clock")?;
    let family = joined.end - (width + 1)..joined.end;
    let mut states: Vec<_> = (0..streams).map(|_| learner.tower.rest()).collect();
    let moment_sections = learner.open_moments(family, &mut states, &sections).map_err(|e| e.to_string())?;
    let moments_ms = moments_started.elapsed().as_millis();
    let sha = write_learner(out, &learner)?;
    println!(
        "TOWER_CLOCK_FOUNDED class={class} piece={} material={} moment_sections={moment_sections} moments_ms={moments_ms} state_sha256={sha} elapsed_ms={}",
        name(class),
        learner.tower.theta.len(),
        started.elapsed().as_millis()
    );
    Ok(())
}

/// [agent-inferred, October 26; record
/// `2026-10-26_THE_THIRD_LAP_FOUNDS_THE_CLOCK_AFTER_EQUALS_AND_ITS_PASS_LOWERS_THE_ROLE_FROM_53_TO_43.md`
/// §4] The clocks' copies, read in `read-tower-held-cells`' partition of `TEXT` (`STREAMS` chunks,
/// each from rest). Each clock's copy is printed (`TOWER_CLOCK_COPY`): its class, its bias `b_A` on
/// `2^(−16)`, its row's square `‖r_A‖²` on `2^(−48)` and its reach `max |r_A|` on `2^(−24)`. `OUT`
/// (create-new) holds one line for each read requested, tab-separated: `p class code rank rival
/// rival_code`, then `held raise held_code` for each clock in founding order. `p` is the place in `TEXT` of the
/// coded class's first byte, `class` that class and `code` and `rank` its code and rank on the face,
/// `rival` the other class carrying the largest mass (on a tie the lowest) and `rival_code` its code,
/// codes on `2^(−20)` bits (the face's mass is `2^z`, so `rival_code − code` is, to the face's
/// grain, the logits' margin `z_class − z_rival` in bits); `held` is
/// the class the clock holds (the alphabet where it holds nothing, its raise and code then `-`),
/// `raise` its copy's `⟨r_A, x⟩ + b_A` on the logit's `2^(−16)` and `held_code` the held class's
/// code on the face, whether or not it arrives next. `REQUESTS` holds one read a line, its first
/// tab-separated field `p` (the `requests` output of `tools/listener/bank_trace.py` serves); a
/// request whose place no cell codes (a chunk's first class) is counted as skipped. A reading beside
/// the code: nothing here enters the machine.
pub(super) fn read_clock_cells(args: &[String]) -> Result<()> {
    let usage = "read-tower-clock-cells STATE STATE_SHA TEXT TEXT_SHA UNITS UNITS_SHA STREAMS REQUESTS REQUESTS_SHA OUT";
    if args.len() != 11 {
        return Err(usage.into());
    }
    let started = Instant::now();
    let learner = learner_of(&args[1], &args[2])?;
    let tower = &learner.tower;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let units = Units::from_text(std::str::from_utf8(&pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?).map_err(|e| e.to_string())?;
    let streams = positive(&args[7])?;
    let wanted: std::collections::HashSet<usize> = std::str::from_utf8(&pinned_read(&args[8], &args[9], READ_BUDGET as usize)?)?
        .lines()
        .map(|l| l.split('\t').next().unwrap_or("").parse::<usize>())
        .collect::<std::result::Result<_, _>>()?;
    let out = Path::new(&args[10]);
    let (alphabet, width) = (tower.declaration.alphabet, tower.declaration.width);
    if units.len() != alphabet {
        return Err("the units are not the tower's alphabet".into());
    }
    let (clock, join) = tower.clock().zip(tower.clock_join()).ok_or("a copies' reading needs a clock")?;
    let name = |class: usize| if class == alphabet { "rest".to_string() } else { format!("{:?}", String::from_utf8_lossy(units.piece(class))) };
    for (c, &class) in clock.classes.iter().enumerate() {
        let row = &tower.theta[join.start + c * (width + 1)..join.start + c * (width + 1) + width];
        let square: i128 = row.iter().map(|&v| v as i128 * v as i128).sum();
        let reach = row.iter().map(|v| v.unsigned_abs()).max().unwrap_or(0);
        println!(
            "TOWER_CLOCK_COPY clock={c} class={class} piece={} bias={} row_square={square} reach={reach}",
            name(class),
            tower.theta[join.start + c * (width + 1) + width]
        );
    }
    let (classes, lengths): (Vec<usize>, Vec<usize>) = units.parse(&text).map_err(|e| e.to_string())?.into_iter().map(|u| (u as usize, units.piece(u as usize).len())).unzip();
    let mut places = Vec::with_capacity(lengths.len());
    lengths.iter().fold(0usize, |at, &n| {
        places.push(at);
        at + n
    });
    let chunk = classes.len().div_ceil(streams);
    let starts: Vec<usize> = (0..classes.len()).step_by(chunk).collect();
    let parts: Vec<Vec<String>> = starts
        .par_iter()
        .map(|&start| {
            let mut state = tower.rest();
            let part = &classes[start..(start + chunk).min(classes.len())];
            let mut lines = Vec::new();
            tower
                .read_clocks(&mut state, part, |i, face, held, raises, _| {
                    let place = places[start + i + 1];
                    if wanted.contains(&place) {
                        let next = part[i + 1];
                        let rival = (0..face.masses.len()).filter(|&c| c != next).fold(usize::from(next == 0), |best, c| if face.masses[c] > face.masses[best] { c } else { best });
                        let mut line = format!("{place}\t{next}\t{}\t{}\t{rival}\t{}", face.code(next), face.rank(next), face.code(rival));
                        for (&h, r) in held.iter().zip(raises) {
                            match r {
                                Some(v) => line.push_str(&format!("\t{h}\t{v}\t{}", face.code(h))),
                                None => line.push_str(&format!("\t{h}\t-\t-")),
                            }
                        }
                        lines.push(line);
                    }
                    Ok(())
                })
                .map_err(|e| e.to_string())?;
            Ok(lines)
        })
        .collect::<std::result::Result<_, String>>()?;
    let read: usize = parts.iter().map(Vec::len).sum();
    let mut written = String::new();
    for line in parts.iter().flatten() {
        written.push_str(line);
        written.push('\n');
    }
    write_new(out, written.as_bytes())?;
    println!(
        "TOWER_CLOCK_CELLS clocks={} streams={streams} requests={} read={read} skipped={} out={} elapsed_ms={}",
        clock.classes.len(),
        wanted.len(),
        wanted.len() - read,
        args[10],
        started.elapsed().as_millis()
    );
    Ok(())
}

/// The places a named problem's cells fall in: its question, the answer's opening, the rest of its
/// answer, and every other cell of the passage.
const PLACES: [&str; 4] = ["question", "opening", "answer", "elsewhere"];

/// One stream's sums for [`read_clock_covectors`]: each group's (place by whether the name
/// arrives) cells and covector on the copies (`clocks · (d + 1)`) and on the readout (`A · d + A`),
/// and, at the openings, the covector toward the name with the openings' own faces.
struct PlaceSums {
    cells: [u64; 8],
    copy: Vec<Vec<i128>>,
    readout: Vec<Vec<i128>>,
    toward_copy: Vec<i128>,
    toward_readout: Vec<i128>,
    open: Vec<i128>,
    openings: u64,
    unheld: u64,
    name_mass: i128,
}

impl PlaceSums {
    fn new(copies: usize, readout: usize) -> Self {
        Self {
            cells: [0; 8],
            copy: vec![vec![0; copies]; 8],
            readout: vec![vec![0; readout]; 8],
            toward_copy: vec![0; copies],
            toward_readout: vec![0; readout],
            open: vec![0; copies],
            openings: 0,
            unheld: 0,
            name_mass: 0,
        }
    }

    fn absorb(&mut self, other: PlaceSums) {
        let add = |a: &mut [i128], b: &[i128]| a.iter_mut().zip(b).for_each(|(x, y)| *x += y);
        for g in 0..8 {
            self.cells[g] += other.cells[g];
            add(&mut self.copy[g], &other.copy[g]);
            add(&mut self.readout[g], &other.readout[g]);
        }
        add(&mut self.toward_copy, &other.toward_copy);
        add(&mut self.toward_readout, &other.toward_readout);
        add(&mut self.open, &other.open);
        self.openings += other.openings;
        self.unheld += other.unheld;
        self.name_mass += other.name_mass;
    }
}

/// The readout's covector at one cell, `δz ⊗ (x, 1)`, added to `sums` (rows `A · d`, then the
/// biases); the classes the face gives no mass at the covector's grain add nothing.
fn add_readout(sums: &mut [i128], dz: &[i64], x: &[i32]) {
    let (a, w) = (dz.len(), x.len());
    for (k, &v) in dz.iter().enumerate().filter(|(_, v)| **v != 0) {
        let row = &mut sums[k * w..(k + 1) * w];
        for (s, &xj) in row.iter_mut().zip(x) {
            *s += (v * xj as i64) as i128;
        }
        sums[a * w + k] += v as i128;
    }
}

/// `v` on `2^(−bits)` as a decimal with `places` places, rounded to the nearest.
fn fixed(v: &BigInt, bits: u32, places: u32) -> String {
    let scale = BigInt::from(10u32).pow(places);
    let half = BigInt::from(1u8) << bits >> 1u32;
    let m = (v.abs() * &scale + half) >> bits;
    let (whole, frac) = (&m / &scale, &m % &scale);
    let sign = if v.is_negative() && !m.is_zero() { "-" } else { "+" };
    format!("{sign}{whole}.{frac:0>width$}", width = places as usize)
}

/// `Σ a_i b_i`, each side on its own grain, exactly.
fn dot(a: &[i128], b: &[i128]) -> BigInt {
    a.iter().zip(b).map(|(x, y)| BigInt::from(*x) * y).sum()
}

/// [agent-inferred, October 26; record
/// `2026-10-26_THE_PASS_MOVES_THE_NAMES_MASS_AWAY_FROM_HOW_OFTEN_THE_ANSWER_OPENS_WITH_IT_SO_EACH_PLACES_PULL_IS_READ_THROUGH_THE_STEP.md`
/// §3] **Each place's pull on the name at the answers' openings, read through the learner's step.**
/// The frozen learner reads `TEXT` in the training pass's partition (`STREAMS` streams from rest,
/// `(chunk − 1) / SECTION` sections of `SECTION` cells, as `found-tower-clock` reads it). Each
/// request `p f` of `REQUESTS` (the `requests` output of `tools/listener/bank_trace.py`) names a
/// problem from its first byte `f` to the byte after its blank line, its answer's opening `p`, and
/// its name `n`, the class at `f`. A cell falls in its problem's question, opening or answer, or
/// elsewhere, and in each by whether the class that arrives next is the name (elsewhere: a class a
/// clock holds). Over each group the readout's covector `G = Σ δz ⊗ (x, 1)` is summed on the
/// clocks' copies (`δz[held]`) and on the readout and its bias, and at every opening where a clock
/// holds the name the covector toward the name `Y = Σ_o δz_o^(n) ⊗ (x_o, 1)`. The pass's change of
/// `F = Σ_o log₂ p̂_o(n_o)`, to first order and under the learner's second moments, is
/// `⟨Y, step(G)⟩` (`TowerLearner::step_for`): each group's share, on the copies (each clock's) and
/// on the readout (the rows of the classes that name a problem and the rest). Beside it the plain
/// share `⟨Y, G⟩` in the material's own units, in parts a thousand of the total's size, and the
/// change of each clock's raise, `−⟨X, step(G)⟩` over the openings' `X = Σ_o (x_o, 1)`, a mean an
/// opening. The lower levels are not read: a change of the top face `x` is outside this reading.
/// A reading beside the code: nothing enters the machine and the learner is not moved.
pub(super) fn read_clock_covectors(args: &[String]) -> Result<()> {
    let usage = "read-tower-clock-covectors STATE STATE_SHA TEXT TEXT_SHA UNITS UNITS_SHA STREAMS SECTION REQUESTS REQUESTS_SHA";
    if args.len() != 11 {
        return Err(usage.into());
    }
    let started = Instant::now();
    let learner = learner_of(&args[1], &args[2])?;
    let tower = &learner.tower;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let units = Units::from_text(std::str::from_utf8(&pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?).map_err(|e| e.to_string())?;
    let (streams, section) = (positive(&args[7])?, positive(&args[8])?);
    let requests: Vec<(usize, usize)> = std::str::from_utf8(&pinned_read(&args[9], &args[10], READ_BUDGET as usize)?)?
        .lines()
        .map(|l| {
            let mut k = l.split('\t').map(|v| v.parse::<usize>());
            match (k.next(), k.next()) {
                (Some(Ok(p)), Some(Ok(f))) => Ok((p, f)),
                _ => Err("a request is `p f`, tab-separated"),
            }
        })
        .collect::<std::result::Result<_, _>>()?;
    let (alphabet, width) = (tower.declaration.alphabet, tower.declaration.width);
    if units.len() != alphabet {
        return Err("the units are not the tower's alphabet".into());
    }
    let (clock, join) = tower.clock().zip(tower.clock_join()).ok_or("a copies' reading needs a clock")?;
    let clocks = clock.classes.len();
    let readout = tower.readout_family();
    let (classes, lengths): (Vec<usize>, Vec<usize>) = units.parse(&text).map_err(|e| e.to_string())?.into_iter().map(|u| (u as usize, units.piece(u as usize).len())).unzip();
    let mut places = Vec::with_capacity(lengths.len());
    lengths.iter().fold(0usize, |at, &n| {
        places.push(at);
        at + n
    });
    // The problems: `(f, p, e, n)`, the first byte, the opening, the byte after the blank line, the
    // name. A request whose bytes no class begins at is not placed.
    let mut problems = Vec::with_capacity(requests.len());
    for &(p, f) in &requests {
        match (places.binary_search(&f), places.binary_search(&p)) {
            (Ok(i), Ok(_)) if f < p => {
                let e = text[p..].windows(2).position(|w| w == b"\n\n").map_or(text.len(), |k| p + k + 2);
                problems.push((f, p, e, classes[i]));
            }
            _ => {}
        }
    }
    problems.sort_unstable();
    let named: std::collections::HashSet<usize> = problems.iter().map(|&(.., n)| n).collect();
    let place_of = |q: usize| -> (usize, Option<usize>) {
        let k = problems.partition_point(|&(f, ..)| f < q);
        match k.checked_sub(1).map(|k| problems[k]) {
            Some((_, p, e, n)) if q < e => (if q < p { 0 } else if q == p { 1 } else { 2 }, Some(n)),
            _ => (3, None),
        }
    };
    // The training pass's partition: `chunk` classes a stream, `(chunk − 1) / section` sections.
    let chunk = classes.len() / streams;
    if chunk < section + 1 {
        return Err("the text must hold one section a stream".into());
    }
    let read = (chunk - 1) / section * section + 1;
    let copies = clocks * (width + 1);
    let parts: Vec<PlaceSums> = (0..streams)
        .into_par_iter()
        .map(|s| {
            let mut sums = PlaceSums::new(copies, readout.len());
            let part = &classes[s * chunk..s * chunk + read];
            tower
                .read_clocks(&mut tower.rest(), part, |i, face, held, _, top| {
                    let next = part[i + 1];
                    let (place, name) = place_of(places[s * chunk + i + 1]);
                    let arrives = name.map_or(held.contains(&next), |n| next == n);
                    let g = place * 2 + usize::from(arrives);
                    let dz = face.covector(next);
                    sums.cells[g] += 1;
                    for (c, &h) in held.iter().enumerate().filter(|(_, h)| **h < alphabet) {
                        let row = &mut sums.copy[g][c * (width + 1)..(c + 1) * (width + 1)];
                        for (v, &xj) in row.iter_mut().zip(top) {
                            *v += (dz[h] * xj as i64) as i128;
                        }
                        row[width] += dz[h] as i128;
                    }
                    add_readout(&mut sums.readout[g], &dz, top);
                    if let (1, Some(n)) = (place, name) {
                        if !held.contains(&n) {
                            sums.unheld += 1;
                            return Ok(());
                        }
                        let dn = face.covector(n);
                        sums.openings += 1;
                        sums.name_mass += dn[n] as i128 + (1i128 << COVECTOR_BITS);
                        for (c, &h) in held.iter().enumerate().filter(|(_, h)| **h < alphabet) {
                            let at = c * (width + 1);
                            for (j, &xj) in top.iter().enumerate() {
                                sums.toward_copy[at + j] += (dn[h] * xj as i64) as i128;
                                sums.open[at + j] += xj as i128;
                            }
                            sums.toward_copy[at + width] += dn[h] as i128;
                            sums.open[at + width] += 1;
                        }
                        add_readout(&mut sums.toward_readout, &dn, top);
                    }
                    Ok(())
                })
                .map_err(|e| e.to_string())?;
            Ok(sums)
        })
        .collect::<std::result::Result<_, String>>()?;
    let read_ms = started.elapsed().as_millis();
    let mut sums = PlaceSums::new(copies, readout.len());
    for part in parts {
        sums.absorb(part);
    }
    println!(
        "TOWER_CLOCK_COVECTOR_OPENINGS requests={} placed={} read={} unheld={} name_mass={}",
        requests.len(),
        problems.len(),
        sums.openings,
        sums.unheld,
        fixed(&BigInt::from(sums.name_mass), COVECTOR_BITS, 1)
    );
    // The groups, then their whole; each read through the step of its own summed covector.
    let mut groups: Vec<(String, usize, Vec<i128>, Vec<i128>)> = (0..8).map(|g| (format!("place={} arrives={}", PLACES[g / 2], g % 2), g, sums.copy[g].clone(), sums.readout[g].clone())).collect();
    let whole = |v: &[Vec<i128>]| (0..v[0].len()).map(|i| v.iter().map(|g| g[i]).sum()).collect::<Vec<i128>>();
    groups.push(("place=all arrives=-".to_string(), 8, whole(&sums.copy), whole(&sums.readout)));
    let (a, w) = (alphabet, width);
    // The plain shares: `⟨Y, G⟩` in the material's own units, a row's on `2^(−80)` and a bias's
    // raised from `2^(−48)`.
    let plain = |y: &[i128], g: &[i128], bias: &dyn Fn(usize) -> bool| -> BigInt {
        y.iter()
            .zip(g)
            .enumerate()
            .map(|(i, (u, v))| {
                let p = BigInt::from(*u) * v;
                if bias(i) { p << 32u32 } else { p }
            })
            .sum()
    };
    let copy_bias = |i: usize| i % (w + 1) == w;
    let readout_bias = |i: usize| i >= a * w;
    let plain_total = plain(&sums.toward_copy, &groups[8].2, &copy_bias) + plain(&sums.toward_readout, &groups[8].3, &readout_bias);
    let per_thousand = |v: &BigInt| if plain_total.is_zero() { BigInt::zero() } else { (v * 1000) / plain_total.abs() };
    for (label, g, copy, ro) in &groups {
        let cells = if *g < 8 { sums.cells[*g] } else { sums.cells.iter().sum() };
        let step_copy = learner.step_for(join.start, copy).map_err(|e| e.to_string())?;
        let step_ro = learner.step_for(readout.start, ro).map_err(|e| e.to_string())?;
        // The readout's share on `2^(−64)`: a row's step on `2^(−24)` against `Y` on `2^(−40)`, a
        // bias's step on `2^(−16)` against `Σ δz` on `2^(−24)`, raised by 24.
        let (mut names, mut others) = (BigInt::zero(), BigInt::zero());
        for k in 0..a {
            let v = dot(&step_ro[k * w..(k + 1) * w], &sums.toward_readout[k * w..(k + 1) * w]) + ((BigInt::from(step_ro[a * w + k]) * sums.toward_readout[a * w + k]) << 24u32);
            if named.contains(&k) { names += v } else { others += v }
        }
        let mut line = format!(
            "TOWER_CLOCK_COVECTOR {label} cells={cells} readout_name={} readout_names={} readout_others={} readout_plain_ppt={}",
            fixed(&(&names + &others), 64, 3),
            fixed(&names, 64, 3),
            fixed(&others, 64, 3),
            per_thousand(&plain(&sums.toward_readout, ro, &readout_bias))
        );
        for c in 0..clocks {
            let r = c * (w + 1)..(c + 1) * (w + 1);
            let (sc, y, x) = (&step_copy[r.clone()], &sums.toward_copy[r.clone()], &sums.open[r.clone()]);
            let name = dot(&sc[..w], &y[..w]) + ((BigInt::from(sc[w]) * y[w]) << 24u32);
            let held = sums.open[r.start + w];
            let raise = -(dot(&sc[..w], &x[..w]) + ((BigInt::from(sc[w]) * x[w]) << 24u32));
            let mean = if held == 0 { BigInt::zero() } else { raise / held };
            line.push_str(&format!(
                " clock={c}:dz={},raise={},name={},plain_ppt={}",
                fixed(&BigInt::from(copy[r.start + w]), COVECTOR_BITS, 1),
                fixed(&mean, 40, 3),
                fixed(&name, 64, 3),
                per_thousand(&plain(y, &copy[r.clone()], &|i| i == w))
            ));
        }
        println!("{line}");
        if *g == 8 {
            for (c, &class) in clock.classes.iter().enumerate() {
                println!("TOWER_CLOCK_COVECTOR_STEP clock={c} class={class} bias={} bias_change={}", tower.theta[join.start + c * (w + 1) + w], -step_copy[c * (w + 1) + w]);
            }
            println!("TOWER_CLOCK_COVECTOR_PLAIN total_sign={}", if plain_total.is_negative() { "-" } else { "+" });
        }
    }
    println!(
        "TOWER_CLOCK_COVECTORS clocks={clocks} streams={streams} section={section} cells={} read_ms={read_ms} elapsed_ms={}",
        sums.cells.iter().sum::<u64>(),
        started.elapsed().as_millis()
    );
    Ok(())
}

/// Each section from rest: at its marked cells after the first, the code (on `2^(−20)` bits), the
/// cells, and how many faces name the arriving class first.
fn held_out(tower: &Tower, classes: &[usize], marks: &[u8], section: usize) -> Result<(i64, usize, usize)> {
    let read: Vec<(i64, usize, usize)> = (0..classes.len() / section)
        .into_par_iter()
        .map(|k| {
            let part = &classes[k * section..(k + 1) * section];
            let mut state = tower.rest();
            let (mut code, mut cells, mut named) = (0i64, 0usize, 0usize);
            for i in 0..section - 1 {
                let face = tower.advance(&mut state, part[i]).map_err(|e| e.to_string())?;
                if marks[k * section + i + 1] == 1 {
                    let next = part[i + 1];
                    let top = (0..face.masses.len()).fold(0, |best, c| if face.masses[c] > face.masses[best] { c } else { best });
                    code += face.code(next);
                    cells += 1;
                    named += usize::from(top == next);
                }
            }
            Ok((code, cells, named))
        })
        .collect::<std::result::Result<_, String>>()?;
    Ok(read.into_iter().fold((0, 0, 0), |a, r| (a.0 + r.0, a.1 + r.1, a.2 + r.2)))
}

fn marked(classes: &[usize], marks: Vec<u8>, section: usize) -> Result<Vec<u8>> {
    if marks.len() != classes.len() || marks.iter().any(|&m| m > 1) {
        return Err("a mark file holds one byte a class, 0 or 1".into());
    }
    if classes.len() % section != 0 || section < 2 {
        return Err("the passage must hold whole sections of at least two classes".into());
    }
    Ok(marks)
}

pub(super) fn train(args: &[String]) -> Result<()> {
    let usage = "train-sections-tower-classes STATE STATE_SHA TRAIN TRAIN_SHA TRAIN_MARKS TRAIN_MARKS_SHA DEV DEV_SHA DEV_MARKS DEV_MARKS_SHA SECTION STREAMS PASSES OUT";
    if args.len() != 15 {
        return Err(usage.into());
    }
    let started = Instant::now();
    let mut learner = learner_of(&args[1], &args[2])?;
    let alphabet = learner.tower.declaration.alphabet;
    let section = count(&args[11])?;
    let train = classes_of(&pinned_read(&args[3], &args[4], READ_BUDGET as usize)?, alphabet)?;
    let train_marks = marked(&train, pinned_read(&args[5], &args[6], READ_BUDGET as usize)?, section)?;
    let dev = classes_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?, alphabet)?;
    let dev_marks = marked(&dev, pinned_read(&args[9], &args[10], READ_BUDGET as usize)?, section)?;
    let streams = positive(&args[12])?;
    let passes = count(&args[13])?;
    let out = Path::new(&args[14]);
    std::fs::create_dir(out)?;
    let groups = train.len() / section / streams;
    if groups == 0 {
        return Err("the training passage must hold one section a stream".into());
    }
    println!(
        "TOWER_SECTIONS material={} bank={} section={section} streams={streams} deposits_a_pass={groups} train_sections={} dev_sections={}",
        learner.tower.theta.len(),
        learner.tower.bank().map_or("none".to_string(), |b| b.to_text().trim_end().to_string()),
        train.len() / section,
        dev.len() / section
    );
    let (code, cells, named) = held_out(&learner.tower, &dev, &dev_marks, section)?;
    println!("TOWER_HELD pass=opening marked={cells} named={named} bits_a_marked={} elapsed_ms={}", per(code, cells), started.elapsed().as_millis());
    for pass in 0..passes {
        let pass_started = Instant::now();
        let (mut code, mut cells, mut deposits, mut halvings) = (0i64, 0usize, 0usize, 0u32);
        let mut window = (0i64, 0usize);
        for k in 0..groups {
            let ranges: Vec<std::ops::Range<usize>> = (0..streams).map(|s| (k * streams + s) * section..(k * streams + s + 1) * section).collect();
            let parts: Vec<&[usize]> = ranges.iter().map(|r| &train[r.clone()]).collect();
            let compared: Vec<Vec<Option<usize>>> = ranges.iter().map(|r| r.clone().map(|i| (train_marks[i] == 1).then_some(train[i])).collect()).collect();
            let slices: Vec<&[Option<usize>]> = compared.iter().map(|c| c.as_slice()).collect();
            let mut states: Vec<_> = (0..streams).map(|_| learner.tower.rest()).collect();
            let receipt = learner.section_compared(&mut states, &parts, Some(&slices)).map_err(|e| e.to_string())?;
            let coded: usize = compared.iter().map(|c| c[1..].iter().filter(|x| x.is_some()).count()).sum();
            code += receipt.code_before;
            cells += coded;
            window.0 += receipt.code_before;
            window.1 += coded;
            deposits += receipt.deposited as usize;
            halvings += receipt.halvings;
            if (k + 1) % 32 == 0 || k + 1 == groups {
                println!(
                    "TOWER_SECTION pass={pass} deposit={} bits_a_marked={} deposits={deposits} halvings={halvings} elapsed_ms={}",
                    k + 1,
                    per(window.0, window.1),
                    started.elapsed().as_millis()
                );
                window = (0, 0);
            }
        }
        let sha = write_learner(&out.join(format!("STATE.{pass}")), &learner)?;
        println!("TOWER_STATE STATE.{pass} state_sha256={sha}");
        let (dev_code, dev_cells, named) = held_out(&learner.tower, &dev, &dev_marks, section)?;
        println!(
            "TOWER_HELD pass={pass} train_bits_a_marked={} marked={dev_cells} named={named} bits_a_marked={} deposits={deposits}/{groups} pass_ms={} elapsed_ms={}",
            per(code, cells),
            per(dev_code, dev_cells),
            pass_started.elapsed().as_millis(),
            started.elapsed().as_millis()
        );
    }
    let sha = write_learner(&out.join("STATE"), &learner)?;
    println!("TOWER_DONE state_sha256={sha} elapsed_ms={}", started.elapsed().as_millis());
    Ok(())
}
