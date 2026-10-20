//! **The one continuing listener on the octet chart**: one constitution
//! receives each section's source passages, codes and learns its target cell by cell, and releases a
//! release section's continuation cell by cell from its own released prefix until the end letter.
//! This is an exterior example boundary: the octet chart and the section framing are authored codec
//! law (`sections`), and nothing it reports is a gate.
//!
//! [declaration] The executed field is a declared navigator family of the machine's own kind:
//! MNIST's serial template widened to lock 32 classes, rings `[CLASSES + 1, 7, 11]`,
//! source ring 0, contacts `0 → 1 → 2`, receiver ring 2 at aperture one, depth six,
//! tolerance `1/CLASSES`, admittance two, exponent two, offsets `{1, 2}` and pairing
//! `c ↦ c ⊕ 1`. These declarations found the participating field, not learned residual modes.
//! On `--route observed`, every continuing carry closes and locates its keys; the sections
//! route closes without location. Recurring-residual founding and a
//! replacement of the authored depth remain separate obligations.
//! Section population is cut-derived and at least the located capacity; observed population
//! is an explicit run declaration and never raised. All CLI labels, I/O encodings and output
//! format literals below are exterior run declarations; fixture literals stay in test modules.
//!
//! **One target cell** (the learning law, unchanged): with the moment holding the section's prefix,
//! `refine` opens the epoch and the commit arm reads its answer-or-hold at the combined face, before
//! `t` is revealed; `compare` against `E(t)` stages the covector of the declared comparison, and its
//! receipt's code length `−log₂ p̂(t)` under the receiver population's scored face (the wave's faces
//! combined with the tree's at the causal address, the face a release draws from) is the sealed
//! code. The wave's face alone is reported beside it as `wave`. Then `deposit` publishes; then the boundary is re-admitted when its producing port
//! changed, and `t` is ingested into the same moment. A carry-out of the joint clock closes the aeon.
//! After the section's end letter the moment is discarded, and the receiving precision event reads the
//! section's receiver features (publication needs every sample handle consumed, so its unit is the
//! section).
//!
//! **The release** (L2, not teacher-forced): a release section's source passages are ingested; each
//! cell is then the draw arm on the declared exterior key stream (`CellLaw::Draw`), beside the commit
//! arm's answer-or-hold, and the drawn class is ingested as the next cell. Nothing is compared or
//! deposited: the release teaches nothing. It stops at the end letter on an octet boundary, at a held
//! cell, or at the declared maximum.
//!
//! **The baselines** (exterior, online): KT estimators of order 0, 2 and 4 over the continuing cell
//! stream (every ingested cell counted, target cells coded before they are counted), each code the
//! exact product `Π (2N + 16)/(2n + 1)` reported as a bit enclosure with integer endpoints.

use std::collections::{BTreeMap, BTreeSet};
use std::{error::Error, time::Instant};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};

use holonics::compression::landmark::context::code_length;
use holonics::geometry::{RatVec3, screw::ScrewGenerator};
use holonics::hnn::constitution::{
    Carrier, Constitution, ContinuingState, DepositReading, LinearLocus, Locus,
};
use holonics::hnn::encoding::Encoded;
use holonics::hnn::encoding::observed::PairedObservation;
use holonics::hnn::field::{
    ConstitutionRead, ContactDeclaration, Current, Field, FieldDeclaration, RingDeclaration,
};
use holonics::hnn::paired::{PairedCarrier, PairingDeclaration};
use holonics::hnn::port::{Deposit, Handle, MomentId, ReceiptDetail};
use holonics::hnn::ratio::Face;
use holonics::hnn::receiving::cells::{CellDecision, CellLaw};
use holonics::hnn::receiving::{COMBINED, TREE};
use holonics::hnn::reference::ExposedResident;
use holonics::hnn::{ExecutionPort, HnnError};
use holonics::ratio::algebraic::ExactInterval;
use holonics::ratio::{Rat, integer, rat};
use holonics::receiver::release::{KeyStream, ReleaseReturn};

use crate::sections::{self, CLASSES, DIGITS, PLACES, Piece, Section};

/// Declared constitution exact-bit budget. Reaching it ends with the typed
/// `ConstitutionBudget` refusal; the budget is never raised.
pub const BUDGET: u64 = 1u64 << 40;
/// Ring 0 locks every class and carries one node more, as MNIST's template's `17 = 16 + 1` does.
const PERIODS: [u64; 3] = [CLASSES as u64 + 1, 7, 11];
const OFFSETS: [usize; 2] = [1, 2];
const EXPONENT: i64 = 2;
const DEPTH: usize = 6;
/// Exterior key-stream read width in bytes, as the observed image boundary reads it.
pub(crate) const RELEASE_KEY_BYTES: usize = 32;
/// Exterior online baseline orders; these do not govern the native field.
const KT_ORDERS: [usize; 3] = [0, 2, 4];
pub(crate) type Result<T> = std::result::Result<T, Box<dyn Error>>;

#[allow(
    clippy::disallowed_methods,
    reason = "the framed sections and the key file are read only by this exterior example boundary"
)]
pub(crate) fn read(path: &str) -> Result<Vec<u8>> {
    Ok(std::fs::read(path)?)
}

#[allow(
    clippy::disallowed_methods,
    reason = "full resident checkpoints are exterior example I/O"
)]
fn write_checkpoint(path: &str, bytes: &[u8]) -> Result<Vec<u8>> {
    if let Some(parent) = std::path::Path::new(path).parent() {
        std::fs::create_dir_all(parent)?;
    }
    let temporary = format!("{path}.tmp");
    std::fs::write(&temporary, bytes)?;
    let staged = std::fs::read(&temporary)?;
    if staged != bytes {
        return Err(
            format!("staged checkpoint {temporary:?} differed after write/read-back").into(),
        );
    }
    std::fs::rename(&temporary, path)?;
    let committed = std::fs::read(path)?;
    if committed != bytes {
        return Err(format!("committed checkpoint {path:?} differed after atomic rename").into());
    }
    Ok(committed)
}

fn checkpoint_path(directory: &str, completed: usize) -> String {
    format!(
        "{}/step-{completed:06}.state",
        directory.trim_end_matches('/')
    )
}

fn checkpoint_counts(value: &str) -> Result<Vec<usize>> {
    let mut counts = value
        .split(',')
        .map(str::parse::<usize>)
        .collect::<std::result::Result<Vec<_>, _>>()?;
    counts.sort_unstable();
    counts.dedup();
    if counts.is_empty() || counts.contains(&0) {
        return Err("--checkpoint-every requires positive comma-separated section counts".into());
    }
    Ok(counts)
}

pub(crate) fn save_checkpoint<R: ExposedResident>(
    resident: &R,
    opening: &Constitution,
    source: usize,
    directory: &str,
    completed: usize,
) -> Result<()> {
    let state = resident.continuing_state(source)?;
    if state.passage().is_none() {
        return Err("checkpoint lacks the resident passage required for resume/evaluation".into());
    }
    let path = checkpoint_path(directory, completed);
    let text = state.to_text();
    let read_back = write_checkpoint(&path, text.as_bytes())?;
    if read_back != text.as_bytes() {
        return Err(format!("checkpoint {path:?} differed after write/read-back").into());
    }
    let read_back_text = std::str::from_utf8(&read_back)?;
    let parsed = ContinuingState::from_text(read_back_text, opening.budget())?;
    if parsed != state {
        return Err(
            format!("checkpoint {path:?} did not parse to its exact resident state").into(),
        );
    }
    let restored = opening.clone().continued(&parsed)?;
    if &restored != resident.constitution() {
        return Err(
            format!("checkpoint {path:?} does not restore the resident constitution").into(),
        );
    }
    println!(
        "checkpoint completed_sections={completed} kind=full_resident path={path:?} source_ring={source} bytes={} byte_roundtrip_equal=true state_parse_equal=true constitution_equal=true passage_included=true",
        read_back.len(),
    );
    Ok(())
}

/// Cost discovery for the existing resident codec, with create-only exterior publication.
/// This does not serialize ObservedCrib and cannot claim an observed-listener resume.
#[allow(
    clippy::disallowed_methods,
    clippy::disallowed_types,
    reason = "create-only checkpoint cost measurement is exterior example I/O"
)]
pub(crate) fn save_checkpoint_cost_profile<R: ExposedResident>(
    resident: &R,
    opening: &Constitution,
    source: usize,
    directory: &str,
    completed: usize,
    receiver_clock: (usize, u64),
    mut check: impl FnMut(&str) -> Result<()>,
) -> Result<()> {
    use std::io::Write;
    let path = checkpoint_path(directory, completed);
    let staged_path = format!("{path}.tmp");
    if std::path::Path::new(&path).exists() || std::path::Path::new(&staged_path).exists() {
        return Err("cost checkpoint refuses an existing destination or staging file".into());
    }
    check("resident snapshot")?;
    let started = Instant::now();
    let state = resident
        .continuing_state(source)?
        .with_receiver_ingress_ticks(receiver_clock.0, receiver_clock.1)?;
    println!(
        "cost_checkpoint component=snapshot elapsed_ns={}",
        elapsed(started)
    );
    if state.passage().is_none() {
        return Err("cost checkpoint lacks the continuing passage".into());
    }
    check("resident serialization")?;
    let started = Instant::now();
    let text = state.to_text();
    println!(
        "cost_checkpoint component=serialize elapsed_ns={} bytes={}",
        elapsed(started),
        text.len()
    );
    check("checkpoint create-only I/O")?;
    let started = Instant::now();
    if let Some(parent) = std::path::Path::new(&path).parent() {
        std::fs::create_dir_all(parent)?;
    }
    let mut staged = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&staged_path)?;
    staged.write_all(text.as_bytes())?;
    staged.sync_all()?;
    drop(staged);
    let staged_bytes = std::fs::read(&staged_path)?;
    if staged_bytes != text.as_bytes() {
        return Err("cost checkpoint staged readback differs".into());
    }
    // A hard link publishes atomically and refuses a raced-in destination. Keep the exact
    // staging inode as private evidence; no existing file is replaced or removed.
    std::fs::hard_link(&staged_path, &path)?;
    let committed = std::fs::read(&path)?;
    // Include publication-directory persistence in the measured I/O, as a production save does.
    // The separate staging name is deliberately preserved as private exact-byte evidence.
    let parent = std::path::Path::new(&path)
        .parent()
        .ok_or("checkpoint has no directory")?;
    std::fs::File::open(parent)?.sync_all()?;
    println!(
        "cost_checkpoint component=create_sync_read_link_read_directory_fsync elapsed_ns={} bytes={} staging_preserved=true staging_reason=private_exact_byte_evidence directory_fsync=true",
        elapsed(started),
        committed.len()
    );
    if committed != text.as_bytes() {
        return Err("cost checkpoint committed readback differs".into());
    }
    check("resident checkpoint parse")?;
    let started = Instant::now();
    let parsed = ContinuingState::from_text(std::str::from_utf8(&committed)?, opening.budget())?;
    println!(
        "cost_checkpoint component=parse elapsed_ns={}",
        elapsed(started)
    );
    check("resident checkpoint exact state equality")?;
    let started = Instant::now();
    if parsed != state {
        return Err("cost checkpoint parsed state differs".into());
    }
    println!(
        "cost_checkpoint component=state_equality elapsed_ns={}",
        elapsed(started)
    );
    check("checkpoint constitution reconstruction")?;
    let started = Instant::now();
    let restored = opening.clone().continued(&parsed)?;
    println!(
        "cost_checkpoint component=constitution_reconstruct elapsed_ns={}",
        elapsed(started)
    );
    check("checkpoint constitution equality")?;
    let started = Instant::now();
    if &restored != resident.constitution() {
        return Err("cost checkpoint reconstructed constitution differs".into());
    }
    println!(
        "cost_checkpoint component=constitution_equality elapsed_ns={}",
        elapsed(started)
    );
    check("checkpoint completion")?;
    println!(
        "cost_checkpoint complete=true scope=resident_only completed_cells={completed} bytes={} byte_roundtrip_equal=true state_parse_equal=true constitution_equal=true receiver_ingress_clock={receiver_clock:?} observed_crib_codec=false observed_resume=false",
        committed.len(),
    );
    Ok(())
}

#[allow(
    clippy::disallowed_methods,
    reason = "full resident checkpoints are exterior example I/O"
)]
fn save_latest_checkpoint<R: ExposedResident>(
    resident: &R,
    opening: &Constitution,
    source: usize,
    path: &str,
    completed: usize,
) -> Result<()> {
    let state = resident.continuing_state(source)?;
    if state.passage().is_none() {
        return Err("checkpoint lacks the resident passage required for resume/evaluation".into());
    }
    let text = state.to_text();
    let read_back = write_checkpoint(path, text.as_bytes())?;
    if read_back != text.as_bytes() {
        return Err(format!("latest checkpoint {path:?} differed after write/read-back").into());
    }
    let parsed = ContinuingState::from_text(std::str::from_utf8(&read_back)?, opening.budget())?;
    if parsed != state || opening.clone().continued(&parsed)? != *resident.constitution() {
        return Err(
            format!("latest checkpoint {path:?} failed state/constitution round-trip").into(),
        );
    }
    println!(
        "checkpoint_latest completed_sections={completed} kind=full_resident path={path:?} source_ring={source} bytes={} byte_roundtrip_equal=true state_parse_equal=true constitution_equal=true passage_included=true",
        read_back.len(),
    );
    Ok(())
}

pub(crate) fn field(population: u64) -> Result<Field> {
    let mut declared = FieldDeclaration::campaign_one(population);
    let axis = ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero());
    declared.rings = PERIODS
        .iter()
        .enumerate()
        .map(|(g, &period)| RingDeclaration {
            period,
            screw: axis.clone(),
            placements: (0..period)
                .map(|n| FieldDeclaration::quarter_turn(n, period))
                .collect(),
            lock: if g == 0 {
                (0..CLASSES as u64).collect()
            } else {
                Vec::new()
            },
            reflector: (0..period)
                .map(|p| ((period - p) % period) as usize)
                .collect(),
            admittance: integer(2),
            initial: 0,
        })
        .collect();
    declared.contacts = [(0, 1), (1, 2)]
        .iter()
        .map(|&(from, to)| ContactDeclaration {
            from,
            to,
            channel: (0..PERIODS[from].min(PERIODS[to]) as usize)
                .map(|node| (node, node))
                .collect(),
            admittance: integer(2),
            exponent: integer(EXPONENT),
        })
        .collect();
    declared.sources = vec![0];
    declared.loops.clear();
    declared.alphabet = CLASSES;
    declared.offsets = OFFSETS.to_vec();
    declared.receivers[0].ring = 2;
    declared.receivers[0].aperture = 1;
    declared.receivers[0].depth = DEPTH;
    declared.receivers[0].tolerance = rat(1, CLASSES as i64);
    declared.lattice.clear();
    Ok(Field::declare(declared.by_lattice_rule())?)
}

/// An exact sum of code-length enclosures, reported with integer endpoints `[⌊Σ lower⌋, ⌈Σ upper⌉]`.
#[derive(Clone, Debug)]
pub(super) struct CodeSum {
    lower: Rat,
    upper: Rat,
    cells: u64,
}

impl Default for CodeSum {
    fn default() -> Self {
        Self {
            lower: integer(0),
            upper: integer(0),
            cells: 0,
        }
    }
}

impl CodeSum {
    pub(super) fn add(&mut self, interval: &ExactInterval) {
        self.lower += &interval.lower;
        self.upper += &interval.upper;
        self.cells += 1;
    }

    pub(super) fn merge(&mut self, other: &CodeSum) {
        self.lower += &other.lower;
        self.upper += &other.upper;
        self.cells += other.cells;
    }

    fn bits(&self) -> String {
        format!(
            "[{},{}]",
            self.lower.floor().to_integer(),
            self.upper.ceil().to_integer()
        )
    }

    /// Exact endpoints of the summed enclosure; no exterior integer rounding.
    pub(super) fn exact_endpoints(&self) -> String {
        format!("[{},{}]", self.lower, self.upper)
    }

    pub(super) fn cells(&self) -> u64 {
        self.cells
    }
}

/// An online order-`k` KT code over the continuing base-16 digit stream (a cell's class read as its base-16 digit,
/// whatever place the chart bears): the exact product of the coded cells' inverse probabilities,
/// `Π (2N + 16)/(2n + 1)`.
#[derive(Clone)]
struct Kt {
    order: usize,
    counts: BTreeMap<(usize, u64), [u64; DIGITS]>,
    numerator: BigUint,
    denominator: BigUint,
}

impl Kt {
    fn new(order: usize) -> Self {
        Self {
            order,
            counts: BTreeMap::new(),
            numerator: BigUint::one(),
            denominator: BigUint::one(),
        }
    }

    fn context(&self, history: &[usize]) -> (usize, u64) {
        let seen = history.len().min(self.order);
        let packed = history[history.len() - seen..]
            .iter()
            .fold(0u64, |key, &class| (key << 4) | (class % DIGITS) as u64);
        (seen, packed)
    }

    /// The cell's probability `(2n + 1)/(2N + 16)` at its context, before it is counted.
    fn code(&mut self, history: &[usize], class: usize) -> (u64, u64) {
        let counts = self
            .counts
            .get(&self.context(history))
            .copied()
            .unwrap_or([0; DIGITS]);
        let n = 2 * counts[class % DIGITS] + 1;
        let total = 2 * counts.iter().sum::<u64>() + DIGITS as u64;
        self.numerator *= n;
        self.denominator *= total;
        (n, total)
    }

    fn count(&mut self, history: &[usize], class: usize) {
        let context = self.context(history);
        self.counts.entry(context).or_insert([0; DIGITS])[class % DIGITS] += 1;
    }

    /// `log₂(D/N)` enclosed by bit lengths: `[ℓ(D) − ℓ(N) − 1, ℓ(D) − ℓ(N) + 1]`.
    fn bits(&self) -> String {
        let difference = self.denominator.bits() as i128 - self.numerator.bits() as i128;
        format!("[{},{}]", difference - 1, difference + 1)
    }
}

/// The exterior cell stream the baselines read: its last cells, enough for the largest order.
#[derive(Clone)]
struct Stream {
    recent: Vec<usize>,
    baselines: Vec<Kt>,
}

impl Stream {
    fn new() -> Self {
        Self {
            recent: Vec::new(),
            baselines: KT_ORDERS.iter().map(|&order| Kt::new(order)).collect(),
        }
    }

    fn code(&mut self, class: usize) -> Vec<(u64, u64)> {
        let recent = &self.recent;
        self.baselines
            .iter_mut()
            .map(|kt| kt.code(recent, class))
            .collect()
    }

    fn count(&mut self, class: usize) {
        for kt in &mut self.baselines {
            kt.count(&self.recent, class);
        }
        self.advance(class);
    }

    /// Moves the context past a cell without counting it.
    fn advance(&mut self, class: usize) {
        self.recent.push(class);
        let keep = KT_ORDERS.iter().copied().max().unwrap_or(0);
        if self.recent.len() > keep {
            self.recent.remove(0);
        }
    }

    /// The baselines frozen at their counts, as the read freezes the constitution: each code
    /// restarts at one, and a frozen read codes and advances without counting.
    fn frozen(&self) -> Self {
        let mut frozen = self.clone();
        for kt in &mut frozen.baselines {
            kt.numerator = BigUint::one();
            kt.denominator = BigUint::one();
        }
        frozen
    }

    fn bits(&self) -> String {
        self.baselines
            .iter()
            .map(|kt| format!("kt{}={}", kt.order, kt.bits()))
            .collect::<Vec<_>>()
            .join(" ")
    }
}

/// Elapsed nanoseconds by kind, summed exactly.
#[derive(Clone, Default)]
pub(crate) struct Cost {
    refine: u128,
    compare: u128,
    deposit: u128,
    ingest: u128,
    close_aeon: u128,
    admission: u128,
    admissions: u64,
    close_aeons: u64,
    precision: u128,
    release_cells: u128,
}

impl Cost {
    fn merge(&mut self, other: &Cost) {
        self.refine += other.refine;
        self.compare += other.compare;
        self.deposit += other.deposit;
        self.ingest += other.ingest;
        self.close_aeon += other.close_aeon;
        self.admission += other.admission;
        self.admissions += other.admissions;
        self.close_aeons += other.close_aeons;
        self.precision += other.precision;
        self.release_cells += other.release_cells;
    }

    fn line(&self) -> String {
        format!(
            "refine_ns={} compare_ns={} deposit_ns={} ingest_ns={} close_aeon_ns={} close_aeons={} admission_ns={} admissions={} precision_ns={} release_cells_ns={}",
            self.refine,
            self.compare,
            self.deposit,
            self.ingest,
            self.close_aeon,
            self.close_aeons,
            self.admission,
            self.admissions,
            self.precision,
            self.release_cells,
        )
    }
}

pub(crate) fn elapsed(started: Instant) -> u128 {
    started.elapsed().as_nanos()
}

/// The exact sum of absolute released contact-factor residuals, per entry. It bounds
/// `|Σe|` without picking report precision. Read against half the locus's founding
/// unit, the bound of Lean `HNN/LatticeDeposit/Rebase.history_release_lt`. Empty while
/// the factors keep their exact remainder and release nothing.
#[derive(Default)]
struct FactorReleases {
    sums: BTreeMap<(Locus, Carrier, usize), Rat>,
    founding: BTreeMap<Locus, u32>,
}

impl FactorReleases {
    fn add(&mut self, reading: &DepositReading, constitution: &Constitution) -> Result<()> {
        for (locus, carrier, entry, released) in &reading.released {
            if !matches!(carrier, Carrier::Factor(_) | Carrier::FactorScale(_))
                || released.is_zero()
            {
                continue;
            }
            if !self.founding.contains_key(locus) {
                self.founding
                    .insert(*locus, constitution.lattice(*locus)?.exponent());
            }
            *self
                .sums
                .entry((*locus, *carrier, *entry))
                .or_insert_with(Rat::zero) += released.abs();
        }
        Ok(())
    }

    /// Per locus: the entries that released, the largest bound, and its ordering against half the
    /// founding unit `2^(−L₀−1)`.
    fn line(&self) -> String {
        let mut by_locus: BTreeMap<Locus, (usize, Rat)> = BTreeMap::new();
        for ((locus, _, _), sum) in &self.sums {
            let (count, largest) = by_locus.entry(*locus).or_insert((0, Rat::zero()));
            *count += 1;
            if sum > largest {
                *largest = sum.clone();
            }
        }
        let parts: Vec<String> = by_locus
            .iter()
            .map(|(locus, (count, largest))| {
                let exponent = self.founding[locus] + 1;
                let half = Rat::new(BigInt::one(), BigInt::one() << exponent as usize);
                let ordering = if largest < &half { "lt" } else { "ge" };
                format!("{locus:?}:entries={count},largest<={largest},half_founding_unit=2^-{exponent},{ordering}")
            })
            .collect();
        format!("[{}]", parts.join(";"))
    }
}

/// The families one deposit stepped, each as `locus/family:k` with its certified exponent `k` (the
/// step is `2^k`), a family whose entries took no lattice coordinate marked `~` (its move retained
/// below the lattice).
pub(crate) fn stepped_families(reading: &DepositReading) -> String {
    let out: Vec<String> = reading
        .steps
        .iter()
        .map(|(locus, step)| {
            let kept = if reading.vanished.contains(&(*locus, step.family)) {
                "~"
            } else {
                ""
            };
            format!("{locus:?}/{:?}:{}{kept}", step.family, step.step.exponent)
        })
        .collect();
    format!("[{}]", out.join(","))
}

/// The exact receiving operands of one staged deposit: each linear sample's feature, nothing else.
fn receiving_features(deposit: &Deposit, ring: usize) -> Vec<Vec<Rat>> {
    deposit
        .linear()
        .iter()
        .filter(|step| step.locus == LinearLocus::Receiving(ring))
        .flat_map(|step| step.samples.iter().map(|sample| sample.feature.clone()))
        .collect()
}

/// The listener's boundary at the current material: kept while its producing port is unchanged,
/// re-admitted when a deposit changed it.
struct Boundary {
    pairing: PairingDeclaration,
    observation: PairedObservation,
}

impl Boundary {
    fn current(&mut self, field: &Field, material: &Constitution, cost: &mut Cost) -> Result<()> {
        if self.observation.check_material(material).is_err() {
            let started = Instant::now();
            self.observation = PairedObservation::admit(field, material, &self.pairing)?;
            cost.admission += elapsed(started);
            cost.admissions += 1;
        }
        Ok(())
    }
}

/// Ingest a passage into the moment (opened when `None`), closing the aeon at every carry-out.
pub(crate) fn ingest<P: ExecutionPort>(
    port: &P,
    resident: &mut P::Resident,
    moment: Option<MomentId>,
    encoded: &Encoded,
    cost: &mut Cost,
) -> Result<MomentId>
where
    P::Resident: ExposedResident,
{
    let mut at = 0;
    let mut moment = moment;
    while at < encoded.len() {
        let part = encoded.part(at..encoded.len())?;
        let started = Instant::now();
        let (id, receipt) = port.ingest(resident, moment.as_ref(), &part)?;
        cost.ingest += elapsed(started);
        let consumed = receipt
            .forward
            .into_present()
            .ok_or("ingest returned no receipt")?;
        if consumed.cells == 0 {
            return Err("ingestion made no progress".into());
        }
        at += consumed.cells;
        moment = Some(id);
        if consumed.carry_out {
            let admitted = resident.admitted().to_vec();
            let started = Instant::now();
            let closed = port.close_aeon(resident, &admitted)?;
            cost.close_aeon += elapsed(started);
            cost.close_aeons += 1;
            if let Some(boundary) = closed.forward.present() {
                println!(
                    "aeon cells={} released={:?} constitution_bits=[{},{}] state_bits=[{},{}]",
                    boundary.cells,
                    boundary.collapse.released,
                    boundary.collapse.bits[0],
                    boundary.collapse.bits[1],
                    boundary.state_bits[0],
                    boundary.state_bits[1],
                );
            }
        }
    }
    moment.ok_or_else(|| "an empty passage opened no moment".into())
}

/// The compare's code lengths at its target: the receiver population's scored face (the wave's faces
/// combined with the tree's at the causal address), the face the release draws from, and beside it
/// the tree's executed face alone (the population's first family).
pub(crate) fn scored_code(
    detail: &ReceiptDetail,
) -> Result<(ExactInterval, Option<ExactInterval>)> {
    match detail {
        ReceiptDetail::Compare {
            code_length, tree, ..
        } => Ok((code_length.clone(), tree.first().cloned())),
        _ => Err("a compare returned no compare receipt".into()),
    }
}

/// An exact code-length enclosure with integer endpoints `[⌊lower⌋, ⌈upper⌉]`.
pub(crate) fn enclosure(interval: &ExactInterval) -> String {
    format!(
        "[{},{}]",
        interval.lower.floor().to_integer(),
        interval.upper.ceil().to_integer()
    )
}

/// Accumulated likelihood codes since the population opening, excluding prior costs.
/// A positive combined-minus-tree gap means the combined family's likelihood trails.
/// No posterior-weight claim is made: priors, charging, and unresolved intervals remain distinct.
fn population_line(constitution: &Constitution, ring: usize) -> String {
    let Some(population) = constitution.population(ring) else {
        return "population_tree=unavailable population_combined=unavailable population_gap=unavailable".to_owned();
    };
    let tree = population.family_code(TREE).ok().flatten();
    let combined = population.family_code(COMBINED).ok().flatten();
    let display = |value: &Option<ExactInterval>| {
        value
            .as_ref()
            .map_or_else(|| "unavailable".to_owned(), enclosure)
    };
    let gap = match (&tree, &combined) {
        (Some(tree), Some(combined)) => enclosure(&ExactInterval {
            lower: &combined.lower - &tree.upper,
            upper: &combined.upper - &tree.lower,
        }),
        _ => "unavailable".to_owned(),
    };
    format!(
        "population_tree={} population_combined={} population_gap={gap}",
        display(&tree),
        display(&combined)
    )
}

/// The wave face's exact spread over the classes: the number of distinct grain cells
/// `(carry, phase)` and distinct rational fibres of the listener's raw wave face.
/// A face's mass reads only its grain cell
/// (`p̂_c = 2^(n_c − n_top) θ^(k_c) / Z`, `hnn::ratio::Face`), so the face is exactly uniform iff the
/// first count is 1: Face validates 0 <= phase < grain, making carry + phase/grain injective.
/// Distinct fibres under one grain cell are motion that stays below the grain.
fn face_spread(face: &Face) -> (usize, usize) {
    let cells: BTreeSet<(&BigInt, u64)> = face
        .cells()
        .iter()
        .map(|cell| (&cell.carry, cell.phase))
        .collect();
    let fibres: BTreeSet<&Rat> = face
        .cells()
        .iter()
        .map(|cell| {
            cell.fibre
                .as_rational()
                .expect("listener flatness reads the raw rational wave face")
        })
        .collect();
    (cells.len(), fibres.len())
}

/// The count of exactly uniform wave faces over a run of cells, and of those whose fibres differ.
#[derive(Default)]
struct Flatness {
    faces: u64,
    flat: u64,
    flat_fibred: u64,
}

impl Flatness {
    fn add(&mut self, (cells, fibres): (usize, usize)) {
        self.faces += 1;
        if cells == 1 {
            self.flat += 1;
            if fibres > 1 {
                self.flat_fibred += 1;
            }
        }
    }

    fn line(&self) -> String {
        format!(
            "wave_flat_faces={}/{} wave_flat_fibred={}",
            self.flat, self.faces, self.flat_fibred
        )
    }
}

/// The current deposit receipt's prior exponent reading, `from->to`, with its held reason.
/// This reports the active law's receipt; it does not infer monotonicity or recompute an old prior rule.
fn prior_move(reading: &DepositReading) -> String {
    reading
        .charts
        .iter()
        .filter(|(locus, _)| matches!(locus, Locus::ReceivingMap(_)))
        .filter_map(|(_, chart)| chart.prior.as_ref())
        .map(|moved| match &moved.held {
            Some(held) => format!("{}->{}/{held:?}", moved.from, moved.to),
            None => format!("{}->{}", moved.from, moved.to),
        })
        .collect::<Vec<_>>()
        .join(",")
}

/// The kind of the target octet a cell belongs to, read on the exterior octet chart: an observer's
/// split of the read, never a law. The cells past the target's octets are its end letter.
fn octet_kind(target: &[u8], j: usize) -> &'static str {
    match target.get(j / PLACES) {
        None => "end",
        Some(b'0'..=b'9') => "digit",
        Some(b'a'..=b'z' | b'A'..=b'Z') => "letter",
        Some(b' ') => "space",
        Some(b'\n') => "newline",
        Some(b'<' | b'>') => "angle",
        Some(b'=') => "equals",
        Some(b'#') => "hash",
        Some(_) => "other",
    }
}

/// The drawn class's own code under the scored face it was drawn from, `−log₂ p(c)` enclosed by
/// the face's mass enclosure: the release's surprise, comparable with a reference's teacher-forced
/// code per cell.
pub(crate) fn drawn_code(cell: &CellDecision, class: usize) -> Result<ExactInterval> {
    let mass = cell
        .face
        .get(class)
        .ok_or("the draw's face has no mass for its class")?;
    if !mass.lower.is_positive() {
        return Err("the drawn class's mass enclosure reaches zero".into());
    }
    Ok(ExactInterval {
        lower: code_length(&mass.upper)?.lower,
        upper: code_length(&mass.lower)?.upper,
    })
}

/// Missing diagnostic enclosures never stop the listener or masquerade as zero code.
#[derive(Default)]
struct DiagnosticCode {
    code: CodeSum,
    missing: u64,
}

impl DiagnosticCode {
    fn add(&mut self, interval: Option<&ExactInterval>) {
        match interval {
            Some(value) => self.code.add(value),
            None => self.missing += 1,
        }
    }
    fn merge(&mut self, other: &Self) {
        self.code.merge(&other.code);
        self.missing += other.missing;
    }
    fn bits(&self) -> String {
        if self.missing == 0 {
            self.code.bits()
        } else {
            format!("unavailable(missing={})", self.missing)
        }
    }
}

/// One kind's read: its cells' sealed and tree codes and the commit arm's outcomes against the
/// target (a certified single class equal to it, a certified single class other than it, a hold).
#[derive(Default)]
struct KindRead {
    sealed: CodeSum,
    tree: DiagnosticCode,
    right: u64,
    wrong: u64,
    hold: u64,
}

#[cfg(test)]
mod diagnostic_tests {
    use super::*;

    #[test]
    fn face_spread_distinguishes_normalized_cells_and_fibres() {
        use holonics::hnn::receiving::ReceivingRead;
        fn face(values: &[Rat]) -> Face {
            let logits = values
                .iter()
                .flat_map(|x| [x.clone(), integer(0)])
                .collect();
            Face::of_read(&ReceivingRead::of_logits(logits, 4), 4).unwrap()
        }
        assert_eq!(face_spread(&face(&[integer(0)])), (1, 1));
        let f = face(&[rat(1, 16), rat(1, 8)]);
        assert_eq!(face_spread(&f), (1, 2));
        assert_eq!(f.mass(0).unwrap(), f.mass(1).unwrap());
        assert_eq!(face_spread(&face(&[integer(0), rat(1, 4)])), (2, 1));
        assert_eq!(face_spread(&face(&[integer(0), integer(1)])), (2, 1));
        let mut counts = Flatness::default();
        counts.add((1, 1));
        counts.add((1, 2));
        counts.add((2, 1));
        assert_eq!(counts.line(), "wave_flat_faces=2/3 wave_flat_fibred=1");
    }

    #[test]
    fn diagnostic_code_keeps_unavailable_distinct_from_zero() {
        let mut code = DiagnosticCode::default();
        code.add(Some(&ExactInterval::point(integer(2))));
        assert_eq!(code.bits(), "[2,2]");
        code.add(None);
        assert_eq!(code.bits(), "unavailable(missing=1)");
        let mut total = DiagnosticCode::default();
        total.merge(&code);
        assert_eq!(total.bits(), code.bits());
    }

    #[test]
    fn drawn_surprise_uses_the_scored_mass_without_mutating_the_decision() {
        let mut cell = CellDecision {
            phase: 0,
            release: ReleaseReturn::Hold,
            classes: vec![0],
            key: None,
            bits: 4,
            face: vec![ExactInterval::point(rat(1, 4))],
            scored_face: None,
        };
        let before = cell.clone();
        let code = drawn_code(&cell, 0).unwrap();
        assert!(code.lower <= integer(2) && code.upper >= integer(2));
        assert_eq!(cell, before);
        cell.face[0].lower = integer(0);
        let mut code = DiagnosticCode::default();
        code.add(drawn_code(&cell, 0).ok().as_ref());
        assert_eq!(code.bits(), "unavailable(missing=1)");
        assert!(drawn_code(&cell, 1).is_err());
    }

    #[test]
    fn exterior_kind_counts_both_digits_and_the_end_separately() {
        let target = b"A1 \n<=>#?";
        for (i, kind) in [
            "letter", "digit", "space", "newline", "angle", "equals", "angle", "hash", "other",
        ]
        .iter()
        .enumerate()
        {
            for place in 0..PLACES {
                assert_eq!(octet_kind(target, i * PLACES + place), *kind);
            }
        }
        assert_eq!(octet_kind(target, target.len() * PLACES), "end");
        assert_eq!(octet_kind(target, target.len() * PLACES + 1), "end");
    }
}

/// The commit arm's answer-or-hold at the receiver's combined face, read before the target.
fn committed_classes<P: ExecutionPort>(
    port: &P,
    resident: &mut P::Resident,
    pending: &holonics::hnn::port::PendingId,
    cost: &mut Cost,
) -> Result<(String, Vec<usize>, bool)>
where
    P::Resident: ExposedResident,
{
    let started = Instant::now();
    let committed = port
        .release_cells(resident, pending, CellLaw::Commit)?
        .forward
        .into_present()
        .ok_or("the commit returned no cells")?;
    cost.release_cells += elapsed(started);
    let cell = committed
        .cells
        .first()
        .ok_or("the commit decided no cell")?;
    Ok((
        arm(cell),
        cell.classes.clone(),
        matches!(cell.release, ReleaseReturn::Released { .. }),
    ))
}

fn arm(cell: &CellDecision) -> String {
    match &cell.release {
        ReleaseReturn::Released { .. } => format!("released{:?}", cell.classes),
        ReleaseReturn::Drawn(draw) => format!(
            "drawn(class={},key={},cell=[{},{}))",
            draw.class,
            cell.key
                .as_ref()
                .map_or("none".into(), |(index, _)| index.to_string()),
            draw.prior_upper,
            draw.through_lower,
        ),
        ReleaseReturn::Hold => format!("hold{:?}", cell.classes),
        ReleaseReturn::Unresolved(_) => format!("unresolved{:?}", cell.classes),
        ReleaseReturn::NoContinuationBridges { .. } => "no_key".into(),
        other => format!("{other:?}"),
    }
}

/// Octets as text, every octet that is not printable ASCII or a line end escaped as `\xNN`.
/// The released pieces as text: printable octets as themselves, other octets as `\xNN`, and a
/// slipped cell as `⟨place digit⟩` (`⟨H7⟩`, `⟨L7⟩`), so no released cell is hidden.
pub(crate) fn shown(pieces: &[Piece]) -> String {
    let mut text = String::new();
    for piece in pieces {
        match *piece {
            Piece::Octet(b'\n') => text.push('\n'),
            Piece::Octet(octet @ 0x20..=0x7e) => text.push(char::from(octet)),
            Piece::Octet(octet) => text.push_str(&format!("\\x{octet:02x}")),
            Piece::End => text.push_str("⟨end⟩"),
            Piece::Slip(class) => {
                let place = if class < DIGITS { 'H' } else { 'L' };
                text.push_str(&format!("⟨{place}{:x}⟩", class % DIGITS));
            }
        }
    }
    text
}

/// Exterior run declaration: a route has no implicit default.
pub(crate) fn take_route(args: &mut Vec<String>) -> Result<String> {
    let at = args
        .iter()
        .position(|arg| arg == "--route")
        .ok_or("missing --route sections|observed")?;
    let route = args
        .get(at + 1)
        .ok_or("--route needs sections or observed")?
        .clone();
    if !matches!(route.as_str(), "sections" | "observed") {
        return Err(format!("unknown route {route:?}; expected sections or observed").into());
    }
    args.drain(at..at + 2);
    Ok(route)
}

pub(crate) struct Options {
    arrival_context: bool,
    learn: Option<String>,
    learn_count: Option<usize>,
    release: Option<String>,
    release_count: Option<usize>,
    read: Option<String>,
    read_count: Option<usize>,
    read_from: usize,
    keys: Option<String>,
    population: Option<u64>,
    max_release_octets: Option<usize>,
    checkpoint_dir: Option<String>,
    checkpoint_every: Vec<usize>,
    checkpoint_in: Option<String>,
    learn_from: usize,
    checkpoint_latest: Option<String>,
    wall_seconds: Option<u64>,
}

pub(crate) fn options(args: &[String]) -> Result<Options> {
    let mut options = Options {
        arrival_context: false,
        learn: None,
        learn_count: None,
        release: None,
        release_count: None,
        read: None,
        read_count: None,
        read_from: 0,
        keys: None,
        population: None,
        max_release_octets: None,
        checkpoint_dir: None,
        checkpoint_every: Vec::new(),
        checkpoint_in: None,
        learn_from: 0,
        checkpoint_latest: None,
        wall_seconds: None,
    };
    let mut at = 0;
    while at < args.len() {
        if args[at] == "--arrival-context" {
            options.arrival_context = true;
            at += 1;
            continue;
        }
        let value = args
            .get(at + 1)
            .ok_or_else(|| format!("{} needs a value", args[at]))?
            .clone();
        match args[at].as_str() {
            "--learn" => options.learn = Some(value),
            "--learn-count" => options.learn_count = Some(value.parse()?),
            "--release" => options.release = Some(value),
            "--release-count" => options.release_count = Some(value.parse()?),
            "--read" => options.read = Some(value),
            "--read-count" => options.read_count = Some(value.parse()?),
            "--read-from" => options.read_from = value.parse()?,
            "--keys" => options.keys = Some(value),
            "--population" => options.population = Some(value.parse()?),
            "--max-release-octets" => options.max_release_octets = Some(value.parse()?),
            "--checkpoint-dir" => options.checkpoint_dir = Some(value),
            "--checkpoint-every" => options.checkpoint_every = checkpoint_counts(&value)?,
            "--checkpoint-in" => options.checkpoint_in = Some(value),
            "--learn-from" => options.learn_from = value.parse()?,
            "--checkpoint-latest" => options.checkpoint_latest = Some(value),
            "--wall-seconds" => options.wall_seconds = Some(value.parse()?),
            other => return Err(format!("unknown argument {other}").into()),
        }
        at += 2;
    }
    if options.read.is_some() && options.release.is_some() {
        return Err(
            "teacher-forced read and question-only release require separate processes".into(),
        );
    }
    if !options.checkpoint_every.is_empty() && options.checkpoint_dir.is_none() {
        return Err("--checkpoint-every requires --checkpoint-dir".into());
    }
    if options.wall_seconds == Some(0) {
        return Err("--wall-seconds must be positive".into());
    }
    if options.wall_seconds.is_some() && options.checkpoint_latest.is_none() {
        return Err("--wall-seconds requires --checkpoint-latest for safe boundary resume".into());
    }
    if options.checkpoint_latest.is_some() && options.learn.is_none() {
        return Err("--checkpoint-latest requires a learning frame".into());
    }
    if options.learn_from > 0 && options.checkpoint_in.is_none() {
        return Err("--learn-from requires --checkpoint-in".into());
    }
    if options.checkpoint_in.is_some() && options.learn.is_some() && options.learn_from == 0 {
        return Err(
            "resuming a learning frame with --checkpoint-in requires --learn-from N".into(),
        );
    }
    if options.checkpoint_in.is_some() && options.population.is_none() {
        return Err(
            "--checkpoint-in requires --population from the original field declaration".into(),
        );
    }
    if options.max_release_octets.is_none() {
        return Err("--route sections requires explicit --max-release-octets".into());
    }
    if options.max_release_octets == Some(0) {
        return Err("--max-release-octets must be positive".into());
    }
    Ok(options)
}

#[cfg(test)]
mod boundary_tests {
    fn declared(args: &[String]) -> super::Result<super::Options> {
        let mut args = args.to_vec();
        args.extend(["--max-release-octets", "1"].map(str::to_owned));
        super::options(&args)
    }
    #[test]
    fn arrival_context_is_explicit_and_compatible_with_paired_observation() {
        use super::*;
        use holonics::hnn::constitution::ReceivingLayout;
        assert!(!declared(&[]).unwrap().arrival_context);
        assert!(
            declared(&["--arrival-context".to_owned()])
                .unwrap()
                .arrival_context
        );
        let population = holonics::hnn::moment::capacity_located(
            &PERIODS,
            &vec![holonics::hnn::RingAdvance::Lock; PERIODS.len()],
            &[0],
            CLASSES,
            &OFFSETS,
        )
        .unwrap()
        .n_star();
        let field = field(u64::try_from(population).unwrap()).unwrap();
        let pairing = PairingDeclaration::Family {
            table: (0..CLASSES).map(|c| (c, c ^ 1)).collect(),
        };
        let mut material = PairedCarrier::found(
            &field,
            Constitution::initial(&field, BUDGET).unwrap(),
            0,
            &pairing,
        )
        .unwrap()
        .0;
        for receiver in field.receivers() {
            assert_eq!(
                material.receiving_layout(receiver.ring),
                Some(ReceivingLayout::Single)
            );
            material
                .bind_arrival_context_receiving(receiver.ring)
                .unwrap();
            assert!(matches!(
                material.receiving_layout(receiver.ring),
                Some(ReceivingLayout::ArrivalContext { .. })
            ));
        }
        PairedObservation::admit(&field, &material, &pairing).unwrap();
    }

    #[test]
    fn an_explicit_population_below_the_located_capacity_is_refused() {
        let refusal = super::declared_population(Some(17), 100, 19)
            .unwrap_err()
            .to_string();
        assert!(refusal.contains("17"));
        assert!(refusal.contains("19"));
        assert_eq!(super::declared_population(Some(19), 100, 19).unwrap(), 19);
        assert_eq!(super::declared_population(None, 17, 19).unwrap(), 19);
        assert_eq!(super::declared_population(None, 23, 19).unwrap(), 23);
    }

    #[test]
    fn teacher_forced_read_and_question_only_release_cannot_share_a_process() {
        let args = [
            "--read",
            "development_read.hlsn",
            "--release",
            "development_release.hlsn",
        ]
        .map(str::to_owned);
        assert!(declared(&args).is_err());
        assert!(declared(&args[..2]).is_ok());
        assert!(declared(&args[2..]).is_ok());
    }

    #[test]
    fn full_resident_checkpoint_options_are_explicit_and_ordered() {
        let args = [
            "--checkpoint-dir",
            "checkpoints",
            "--checkpoint-every",
            "64,16,64",
        ]
        .map(str::to_owned);
        let parsed = declared(&args).unwrap();
        assert_eq!(parsed.checkpoint_every, [16, 64]);

        let invalid = ["--checkpoint-in", "state"].map(str::to_owned);
        assert!(declared(&invalid).is_err());
        let resumable = [
            "--checkpoint-in",
            "state",
            "--population",
            "80",
            "--learn",
            "learn.hlsn",
            "--learn-from",
            "16",
        ]
        .map(str::to_owned);
        assert_eq!(declared(&resumable).unwrap().learn_from, 16);
        let bounded = [
            "--learn",
            "learn.hlsn",
            "--checkpoint-latest",
            "latest.state",
            "--wall-seconds",
            "3600",
        ]
        .map(str::to_owned);
        let parsed = declared(&bounded).unwrap();
        assert_eq!(parsed.wall_seconds, Some(3600));
        assert_eq!(parsed.checkpoint_latest.as_deref(), Some("latest.state"));
        assert!(declared(&["--wall-seconds", "0"].map(str::to_owned)).is_err());
        assert!(declared(&["--wall-seconds", "60"].map(str::to_owned)).is_err());
    }
}

pub(crate) fn sections_of(path: Option<&String>, count: Option<usize>) -> Result<Vec<Section>> {
    let Some(path) = path else {
        return Ok(Vec::new());
    };
    let mut sections = sections::read_frames(&read(path)?)?;
    if let Some(count) = count {
        sections.truncate(count);
    }
    Ok(sections)
}

fn declared_population(declared: Option<u64>, longest: usize, located: u64) -> Result<u64> {
    match declared {
        Some(population) if population < located => Err(format!(
            "declared --population {population} is below located n* {located}; it is not raised"
        )
        .into()),
        Some(population) => Ok(population),
        None => Ok(u64::try_from(longest)
            .map_err(|_| "the cut length does not fit u64")?
            .max(located)),
    }
}

pub fn run<P, Mount, Restore>(
    port: &P,
    args: &[String],
    mount_with: Mount,
    mount_continued: Restore,
) -> Result<()>
where
    P: ExecutionPort,
    P::Resident: ExposedResident,
    Mount: Fn(&Field, &Current, Constitution) -> std::result::Result<P::Resident, HnnError>,
    Restore: Fn(
        &Field,
        &Current,
        Constitution,
        &ContinuingState,
    ) -> std::result::Result<P::Resident, HnnError>,
{
    let options = options(args)?;
    let max_release_octets = options
        .max_release_octets
        .expect("validated run declaration");
    // Keep the whole learning frame for a stable field population across resumed suffix chunks.
    // `--learn-count` is the global exclusive end index; `--learn-from` is the global start.
    let learn = sections_of(options.learn.as_ref(), None)?;
    let learn_end = options.learn_count.unwrap_or(learn.len());
    let release = sections_of(options.release.as_ref(), options.release_count)?;
    if release.iter().any(|section| !section.target.is_empty()) {
        return Err("question-only release sections must have empty targets".into());
    }
    let reads = sections_of(
        options.read.as_ref(),
        options.read_count.map(|count| count + options.read_from),
    )?
    .into_iter()
    .skip(options.read_from)
    .collect::<Vec<_>>();
    let mut keys = match &options.keys {
        Some(path) => Some(KeyStream::new(read(path)?, RELEASE_KEY_BYTES)?),
        None => None,
    };
    if !release.is_empty() && keys.is_none() {
        return Err("a release needs --keys, the declared exterior key stream".into());
    }
    let mut longest = 0usize;
    for (index, section) in learn.iter().chain(&release).chain(&reads).enumerate() {
        let cells = section.source_cells(index)?.len() + section.target_cells(index)?.len();
        longest = longest.max(cells);
    }
    let located = holonics::hnn::moment::capacity_located(
        &PERIODS,
        &vec![holonics::hnn::RingAdvance::Lock; PERIODS.len()],
        &[0],
        CLASSES,
        &OFFSETS,
    )?
    .n_star();
    if learn_end > learn.len() {
        return Err(format!(
            "--learn-count {learn_end} exceeds the available {} learning sections",
            learn.len()
        )
        .into());
    }
    if options.learn_from > learn_end {
        return Err(format!(
            "--learn-from {} is after the requested training endpoint {learn_end}",
            options.learn_from,
        )
        .into());
    }
    if options
        .checkpoint_every
        .iter()
        .any(|&count| count <= options.learn_from || count > learn_end)
    {
        return Err(format!(
            "checkpoint counts must lie in the current global training interval ({}, {learn_end}]",
            options.learn_from,
        )
        .into());
    }
    let population = declared_population(options.population, longest, located)?;
    let field = field(population)?;
    let pairing = PairingDeclaration::Family {
        table: (0..CLASSES).map(|c| (c, c ^ 1)).collect(),
    };
    let mut material =
        PairedCarrier::found(&field, Constitution::initial(&field, BUDGET)?, 0, &pairing)?.0;
    if options.arrival_context {
        for receiver in field.receivers() {
            material.bind_arrival_context_receiving(receiver.ring)?;
        }
    }
    for receiver in field.receivers() {
        println!(
            "receiving_configuration ring={} layout={:?} arrival_context={} finite_candidate_admission={}",
            receiver.ring,
            material.receiving_layout(receiver.ring),
            options.arrival_context,
            options.arrival_context,
        );
    }
    let observation = PairedObservation::admit(&field, &material, &pairing)?;
    let mut boundary = Boundary {
        pairing,
        observation,
    };
    let mut resident = if let Some(path) = &options.checkpoint_in {
        let text = String::from_utf8(read(path)?)?;
        let state = ContinuingState::from_text(&text, material.budget())?;
        if state.ring() != 0 || state.passage().is_none() {
            return Err("--checkpoint-in requires a full source-0 resident continuation".into());
        }
        let restored = material.clone().continued(&state)?;
        let resident =
            mount_continued(&field, &Current::at_rest(&field), material.clone(), &state)?;
        if resident.constitution() != &restored {
            return Err("continued mount did not reproduce the saved constitution".into());
        }
        println!(
            "checkpoint_input path={path:?} bytes={} kind=full_resident passage_included=true mount_continued=true learned_sections_before_resume={}",
            text.len(),
            options.learn_from,
        );
        resident
    } else {
        mount_with(&field, &Current::at_rest(&field), material.clone())?
    };
    println!(
        "listener chart=octet_digits places={PLACES} classes={CLASSES} end_letter={:?} rings={PERIODS:?} offsets={OFFSETS:?} exponent={EXPONENT} depth={DEPTH} sources=[0] receiver_ring=2 aperture=1 tolerance=1/{CLASSES} pairing=c^1 population={population} longest_section_cells={longest} located_n_star={located} learn_sections={} release_sections={} keys={} max_release_octets={}",
        sections::end_cells(),
        learn_end,
        release.len(),
        options.keys.as_deref().unwrap_or("none"),
        max_release_octets,
    );
    let mut stream = Stream::new();
    let mut factor_releases = FactorReleases::default();
    let mut run_code = CodeSum::default();
    let mut run_tree = DiagnosticCode::default();
    let mut run_cost = Cost::default();
    let run_started = Instant::now();
    let mut completed_sections = options.learn_from;
    let mut stop_reason = "requested_end";
    for index in options.learn_from..learn_end {
        let section = &learn[index];
        let started = Instant::now();
        let mut cost = Cost::default();
        let mut code = CodeSum::default();
        let baseline_before: Vec<(BigUint, BigUint)> = stream
            .baselines
            .iter()
            .map(|kt| (kt.numerator.clone(), kt.denominator.clone()))
            .collect();
        let source = section.source_cells(index)?;
        let target = section.target_cells(index)?;
        if target.is_empty() {
            return Err(format!("learning section {index} has no target").into());
        }
        boundary.current(&field, resident.constitution(), &mut cost)?;
        let encoded = boundary.observation.encode(&source)?;
        let mut moment = ingest(port, &mut resident, None, &encoded, &mut cost)?;
        for &class in &source {
            stream.count(class);
        }
        let mut features = Vec::new();
        let mut maximal_runs: BTreeMap<Vec<usize>, u64> = BTreeMap::new();
        let mut wave = CodeSum::default();
        let mut tree_code = DiagnosticCode::default();
        let mut flatness = Flatness::default();
        for (j, &class) in target.iter().enumerate() {
            let cell_started = Instant::now();
            let phases = resident
                .admitted()
                .first()
                .ok_or("no admitted receiver")?
                .clone();
            let refine_started = Instant::now();
            let (pending, refined) = port.refine(&mut resident, &moment, &phases)?;
            let refine_ns = elapsed(refine_started);
            cost.refine += refine_ns;
            let faces = refined
                .forward
                .present()
                .ok_or("refinement returned no face")?;
            let [face] = faces.faces.as_slice() else {
                return Err(
                    format!("expected one receiving phase, got {}", faces.faces.len()).into(),
                );
            };
            if face.cells().len() != CLASSES {
                return Err(
                    format!("expected {CLASSES} class cells, got {}", face.cells().len()).into(),
                );
            }
            let wave_code = face.code_length(class)?;
            wave.add(&wave_code);
            let (wave_cells, wave_fibres) = face_spread(face);
            flatness.add((wave_cells, wave_fibres));
            let (committed, maximal, _) =
                committed_classes(port, &mut resident, &pending, &mut cost)?;
            *maximal_runs.entry(maximal.clone()).or_default() += 1;
            let kt = stream.code(class);
            let target_cell = boundary.observation.encode(&[class])?;
            let compare_started = Instant::now();
            let (staged, compared) = port.compare(&mut resident, pending, &target_cell)?;
            let compare_ns = elapsed(compare_started);
            cost.compare += compare_ns;
            let (sealed, tree) = scored_code(&compared.receipt.detail)?;
            code.add(&sealed);
            tree_code.add(tree.as_ref());
            features.extend(
                compared
                    .deposit
                    .present()
                    .map(|deposit| receiving_features(deposit, phases.ring()))
                    .ok_or("compare returned no staged deposit")?,
            );
            let deposit_started = Instant::now();
            let deposited = port.deposit(&mut resident, staged)?;
            let deposit_ns = elapsed(deposit_started);
            let stepped = deposited
                .deposit
                .present()
                .map(stepped_families)
                .unwrap_or_default();
            let prior = deposited
                .deposit
                .present()
                .map(prior_move)
                .unwrap_or_default();
            if let Some(reading) = deposited.deposit.present() {
                factor_releases.add(reading, resident.constitution())?;
            }
            cost.deposit += deposit_ns;
            boundary.current(&field, resident.constitution(), &mut cost)?;
            let next = boundary.observation.encode(&[class])?;
            moment = ingest(port, &mut resident, Some(moment), &next, &mut cost)?;
            stream.count(class);
            println!(
                "cell section={index} j={j} class={class} sealed=[{},{}] tree={} wave=[{},{}] commit={committed} kt0={}/{} kt2={}/{} kt4={}/{} refine_ns={refine_ns} compare_ns={compare_ns} deposit_ns={deposit_ns} cell_ns={} steps={stepped} prior={prior} wave_cells={wave_cells} wave_fibres={wave_fibres}",
                sealed.lower,
                sealed.upper,
                tree.as_ref()
                    .map_or_else(|| "unavailable".to_owned(), enclosure),
                wave_code.lower,
                wave_code.upper,
                kt[0].0,
                kt[0].1,
                kt[1].0,
                kt[1].1,
                kt[2].0,
                kt[2].1,
                elapsed(cell_started),
            );
        }
        port.discard(&mut resident, Handle::Moment(moment))?;
        let precision_started = Instant::now();
        let phases = resident
            .admitted()
            .first()
            .ok_or("no admitted receiver for the precision event")?
            .clone();
        let precision = resident.constitution().receiving_precision_event(
            phases.ring(),
            &features,
            phases.tolerance(),
        )?;
        let storage_before_publication = resident.publication_storage_bits()?;
        let precision_applied = match precision {
            Some(event) => match resident.publish_receiving_precision(&event) {
                Ok(()) => "applied".to_string(),
                Err(HnnError::ConstitutionBudget { bits, budget, .. }) => {
                    format!("refused_budget(bits={bits},budget={budget})")
                }
                Err(error) => return Err(error.into()),
            },
            None => "none".to_string(),
        };
        cost.precision += elapsed(precision_started);
        let storage_after_publication = resident.publication_storage_bits()?;
        // The arrived operand remains resident after publication; no duplicate receiver is held.
        let retained_arrived = if precision_applied == "applied" {
            storage_after_publication.arrived
        } else {
            0
        };
        println!(
            "publication_storage section={index} retained_arrived_bits={} arrived_bits={} executed_chart_bits_before={} executed_chart_bits_after={}",
            retained_arrived,
            storage_after_publication.arrived,
            storage_before_publication.charts,
            storage_after_publication.charts,
        );
        let section_baselines = stream
            .baselines
            .iter()
            .zip(&baseline_before)
            .map(|(kt, (numerator, denominator))| {
                let n = &kt.numerator / numerator;
                let d = &kt.denominator / denominator;
                let difference = d.bits() as i128 - n.bits() as i128;
                format!("kt{}=[{},{}]", kt.order, difference - 1, difference + 1)
            })
            .collect::<Vec<_>>()
            .join(" ");
        let by_locus = resident
            .constitution()
            .carrier_bits_by_locus()
            .into_iter()
            .filter(|(_, parts)| parts.total() > 0)
            .map(|(locus, parts)| {
                format!(
                    "{locus:?}:{}+{}+{}",
                    parts.entries, parts.remainders, parts.solved
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        println!(
            "section index={index} source_cells={} target_cells={} sealed_bits={} tree_bits={} wave_bits={} {} {} {section_baselines} committed_classes={maximal_runs:?} precision_event={precision_applied} commit={} exact_constitution_bits={} bits_by_locus=[{by_locus}] factor_release={} resident_state_bits={} elapsed_ns={} {}",
            source.len(),
            target.len(),
            code.bits(),
            tree_code.bits(),
            wave.bits(),
            flatness.line(),
            population_line(resident.constitution(), phases.ring()),
            resident.constitution().commit(),
            resident.constitution().exact_bits(),
            factor_releases.line(),
            resident.state_bits(),
            elapsed(started),
            cost.line(),
        );
        if options.checkpoint_every.binary_search(&(index + 1)).is_ok() {
            let directory = options
                .checkpoint_dir
                .as_deref()
                .ok_or("checkpoint directory disappeared after option validation")?;
            save_checkpoint(
                &resident,
                &material,
                field.sources()[0],
                directory,
                index + 1,
            )?;
        }
        run_code.merge(&code);
        run_tree.merge(&tree_code);
        run_cost.merge(&cost);
        completed_sections = index + 1;
        if let Some(path) = options.checkpoint_latest.as_deref() {
            save_latest_checkpoint(
                &resident,
                &material,
                field.sources()[0],
                path,
                completed_sections,
            )?;
        }
        if options
            .wall_seconds
            .is_some_and(|seconds| run_started.elapsed().as_secs() >= seconds)
        {
            stop_reason = "wall_budget_boundary";
            break;
        }
    }
    println!(
        "train_progress completed_sections={completed_sections} requested_end={learn_end} total_sections={} stop_reason={stop_reason} elapsed_wall_ns={}",
        learn.len(),
        elapsed(run_started),
    );
    if options.learn_from < learn_end {
        let cells = u128::from(run_code.cells.max(1));
        let learning = run_cost.refine + run_cost.compare + run_cost.deposit;
        println!(
            "learned sections={} target_cells={} sealed_bits={} tree_bits={} {} {} learning_ns_per_target_cell={} rem {} wall_ns={} {}",
            completed_sections - options.learn_from,
            run_code.cells,
            run_code.bits(),
            run_tree.bits(),
            resident.admitted().first().map_or_else(
                || "population=unavailable".to_owned(),
                |phase| population_line(resident.constitution(), phase.ring())
            ),
            stream.bits(),
            learning / cells,
            learning % cells,
            elapsed(run_started),
            run_cost.line(),
        );
    }
    // Teacher-forced read: compare stages the target only to read its receipt, then the staged
    // deposit is discarded. No target deposit is applied; the passage still ingests each target.
    // The diagnostics observe those existing receipts and add no native operation.
    for (index, section) in reads.iter().enumerate() {
        let started = Instant::now();
        let mut cost = Cost::default();
        let mut code = CodeSum::default();
        let mut phase_bits = [CodeSum::default(), CodeSum::default()];
        let source = section.source_cells(index)?;
        let target = section.target_cells(index)?;
        boundary.current(&field, resident.constitution(), &mut cost)?;
        let encoded = boundary.observation.encode(&source)?;
        let mut moment = ingest(port, &mut resident, None, &encoded, &mut cost)?;
        let mut frozen = stream.frozen();
        for &class in &source {
            frozen.advance(class);
        }
        let mut single_hits = 0u64;
        let mut wave = CodeSum::default();
        let mut tree_code = DiagnosticCode::default();
        let mut flatness = Flatness::default();
        let mut kinds: BTreeMap<&'static str, KindRead> = BTreeMap::new();
        for (j, &class) in target.iter().enumerate() {
            let phases = resident
                .admitted()
                .first()
                .ok_or("no admitted receiver")?
                .clone();
            let refine_started = Instant::now();
            let (pending, refined) = port.refine(&mut resident, &moment, &phases)?;
            cost.refine += elapsed(refine_started);
            let faces = refined
                .forward
                .present()
                .ok_or("refinement returned no face")?;
            let [face] = faces.faces.as_slice() else {
                return Err(
                    format!("expected one receiving phase, got {}", faces.faces.len()).into(),
                );
            };
            let wave_code = face.code_length(class)?;
            wave.add(&wave_code);
            let (wave_cells, wave_fibres) = face_spread(face);
            flatness.add((wave_cells, wave_fibres));
            let (committed, maximal, certified) =
                committed_classes(port, &mut resident, &pending, &mut cost)?;
            let kind = octet_kind(&section.target, j);
            let read = kinds.entry(kind).or_default();
            match (certified, maximal.as_slice()) {
                (true, [single]) if *single == class => read.right += 1,
                (true, _) => read.wrong += 1,
                (false, _) => read.hold += 1,
            }
            if maximal == [class] {
                single_hits += 1;
            }
            let target_cell = boundary.observation.encode(&[class])?;
            let compare_started = Instant::now();
            let (staged, compared) = port.compare(&mut resident, pending, &target_cell)?;
            cost.compare += elapsed(compare_started);
            let (sealed, tree) = scored_code(&compared.receipt.detail)?;
            code.add(&sealed);
            tree_code.add(tree.as_ref());
            phase_bits[j % 2].add(&sealed);
            let read = kinds.entry(kind).or_default();
            read.sealed.add(&sealed);
            read.tree.add(tree.as_ref());
            println!(
                "read_cell section={index} j={j} class={class} kind={kind} sealed=[{},{}] tree={} wave=[{},{}] commit={committed} wave_cells={wave_cells} wave_fibres={wave_fibres}",
                sealed.lower,
                sealed.upper,
                tree.as_ref()
                    .map_or_else(|| "unavailable".to_owned(), enclosure),
                wave_code.lower,
                wave_code.upper,
            );
            frozen.code(class);
            frozen.advance(class);
            port.discard(&mut resident, Handle::Staged(staged))?;
            let next = boundary.observation.encode(&[class])?;
            moment = ingest(port, &mut resident, Some(moment), &next, &mut cost)?;
        }
        port.discard(&mut resident, Handle::Moment(moment))?;
        println!(
            "read section={index} source_cells={} target_cells={} sealed_bits={} tree_bits={} wave_bits={} {} frozen_{} quotient_bits={} remainder_bits={} single_committed_hits={single_hits} elapsed_ns={} {}",
            source.len(),
            target.len(),
            code.bits(),
            tree_code.bits(),
            wave.bits(),
            flatness.line(),
            frozen.bits().replace(" kt", " frozen_kt"),
            phase_bits[0].bits(),
            phase_bits[1].bits(),
            elapsed(started),
            cost.line(),
        );
        for (kind, read) in &kinds {
            println!(
                "read_kind section={index} kind={kind} cells={} sealed_bits={} tree_bits={} certified_right={} certified_wrong={} hold={}",
                read.sealed.cells,
                read.sealed.bits(),
                read.tree.bits(),
                read.right,
                read.wrong,
                read.hold,
            );
        }
    }
    for (index, section) in release.iter().enumerate() {
        let started = Instant::now();
        let mut cost = Cost::default();
        let keys = keys.as_mut().ok_or("a release needs keys")?;
        let source = section.source_cells(index)?;
        boundary.current(&field, resident.constitution(), &mut cost)?;
        let encoded = boundary.observation.encode(&source)?;
        let mut moment = ingest(port, &mut resident, None, &encoded, &mut cost)?;
        let mut released: Vec<usize> = Vec::new();
        let mut release_code = DiagnosticCode::default();
        let mut stop = "maximum";
        while released.len() < 2 * max_release_octets {
            let phases = resident
                .admitted()
                .first()
                .ok_or("no admitted receiver")?
                .clone();
            let refine_started = Instant::now();
            let (pending, _) = port.refine(&mut resident, &moment, &phases)?;
            cost.refine += elapsed(refine_started);
            let cells_started = Instant::now();
            let committed = port
                .release_cells(&mut resident, &pending, CellLaw::Commit)?
                .forward
                .into_present()
                .ok_or("the commit returned no cells")?;
            let drawn = port
                .release_cells(&mut resident, &pending, CellLaw::Draw(keys))?
                .forward
                .into_present()
                .ok_or("the draw returned no cells")?;
            cost.release_cells += elapsed(cells_started);
            port.discard(&mut resident, Handle::Pending(pending))?;
            let commit_arm = committed.cells.first().map_or("none".into(), arm);
            let draw_cell = drawn.cells.first().ok_or("the draw decided no cell")?;
            let draw_face = draw_cell
                .face
                .iter()
                .map(|interval| format!("[{},{}]", interval.lower, interval.upper))
                .collect::<Vec<_>>()
                .join(",");
            println!(
                "release section={index} j={} commit={commit_arm} draw={} reading_bits={} face=[{draw_face}]",
                released.len(),
                arm(draw_cell),
                draw_cell.bits,
            );
            let Some(class) = draw_cell.class() else {
                stop = "held";
                break;
            };
            release_code.add(drawn_code(draw_cell, class).ok().as_ref());
            released.push(class);
            let next = boundary.observation.encode(&[class])?;
            moment = ingest(port, &mut resident, Some(moment), &next, &mut cost)?;
            if sections::closes(&released) {
                stop = "end_letter";
                break;
            }
        }
        port.discard(&mut resident, Handle::Moment(moment))?;
        let pieces = sections::pieces_of(&released);
        let body = match pieces.split_last() {
            Some((&Piece::End, body)) if stop == "end_letter" => body,
            _ => pieces.as_slice(),
        };
        let slips = pieces
            .iter()
            .filter(|piece| matches!(piece, Piece::Slip(_)))
            .count();
        println!(
            "released section={index} cells={} octets={} slips={slips} stop={stop} release_code_bits={} keys_read={} elapsed_ns={} {}",
            released.len(),
            pieces.len() - slips,
            release_code.bits(),
            keys.keys_read(),
            elapsed(started),
            cost.line(),
        );
        println!(
            "released_text section={index} begin\n{}\nreleased_text section={index} end",
            shown(body)
        );
    }
    Ok(())
}
