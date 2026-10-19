//! Shared host/CUDA MNIST observed runner. This is an exterior example boundary: its IDX and
//! label codec is authored, and no spatial invariance or learned-image claim follows from it.

use std::{error::Error, time::Instant};

use holonics::geometry::spatial::idx::{Images, Labels};
use holonics::geometry::spatial::{PlacedRaster, Raster, SpatialPassage};
use holonics::geometry::{RatVec3, screw::ScrewGenerator};
use holonics::hnn::constitution::{Constitution, ContinuingState, LinearLocus, ReceivingLayout};
use holonics::hnn::encoding::observed::PairedObservation;
use holonics::hnn::field::{ContactDeclaration, Current, Field, FieldDeclaration, RingDeclaration};
use holonics::hnn::paired::{PairedCarrier, PairingDeclaration};
use holonics::hnn::port::{Deposit, Handle, MomentId, PendingId, ReceiptDetail};
use holonics::hnn::ratio::{Face, Faces};
use holonics::hnn::receiving::ObservationPartition;
use holonics::hnn::receiving::cells::{CellLaw, CellRelease};
use holonics::hnn::reference::ExposedResident;
use holonics::hnn::ring::modes::{
    ModeView,
    exploration::{ChoiceReason, ExplorationBudget, ModeExplorer},
};
use holonics::hnn::{ConstitutionRead, ExecutionPort, HnnError};
use holonics::ratio::algebraic::ExactInterval;
use holonics::ratio::{Rat, integer, rat};
use holonics::receiver::release::{
    BeyondTolerance, DecisionRule, KeyStream, ReleaseReturn, WithinTolerance,
};

#[path = "cost.rs"]
mod cost;
#[path = "diagnostics.rs"]
mod diagnostics;

pub const BUDGET: u64 = 1u64 << 40; // native exact-bit address budget, not a RAM/runtime limit
const MNIST_ALPHABET: usize = 16; // the declared class aperture, including OOD symbols 10..15
/// [agent-inferred, October 16] The bytes of one declared release key: `2^256` cells of the unit
/// interval, the width the October 15 release redesign reads its exterior keys at.
const RELEASE_KEY_BYTES: usize = 32;
type Result<T> = std::result::Result<T, Box<dyn Error>>;

#[allow(
    clippy::disallowed_methods,
    reason = "IDX is read only by this exterior example boundary"
)]
fn read(path: &str) -> Result<Vec<u8>> {
    Ok(std::fs::read(path)?)
}

#[allow(
    clippy::disallowed_methods,
    reason = "constitution checkpoint persistence is exterior example I/O"
)]
fn write_checkpoint_file(path: &str, bytes: &[u8]) -> Result<()> {
    Ok(std::fs::write(path, bytes)?)
}

#[allow(
    clippy::disallowed_methods,
    reason = "constitution checkpoint verification is exterior example I/O"
)]
fn read_checkpoint_file(path: &str) -> Result<Vec<u8>> {
    Ok(std::fs::read(path)?)
}

/// Load only a constitution checkpoint of this exact declared layout.
fn load_evaluation_material(field: &Field, path: &str, opening: &Constitution) -> Result<Constitution> {
    let bytes = read_checkpoint_file(path)?;
    let original = std::str::from_utf8(&bytes)?;
    let state = ContinuingState::from_text(original)?;
    let material = opening.clone().continued_on(field, &state)?;
    println!(
        "checkpoint_input path={path:?} bytes={} training_updates=0 constitution_only=true current_at_rest=true carry_fresh=true address_fresh=true selector_fresh=true",
        bytes.len()
    );
    Ok(material)
}

fn field(
    periods: [u64; 3],
    offsets: Vec<usize>,
    exponent: i64,
    depth: usize,
    sources: &[usize],
    population: u64,
) -> Result<Field> {
    let mut declared = FieldDeclaration::campaign_one(population);
    let axis = ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero());
    declared.rings = periods
        .iter()
        .enumerate()
        .map(|(g, &period)| RingDeclaration {
            period,
            screw: axis.clone(),
            placements: (0..period)
                .map(|n| FieldDeclaration::quarter_turn(n, period))
                .collect(),
            lock: if sources.contains(&g) {
                (0..MNIST_ALPHABET).map(|symbol| symbol as u64).collect()
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
    // In placed/two-source mode both spatial axes need a one-hop relation to the receiver.
    // Keep the serial single-source reproducer's original chain and its temporal semantics.
    let contact_ends = if sources == [0, 1] {
        [(0, 2), (1, 2)]
    } else {
        [(0, 1), (1, 2)]
    };
    declared.contacts = contact_ends
        .iter()
        .map(|&(from, to)| ContactDeclaration {
            from,
            to,
            channel: (0..periods[from].min(periods[to]) as usize)
                .map(|node| (node, node))
                .collect(),
            admittance: integer(2),
            exponent: integer(exponent),
        })
        .collect();
    declared.sources = sources.to_vec();
    declared.loops.clear();
    declared.alphabet = MNIST_ALPHABET;
    declared.offsets = offsets;
    declared.receivers[0].ring = 2;
    declared.receivers[0].aperture = 1;
    declared.receivers[0].depth = depth;
    declared.receivers[0].tolerance = rat(1, 16);
    declared.lattice.clear();
    Ok(Field::declare(declared.by_lattice_rule())?)
}

fn parse_mode_view(field: &Field, spec: &str) -> Result<ModeView> {
    let selections = spec
        .split(',')
        .map(|part| {
            let (source, period) = part
                .split_once(':')
                .ok_or("mode view entries use SOURCE:PERIOD")?;
            Ok::<_, Box<dyn Error>>((source.parse::<usize>()?, period.parse::<u64>()?))
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(ModeView::from_periods(field, &selections)?)
}

/// Retain an in-memory selector checkpoint and bounded last-only audit at an image boundary.
/// The format is intentionally not written to disk; the separate resident checkpoint remains
/// constitution-only and cannot resume this adaptive policy on its own.
fn report_mode_explorer_checkpoint(
    explorer: &ModeExplorer,
    budget: &ExplorationBudget,
    field: &Field,
    role: &str,
    phase: &str,
) -> Result<()> {
    let _checkpoint = explorer.checkpoint()?;
    let history = explorer
        .history()
        .iter()
        .enumerate()
        .map(|(index, item)| {
            (
                index,
                item.attempted,
                item.completed,
                item.failed,
                item.last.as_ref().map(|feedback| {
                    (
                        feedback.context.commit,
                        feedback.context.lift.clone(),
                        feedback.context.receiver,
                        feedback.word_ticks,
                        feedback.selected_source_bits,
                        feedback.reached_logits.iter().map(Vec::len).sum::<usize>(),
                    )
                }),
            )
        })
        .collect::<Vec<_>>();
    let storage = explorer.policy_storage();
    println!(
        "mode_explorer_checkpoint role={role} phase={phase} budget={budget:?} spent={:?} menu={:?} history_attempts_completed_failed_last_context_commit_lift_receiver_ticks_selected_source_bits_reached_logit_count={history:?} policy_storage={storage:?} typed_in_memory_checkpoint_created=true adaptive_state_disk_resumable=false",
        explorer.spent(),
        explorer.menu(),
    );
    for (menu_index, (view, item)) in explorer.menu().iter().zip(explorer.history()).enumerate() {
        if item.attempted == 0 {
            continue;
        }
        report_mode_projector_storage(field, role, phase, menu_index, view)?;
    }
    Ok(())
}

/// Report a view's compiled exact projector only after that view has actually been used.
/// The byte figures are container/gather payload estimates, not allocator RSS or GPU memory.
fn report_mode_projector_storage(
    field: &Field,
    role: &str,
    phase: &str,
    menu_index: usize,
    view: &ModeView,
) -> Result<()> {
    if view.is_whole() {
        println!(
            "mode_projector_storage role={role} phase={phase} menu_index={menu_index} semantic_view_bits={} whole=true compiled_operator_count=0 sparse_terms=0 coefficient_rational_bits=0 gather_entries=0 gather_length_bytes=0 gather_capacity_bytes=0 term_descriptor_length_bytes=0 term_descriptor_capacity_bytes=0 compiled=false accounting=not_applicable_whole_view",
            view.bits(),
        );
        return Ok(());
    }
    let storage = view.compiled_storage(field)?;
    println!(
        "mode_projector_storage role={role} phase={phase} menu_index={menu_index} semantic_view_bits={} whole=false compiled_operator_count={} sparse_terms={} coefficient_rational_bits={} gather_entries={} gather_length_bytes={} gather_capacity_bytes={} term_descriptor_length_bytes={} term_descriptor_capacity_bytes={} compiled=true accounting=reported_gather_and_descriptor_payload_excludes_bigint_allocator_limbs_rss_and_device_bytes",
        view.bits(),
        storage.operators,
        storage.terms,
        storage.coefficient_rational_bits,
        storage.gather_entries,
        storage.gather_length_bytes,
        storage.gather_capacity_bytes,
        storage.term_descriptor_length_bytes,
        storage.term_descriptor_capacity_bytes,
    );
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum InputChart {
    /// The existing coordinate-bearing serial pixel codec, retained as the default reproducer.
    Serial,
    /// Two nibble occurrences at each explicit (x=column, y=row) source-ring phase prefix.
    Placed,
}

impl InputChart {
    fn digits_per_image(self) -> usize {
        match self {
            Self::Serial => 4_704,
            Self::Placed => 1_568,
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::Serial => "coordinate-bearing-serial",
            Self::Placed => "occurrence-placed_xy_nibbles",
        }
    }

    fn default_periods(self) -> &'static str {
        match self {
            Self::Serial => "17,7,11",
            Self::Placed => "28,28,11",
        }
    }

    fn default_offsets(self) -> &'static str {
        match self {
            Self::Serial => "1,6,168",
            // Stream steps: paired nibbles (1), horizontal pixel (2), and diagonal/vertical
            // neighbors (2*(28−1), 2*28, 2*(28+1)); these retain both axes' local relations.
            Self::Placed => "1,2,54,56,58",
        }
    }

    fn source_rings(self) -> &'static [usize] {
        match self {
            Self::Serial => &[0],
            Self::Placed => &[0, 1],
        }
    }
}

/// A decision is emitted only when one class is the exact maximum of the face mass. Ties retain
/// every maximum; the code-length intervals remain a separate exact-enclosure report.
#[derive(Clone, Debug, PartialEq, Eq)]
enum ClassChoice {
    Unique { class: usize },
    Ambiguous { classes: Vec<usize> },
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ClassScores {
    /// Every class's exact code-length enclosure, in authored class order.
    code_lengths: Vec<ExactInterval>,
    choice: ClassChoice,
}

fn class_scores(face: &Face) -> std::result::Result<ClassScores, HnnError> {
    // The common normalizer is canceled by the native exact comparator. Keep the enclosures for
    // reporting, but don't use overlapping log-normalizer intervals to decide a winner.
    let code_lengths = face.code_lengths()?;
    let maximal = face.maximal_mass_classes();
    let choice = if let [class] = maximal.as_slice() {
        ClassChoice::Unique { class: *class }
    } else {
        ClassChoice::Ambiguous { classes: maximal }
    };
    Ok(ClassScores {
        code_lengths,
        choice,
    })
}

impl ClassScores {
    fn digit(&self, boundary: &PairedObservation) -> Option<usize> {
        let ClassChoice::Unique { class } = &self.choice else {
            return None;
        };
        boundary.symbol(*class).filter(|&symbol| symbol < 10)
    }

    fn description(&self, boundary: &PairedObservation) -> String {
        match &self.choice {
            ClassChoice::Unique { class } => match boundary.symbol(*class) {
                Some(symbol) if symbol < 10 => {
                    format!("unique_maximal_mass_digit(class={class},symbol={symbol})")
                }
                Some(symbol) => {
                    format!("unique_maximal_mass_out_of_domain(class={class},symbol={symbol})")
                }
                None => format!("unique_maximal_mass_unmapped_class(class={class})"),
            },
            ClassChoice::Ambiguous { classes } => {
                format!("ambiguous_maximal_mass_classes={classes:?}")
            }
        }
    }
}

#[derive(Debug)]
struct ObservationRead {
    moment: MomentId,
    pending: PendingId,
    faces: Faces,
    pre_release: ClassScores,
    /// Present only when the receiver's declared release law actually releases the face.
    released: Option<ClassScores>,
    /// The release at class grain on the receiver's scored face (`hnn::receiving::cells`), when
    /// the role reads it.
    cells: Option<CellsRead>,
}

/// [agent-inferred, October 16] **The release at class grain of one image**
/// (`hnn::receiving::cells`): the commit of a unique answer on the receiver's scored face, and,
/// when release keys are declared, the draw by the next declared key. Both are decided by the
/// one decision law at tolerance zero and read nothing the comparison has not read.
#[derive(Debug)]
struct CellsRead {
    commit: CellRelease,
    drawn: Option<CellRelease>,
    elapsed_ns: u128,
}

/// Which releases at class grain a role reads: none (training, whose comparison is the target's),
/// or the commit and, with declared keys, the draw (the held-out roles).
enum ClassGrain<'k> {
    Off,
    Read(Option<&'k mut KeyStream>),
}

impl CellsRead {
    /// The class an arm released, as its digit at the boundary.
    fn digit(release: &CellRelease, boundary: &PairedObservation) -> Option<usize> {
        let [class] = release.classes()?[..] else {
            return None;
        };
        boundary.symbol(class).filter(|&symbol| symbol < 10)
    }

    /// One exact report line per arm: its decision, class, digit, the reading bits that decided
    /// it and the scored face it was decided on (every class's enclosure, exact endpoints); the
    /// draw adds its key and its certified cell.
    fn report(&self, role: &str, image: usize, label: usize, boundary: &PairedObservation) {
        let arms = std::iter::once(("commit", &self.commit))
            .chain(self.drawn.as_ref().map(|drawn| ("draw", drawn)));
        for (arm, release) in arms {
            for cell in &release.cells {
                let decision = match &cell.release {
                    ReleaseReturn::Released { .. } => "released".to_string(),
                    ReleaseReturn::Drawn(draw) => format!(
                        "drawn certified_cell=[{},{})",
                        draw.prior_upper, draw.through_lower
                    ),
                    ReleaseReturn::Hold => "hold".to_string(),
                    ReleaseReturn::Unresolved(_) => "unresolved".to_string(),
                    ReleaseReturn::NoContinuationBridges { .. } => {
                        "no_key_declared_hold".to_string()
                    }
                    other => format!("{other:?}"),
                };
                let symbol = cell
                    .class()
                    .and_then(|class| boundary.symbol(class))
                    .map_or("none".to_string(), |symbol| symbol.to_string());
                let key = cell
                    .key
                    .as_ref()
                    .map_or("none".to_string(), |(index, key)| format!("{index}:{key}"));
                let face = cell
                    .face
                    .iter()
                    .map(|interval| format!("[{},{}]", interval.lower, interval.upper))
                    .collect::<Vec<_>>()
                    .join(",");
                println!(
                    "held_out_class_grain role={role} image={image} true_label={label} arm={arm} phase={} decision={decision} classes={:?} symbol={symbol} key={key} reading_bits={} scored_face=[{face}] elapsed_ns={}",
                    cell.phase, cell.classes, cell.bits, self.elapsed_ns,
                );
            }
            if let Some(mass) = release.certified_mass() {
                println!(
                    "held_out_class_grain_mass role={role} image={image} arm={arm} certified_mass={mass}"
                );
            }
        }
    }
}

/// The exact current receiver operands from this comparison. Only each linear sample's feature
/// is returned; covectors, target masses/classes, and labels are deliberately excluded.
fn receiving_features(deposit: &Deposit, ring: usize) -> Vec<Vec<Rat>> {
    deposit
        .linear()
        .iter()
        .filter(|step| step.locus == LinearLocus::Receiving(ring))
        .flat_map(|step| step.samples.iter().map(|sample| sample.feature.clone()))
        .collect()
}

fn split_receiver_reads(reads: &[Vec<Rat>]) -> (Vec<Vec<Rat>>, Vec<Vec<Rat>>) {
    let real_logits = reads
        .iter()
        .map(|read| read.iter().step_by(2).cloned().collect())
        .collect();
    let phase_turns = reads
        .iter()
        .map(|read| {
            read.iter()
                .skip(1)
                .step_by(2)
                .map(|value| value / integer(2))
                .collect()
        })
        .collect();
    (real_logits, phase_turns)
}

/// Exterior-only elapsed-time readings. Each operation's exact `u128` nanosecond count is kept
/// as reported by `Instant`; the nested ingestion timings separate native ingest calls from the
/// carry-closing calls that occur between them.
#[derive(Clone, Copy, Debug, Default)]
struct StageTimes {
    boundary_admission_ns: Option<u128>,
    encode_ns: Option<u128>,
    ingest_ns: Option<u128>,
    ingest_wall_ns: Option<u128>,
    ingest_calls: usize,
    close_aeon_ns: Option<u128>,
    mode_selection_ns: Option<u128>,
    continued_view_probe_ns: Option<u128>,
    refine_ns: Option<u128>,
    pre_release_decode_ns: Option<u128>,
    release_ns: Option<u128>,
    released_decode_ns: Option<u128>,
    target_encode_ns: Option<u128>,
    compare_ns: Option<u128>,
    deposit_ns: Option<u128>,
    post_deposit_reread_ns: Option<u128>,
    receiving_precision_event_ns: Option<u128>,
    receiving_precision_check_ns: Option<u128>,
    receiving_precision_publish_ns: Option<u128>,
    close_aeon_calls: usize,
}

struct PredictionTiming {
    stages: StageTimes,
    current_rings: usize,
    input_symbols: usize,
    cost: cost::CostLedger,
}

#[derive(Clone, Copy)]
struct StageProgress {
    role: &'static str,
    image: usize,
    enabled: bool,
}

impl StageProgress {
    fn begin(self, stage: &str) {
        if self.enabled {
            println!(
                "progress role={} image={} stage={} status=start",
                self.role, self.image, stage
            );
        }
    }

    fn done(self, stage: &str, elapsed_ns: u128) {
        if self.enabled {
            println!(
                "progress role={} image={} stage={} status=complete elapsed_ns={elapsed_ns}",
                self.role, self.image, stage
            );
        }
    }

    fn ingest_chunk_begin(self, chunk: usize, start: usize, end: usize) {
        if self.enabled {
            println!(
                "progress role={} image={} stage=ingest_chunk chunk={} range={}..{} status=start",
                self.role, self.image, chunk, start, end
            );
        }
    }

    fn ingest_chunk_done(
        self,
        chunk: usize,
        start: usize,
        end: usize,
        elapsed_ns: u128,
        cells: usize,
        carry_out: bool,
    ) {
        if self.enabled {
            println!(
                "progress role={} image={} stage=ingest_chunk chunk={} range={}..{} status=complete elapsed_ns={} consumed_cells={} carry_out={}",
                self.role, self.image, chunk, start, end, elapsed_ns, cells, carry_out
            );
        }
    }
}

#[derive(Default)]
struct StageTotal {
    calls: usize,
    elapsed_ns: u128,
}

impl StageTotal {
    fn add(&mut self, elapsed_ns: Option<u128>, calls: usize) {
        if let Some(elapsed_ns) = elapsed_ns {
            self.calls += calls;
            self.elapsed_ns = self
                .elapsed_ns
                .checked_add(elapsed_ns)
                .expect("aggregate elapsed nanoseconds overflowed u128");
        }
    }
}

#[derive(Default)]
struct TimingTotals {
    samples: usize,
    boundary_admission: StageTotal,
    encode: StageTotal,
    ingest: StageTotal,
    ingest_wall: StageTotal,
    close_aeon: StageTotal,
    mode_selection: StageTotal,
    continued_view_probe: StageTotal,
    refine: StageTotal,
    pre_release_decode: StageTotal,
    release: StageTotal,
    released_decode: StageTotal,
    target_encode: StageTotal,
    compare: StageTotal,
    deposit: StageTotal,
    post_deposit_reread: StageTotal,
    receiving_precision_event: StageTotal,
    receiving_precision_check: StageTotal,
    receiving_precision_publish: StageTotal,
}

impl TimingTotals {
    fn record(&mut self, stages: &StageTimes) {
        self.samples += 1;
        self.boundary_admission.add(stages.boundary_admission_ns, 1);
        self.encode.add(stages.encode_ns, 1);
        self.ingest.add(stages.ingest_ns, stages.ingest_calls);
        self.ingest_wall.add(stages.ingest_wall_ns, 1);
        self.close_aeon
            .add(stages.close_aeon_ns, stages.close_aeon_calls);
        self.mode_selection.add(stages.mode_selection_ns, 1);
        self.continued_view_probe
            .add(stages.continued_view_probe_ns, 1);
        self.refine.add(stages.refine_ns, 1);
        self.pre_release_decode.add(stages.pre_release_decode_ns, 1);
        self.release.add(stages.release_ns, 1);
        self.released_decode.add(stages.released_decode_ns, 1);
        self.target_encode.add(stages.target_encode_ns, 1);
        self.compare.add(stages.compare_ns, 1);
        self.deposit.add(stages.deposit_ns, 1);
        self.post_deposit_reread
            .add(stages.post_deposit_reread_ns, 1);
        self.receiving_precision_event
            .add(stages.receiving_precision_event_ns, 1);
        self.receiving_precision_check
            .add(stages.receiving_precision_check_ns, 1);
        self.receiving_precision_publish
            .add(stages.receiving_precision_publish_ns, 1);
    }

    fn summary(&self, role: &str) -> String {
        let stage = |name: &str, total: &StageTotal| {
            format!(
                "{name}_calls={} {name}_elapsed_ns={}",
                total.calls, total.elapsed_ns
            )
        };
        format!(
            "timing_total role={role} samples={} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {}",
            self.samples,
            stage("boundary_admission", &self.boundary_admission),
            stage("encode", &self.encode),
            stage("ingest", &self.ingest),
            stage("ingest_wall", &self.ingest_wall),
            stage("close_aeon", &self.close_aeon),
            stage("mode_selection", &self.mode_selection),
            stage("continued_view_probe", &self.continued_view_probe),
            stage("refine", &self.refine),
            stage("pre_release_decode", &self.pre_release_decode),
            stage("release", &self.release),
            stage("released_decode", &self.released_decode),
            stage("target_encode", &self.target_encode),
            stage("compare", &self.compare),
            stage("deposit", &self.deposit),
            stage("post_deposit_reread", &self.post_deposit_reread),
            stage("receiving_precision_event", &self.receiving_precision_event),
            stage("receiving_precision_check", &self.receiving_precision_check),
            stage(
                "receiving_precision_publish",
                &self.receiving_precision_publish
            ),
        )
    }
}

fn print_sample_timing(
    role: &'static str,
    image: usize,
    stages: &StageTimes,
    field: &Field,
    current_rings: usize,
    input_symbols: usize,
    periods: [u64; 3],
) {
    println!(
        "timing_sample role={role} image={image} input_symbols={input_symbols} field_rings={} field_contacts={} source_rings={:?} field_periods={periods:?} alphabet={} offsets={:?} current_rings={} boundary_admission_ns={:?} encode_ns={:?} ingest_ns={:?} ingest_wall_ns={:?} close_aeon_ns={:?} close_aeon_calls={} mode_selection_ns={:?} continued_view_probe_ns={:?} refine_ns={:?} pre_release_decode_ns={:?} release_ns={:?} released_decode_ns={:?} target_encode_ns={:?} compare_ns={:?} deposit_ns={:?} post_deposit_reread_ns={:?} receiving_precision_check_ns={:?} receiving_precision_publish_ns={:?} receiving_precision_event_total_ns={:?}",
        field.rings().len(),
        field.contacts().len(),
        field.sources(),
        field.alphabet(),
        field.offsets(),
        current_rings,
        stages.boundary_admission_ns,
        stages.encode_ns,
        stages.ingest_ns,
        stages.ingest_wall_ns,
        stages.close_aeon_ns,
        stages.close_aeon_calls,
        stages.mode_selection_ns,
        stages.continued_view_probe_ns,
        stages.refine_ns,
        stages.pre_release_decode_ns,
        stages.release_ns,
        stages.released_decode_ns,
        stages.target_encode_ns,
        stages.compare_ns,
        stages.deposit_ns,
        stages.post_deposit_reread_ns,
        stages.receiving_precision_check_ns,
        stages.receiving_precision_publish_ns,
        stages.receiving_precision_event_ns,
    );
}

impl ObservationRead {
    fn released_face(&self) -> bool {
        self.released.is_some()
    }
    fn raw_digit(&self, boundary: &PairedObservation) -> Option<usize> {
        self.pre_release.digit(boundary)
    }
    fn released_digit(&self, boundary: &PairedObservation) -> Option<usize> {
        self.released.as_ref()?.digit(boundary)
    }
}

/// No label enters the source encoder here. A raster becomes either the original authored serial
/// spatial passage or an occurrence-placed x/y nibble chart; the same admitted boundary and
/// receiver then process either encoding.
fn predict<P: ExecutionPort>(
    port: &P,
    resident: &mut P::Resident,
    field: &Field,
    chart: InputChart,
    periods: [u64; 3],
    mode_view: &ModeView,
    mut mode_explorer: Option<&mut ModeExplorer>,
    profile_proposals: bool,
    continued_view_probe: Option<(&Constitution, &[(&str, ModeView)], &[u64])>,
    boundary: &PairedObservation,
    raster: Raster,
    progress: StageProgress,
    class_grain: ClassGrain<'_>,
) -> Result<(ObservationRead, PredictionTiming)>
where
    P::Resident: ExposedResident,
{
    let mut cost = cost::CostLedger::default();
    let current_rings = resident.current().lift().len();
    progress.begin("encode");
    let encode_started = Instant::now();
    let encoded = match chart {
        InputChart::Serial => {
            let passage = SpatialPassage::encode(&raster);
            if passage.decode()? != raster {
                return Err("the serial spatial boundary failed exact recovery".into());
            }
            boundary.encode(passage.digits())?
        }
        InputChart::Placed => {
            let placed = PlacedRaster::encode(&raster, [periods[0], periods[1]])?;
            if placed.decode()? != raster {
                return Err("the placed spatial boundary failed exact recovery".into());
            }
            // Build one full placement from this observation's actual opening Current. Encoded
            // slices below retain absolute lifts, including carry, across every aeon close.
            boundary.encode_raster(field, resident.current(), &placed)?
        }
    };
    let encode_ns = encode_started.elapsed().as_nanos();
    progress.done("encode", encode_ns);
    let input_symbols = encoded.len();
    cost.encoded_passage(input_symbols, raster.samples().len(), field.alphabet());
    let mut at = 0;
    let mut moment = None;
    let mut ingest_ns = 0u128;
    let mut close_aeon_ns = 0u128;
    let mut close_aeon_calls = 0usize;
    let mut ingest_calls = 0usize;
    progress.begin("ingest");
    let ingest_wall_started = Instant::now();
    let mut chunk = 0usize;
    while at < encoded.len() {
        let part = encoded.part(at..encoded.len())?;
        progress.ingest_chunk_begin(chunk + 1, at, encoded.len());
        let chunk_start = Instant::now();
        let ingest_started = Instant::now();
        let (id, receipt) = port.ingest(resident, moment.as_ref(), &part)?;
        cost.port("ingest", &receipt.receipt, field);
        let chunk_ingest_ns = ingest_started.elapsed().as_nanos();
        ingest_ns = ingest_ns
            .checked_add(chunk_ingest_ns)
            .expect("per-image ingest nanoseconds overflowed u128");
        ingest_calls += 1;
        let consumed = receipt
            .forward
            .into_present()
            .ok_or("ingest returned no receipt")?;
        if consumed.cells == 0 {
            return Err("ingestion made no progress".into());
        }
        at += consumed.cells;
        moment = Some(id);
        progress.ingest_chunk_done(
            chunk + 1,
            at - consumed.cells,
            at,
            chunk_start.elapsed().as_nanos(),
            consumed.cells,
            consumed.carry_out,
        );
        chunk += 1;
        if consumed.carry_out {
            let admitted = resident.admitted().to_vec();
            progress.begin("close_aeon");
            let close_started = Instant::now();
            let boundary = port.close_aeon(resident, &admitted)?;
            cost.port("close_aeon", &boundary.receipt, field);
            let elapsed_ns = close_started.elapsed().as_nanos();
            close_aeon_ns = close_aeon_ns
                .checked_add(elapsed_ns)
                .expect("per-image carry-close nanoseconds overflowed u128");
            close_aeon_calls += 1;
            progress.done("close_aeon", elapsed_ns);
        }
    }
    let ingest_wall_ns = ingest_wall_started.elapsed().as_nanos();
    progress.done("ingest", ingest_wall_ns);
    let id = moment.ok_or("empty image passage")?;
    let phases = resident
        .admitted()
        .first()
        .ok_or("no admitted receiver")?
        .clone();
    let mut continued_view_probe_ns = None;
    if let Some((opening, views, grains)) = continued_view_probe {
        let probe_started = Instant::now();
        let state = resident.continuing_state(field.sources()[0])?;
        println!(
            "continued_view_probe_capture role={} image={} full_passage_included=true labels_used=false view_count={} elapsed_ns={}",
            progress.role,
            progress.image,
            views.len(),
            probe_started.elapsed().as_nanos(),
        );
        diagnostics::continued_views(port, field, opening, &state, views, grains)?;
        let elapsed_ns = probe_started.elapsed().as_nanos();
        continued_view_probe_ns = Some(elapsed_ns);
        cost.exterior("same_full_state_view_probe_calls", 1);
        cost.exterior("same_full_state_view_probe_views", views.len() as u128);
        println!(
            "continued_view_probe_complete role={} image={} same_full_state=true labels_used=false extra_clone_traversals={} elapsed_ns={elapsed_ns}",
            progress.role,
            progress.image,
            views.len(),
        );
    }
    let mut mode_selection_ns = None;
    let mut mode_proposal = None;
    let mut mode_choice: Option<(u64, ModeView, ChoiceReason, Rat)> = None;
    if let Some(explorer) = mode_explorer.as_deref_mut() {
        progress.begin("mode_selection");
        let selection_started = Instant::now();
        cost.exterior("mode_explorer_proposals", 1);
        let proposal = if profile_proposals {
            explorer.propose_profiled(port, resident, id, &phases)?
        } else {
            explorer.propose(port, resident, id, &phases)?
        }
        .ok_or("mode explorer exhausted its declared budget or found no nonzero input view")?;
        let selection_elapsed = selection_started.elapsed().as_nanos();
        mode_selection_ns = Some(selection_elapsed);
        progress.done("mode_selection", selection_elapsed);
        mode_choice = Some((
            proposal.sequence(),
            proposal.view().clone(),
            proposal.reason().clone(),
            proposal.contextual_score().clone(),
        ));
        let proposal_timing = proposal.timing().cloned();
        mode_proposal = Some(proposal);
        if let Some(timing) = proposal_timing {
            let substep_total_ns = timing
                .resident_read_ns
                .saturating_add(timing.source_open_storage_ns)
                .saturating_add(timing.source_storage_audit_ns)
                .saturating_add(timing.source_projection_ns)
                .saturating_add(timing.intrinsic_frame_ns)
                .saturating_add(timing.novelty_and_norm_ns)
                .saturating_add(timing.proposal_construction_ns);
            println!(
                "mode_proposal_profile role={} image={} sequence={} selection_elapsed_ns={} resident_read_ns={} source_open_storage_ns={} source_storage_audit_ns={} source_storage_shape={:?} source_storage_entries={} source_storage_nonzero={} source_storage_rational_component_bits={} source_storage_max_component_bits={} source_projection_ns={} intrinsic_frame_ns={} novelty_and_norm_ns={} proposal_construction_ns={} substep_total_ns={} selection_unattributed_ns={} menu_views={} host_wall_clock=true timer_intervals={} hardware_instruction_count=false source_storage_bits_are_exact_component_magnitude_counts_not_ram=true",
                progress.role,
                progress.image,
                mode_choice
                    .as_ref()
                    .map(|choice| choice.0)
                    .unwrap_or_default(),
                selection_elapsed,
                timing.resident_read_ns,
                timing.source_open_storage_ns,
                timing.source_storage_audit_ns,
                timing.source_storage_shape,
                timing.source_storage_entries,
                timing.source_storage_nonzero,
                timing.source_storage_rational_component_bits,
                timing.source_storage_max_component_bits,
                timing.source_projection_ns,
                timing.intrinsic_frame_ns,
                timing.novelty_and_norm_ns,
                timing.proposal_construction_ns,
                substep_total_ns,
                selection_elapsed.saturating_sub(substep_total_ns),
                timing.menu_views,
                5 + 3 * timing.menu_views,
            );
        }
    }
    progress.begin("refine");
    let refine_started = Instant::now();
    let (pending, refined) = if let Some(proposal) = mode_proposal {
        let explorer = mode_explorer
            .as_deref_mut()
            .ok_or("mode explorer proposal lost its selector")?;
        let trial = explorer.execute(port, resident, proposal)?;
        cost.exterior("mode_explorer_executions", 1);
        let (sequence, view, reason, contextual_score) = mode_choice
            .as_ref()
            .ok_or("mode explorer execution lost its selection metadata")?;
        println!(
            "mode_selection role={} image={} sequence={} menu_index={} view={:?} reason={reason:?} contextual_score={contextual_score:?} selection_elapsed_ns={:?} word_ticks={} selected_source_bits={} reached_logit_values={} reported_peak_bits={} reported_work={:?} label_or_target_accessed=false",
            progress.role,
            progress.image,
            sequence,
            trial.view_index,
            view,
            mode_selection_ns,
            trial.feedback.word_ticks,
            trial.feedback.selected_source_bits,
            trial
                .feedback
                .reached_logits
                .iter()
                .map(Vec::len)
                .sum::<usize>(),
            trial.feedback.reported_peak_bits,
            trial.feedback.reported_work,
        );
        (trial.pending, trial.returned)
    } else {
        port.refine_view(resident, &id, &phases, mode_view)?
    };
    cost.port("refine", &refined.receipt, field);
    let refine_ns = refine_started.elapsed().as_nanos();
    progress.done("refine", refine_ns);
    let faces = refined
        .forward
        .present()
        .ok_or("refinement returned no face")?
        .clone();
    progress.begin("pre_release_decode");
    let pre_release_decode_started = Instant::now();
    if faces.faces.len() != 1 {
        return Err(format!(
            "expected the one declared label phase, got {}",
            faces.faces.len()
        )
        .into());
    }
    if faces.faces[0].cells().len() != boundary.classes() {
        return Err(format!(
            "expected {} class cells, got {}",
            boundary.classes(),
            faces.faces[0].cells().len()
        )
        .into());
    }
    let pre_release = class_scores(&faces.faces[0])?;
    cost.score_read(&pre_release);
    let pre_release_decode_ns = pre_release_decode_started.elapsed().as_nanos();
    progress.done("pre_release_decode", pre_release_decode_ns);
    progress.begin("release");
    let release_started = Instant::now();
    let release = port.release(
        resident,
        &pending,
        &DecisionRule::new(
            "MNIST face at its declared tolerance",
            WithinTolerance::Release,
            BeyondTolerance::Hold,
        ),
    )?;
    cost.port("release", &release.receipt, field);
    let release_ns = release_started.elapsed().as_nanos();
    progress.done("release", release_ns);
    progress.begin("released_decode");
    let released_decode_started = Instant::now();
    let released = release
        .forward
        .present()
        .map(|released_faces| {
            if released_faces.faces.len() != 1 {
                return Err(HnnError::Shape {
                    what: "the released MNIST label phase",
                    expected: 1,
                    found: released_faces.faces.len(),
                });
            }
            if released_faces.faces[0].cells().len() != boundary.classes() {
                return Err(HnnError::Shape {
                    what: "the released face's authored class cells",
                    expected: boundary.classes(),
                    found: released_faces.faces[0].cells().len(),
                });
            }
            let scores = class_scores(&released_faces.faces[0])?;
            cost.score_read(&scores);
            Ok(scores)
        })
        .transpose()?;
    let released_decode_ns = released_decode_started.elapsed().as_nanos();
    progress.done("released_decode", released_decode_ns);
    let cells = match class_grain {
        ClassGrain::Off => None,
        ClassGrain::Read(keys) => {
            progress.begin("release_cells");
            let started = Instant::now();
            let committed = port.release_cells(resident, &pending, CellLaw::Commit)?;
            cost.port("release_cells", &committed.receipt, field);
            let drawn = keys
                .map(|keys| port.release_cells(resident, &pending, CellLaw::Draw(keys)))
                .transpose()?;
            if let Some(drawn) = &drawn {
                cost.port("release_cells", &drawn.receipt, field);
            }
            let elapsed_ns = started.elapsed().as_nanos();
            progress.done("release_cells", elapsed_ns);
            Some(CellsRead {
                commit: committed
                    .forward
                    .into_present()
                    .ok_or("the release at class grain returned no cells")?,
                drawn: drawn
                    .map(|drawn| {
                        drawn
                            .forward
                            .into_present()
                            .ok_or("the draw at class grain returned no cells")
                    })
                    .transpose()?,
                elapsed_ns,
            })
        }
    };
    Ok((
        ObservationRead {
            moment: id,
            pending,
            faces,
            pre_release,
            released,
            cells,
        },
        PredictionTiming {
            stages: StageTimes {
                encode_ns: Some(encode_ns),
                ingest_ns: Some(ingest_ns),
                ingest_wall_ns: Some(ingest_wall_ns),
                ingest_calls,
                close_aeon_ns: (close_aeon_calls != 0).then_some(close_aeon_ns),
                mode_selection_ns,
                continued_view_probe_ns,
                refine_ns: Some(refine_ns),
                pre_release_decode_ns: Some(pre_release_decode_ns),
                release_ns: Some(release_ns),
                released_decode_ns: Some(released_decode_ns),
                close_aeon_calls,
                ..StageTimes::default()
            },
            current_rings,
            input_symbols,
            cost,
        },
    ))
}

#[derive(Default, Debug)]
struct Metrics {
    samples: usize,
    raw_digit_decoded: usize,
    raw_digit_correct: usize,
    released_faces: usize,
    released_digit_outputs: usize,
    released_digit_correct: usize,
    class_grain_samples: usize,
    commit_digit_outputs: usize,
    commit_digit_correct: usize,
    drawn_samples: usize,
    drawn_digit_outputs: usize,
    drawn_digit_correct: usize,
}

impl Metrics {
    fn record(&mut self, read: &ObservationRead, boundary: &PairedObservation, label: usize) {
        self.samples += 1;
        if read.released_face() {
            self.released_faces += 1;
        }
        if let Some(raw) = read.raw_digit(boundary) {
            self.raw_digit_decoded += 1;
            self.raw_digit_correct += usize::from(raw == label);
        }
        if let Some(released) = read.released_digit(boundary) {
            self.released_digit_outputs += 1;
            self.released_digit_correct += usize::from(released == label);
        }
        if let Some(cells) = &read.cells {
            self.class_grain_samples += 1;
            if let Some(digit) = CellsRead::digit(&cells.commit, boundary) {
                self.commit_digit_outputs += 1;
                self.commit_digit_correct += usize::from(digit == label);
            }
            if let Some(drawn) = &cells.drawn {
                self.drawn_samples += 1;
                if let Some(digit) = CellsRead::digit(drawn, boundary) {
                    self.drawn_digit_outputs += 1;
                    self.drawn_digit_correct += usize::from(digit == label);
                }
            }
        }
    }

    fn summary(&self, name: &str) -> String {
        let abstentions = self.samples.saturating_sub(self.released_digit_outputs);
        let class_grain = if self.class_grain_samples == 0 {
            String::new()
        } else {
            format!(
                " commit_digit_coverage={}/{} commit_digit_correct={}/{} drawn_digit_coverage={}/{} drawn_digit_correct={}/{}",
                self.commit_digit_outputs,
                self.class_grain_samples,
                self.commit_digit_correct,
                self.class_grain_samples,
                self.drawn_digit_outputs,
                self.drawn_samples,
                self.drawn_digit_correct,
                self.drawn_samples,
            )
        };
        format!(
            "{name}_raw_digit={}/{} raw_digit_correct={}/{} released_faces={}/{} released_digit_coverage={}/{} released_digit_correct={}/{} released_only_accuracy={}/{} released_digit_abstentions={}/{}",
            self.raw_digit_decoded,
            self.samples,
            self.raw_digit_correct,
            self.samples,
            self.released_faces,
            self.samples,
            self.released_digit_outputs,
            self.samples,
            self.released_digit_correct,
            self.samples,
            self.released_digit_correct,
            self.released_digit_outputs,
            abstentions,
            self.samples,
        ) + &class_grain
    }
}

/// Save and exact-roundtrip-check the trained constitution. This intentionally does not claim
/// to checkpoint the complete host/CUDA resident passage or its current reception state.
fn write_constitution_checkpoint<P: ExecutionPort>(
    field: &Field,
    resident: &P::Resident,
    declared_opening: &Constitution,
    sources: &[usize],
    path: &str,
    phase: &str,
    exterior_cost: &mut cost::CostLedger,
) -> Result<()>
where
    P::Resident: ExposedResident,
{
    let checkpoint_started = Instant::now();
    let source = *sources
        .first()
        .ok_or("cannot checkpoint a field with no source rings")?;
    let state = resident.constitution().continuing_state(source)?;
    exterior_cost.exterior("constitution_continuing_state_serializations", 1);
    let text = state.to_text();
    let utf8_bytes = text.as_bytes().len();
    write_checkpoint_file(path, text.as_bytes())?;
    exterior_cost.exterior("constitution_checkpoint_file_writes", 1);
    exterior_cost.exterior(
        "constitution_checkpoint_file_bytes_written",
        utf8_bytes as u128,
    );
    let read_back = read_checkpoint_file(path)?;
    exterior_cost.exterior("constitution_checkpoint_file_readbacks", 1);
    exterior_cost.exterior(
        "constitution_checkpoint_file_bytes_read",
        read_back.len() as u128,
    );
    if read_back != text.as_bytes() {
        return Err("constitution checkpoint bytes differed after write/read-back".into());
    }
    let read_back_text = std::str::from_utf8(&read_back)?;
    let parsed = ContinuingState::from_text(read_back_text)?;
    exterior_cost.exterior("constitution_checkpoint_parses", 1);
    if parsed != state {
        return Err("constitution checkpoint parse did not reproduce its exact state".into());
    }
    // Reuse the exact declared opening retained before learning/restoration. Rebuilding a
    // Single receiver here would erase the explicit ArrivalContext declaration and correctly
    // fail the core material-identity check; never repair that mismatch by restamping a save.
    let restored = declared_opening.clone().continued_on(field, &parsed)?;
    exterior_cost.exterior("constitution_checkpoint_restores", 1);
    if &restored != resident.constitution() {
        return Err("constitution checkpoint restored on its declared opening did not equal the live constitution".into());
    }
    let coordinate_storage = resident.constitution().chart_coordinate_storage();
    let coordinate_storage_by_locus = resident.constitution().chart_coordinate_storage_by_locus();
    println!(
        "checkpoint phase={phase} kind=constitution_only path={path:?} source_ring={source} exact_utf8_bytes={utf8_bytes} file_bytes={} byte_roundtrip_equal=true state_parse_equal=true restored_constitution_equal=true resident_full_passage_included=false resident_lift_included=false resident_address_included=false reception_carry_included=false current_included=false handles_included=false exact_constitution_bits={} resident_state_bits={} chart_coordinate_storage={coordinate_storage:?} chart_coordinate_storage_by_locus={coordinate_storage_by_locus:?} accounting=chart_coordinate_payload_and_descriptor_estimates_are_not_allocator_ram_or_disk_checkpoint_bytes elapsed_ns={}",
        read_back.len(),
        resident.constitution().exact_bits(),
        resident.state_bits(),
        checkpoint_started.elapsed().as_nanos(),
    );
    Ok(())
}

/// Run the same example over either execution port. The mount closure is the only realization
/// adapter because `ExecutionPort` intentionally exposes `mount`, while the host and card each own
/// their concrete `mount_with` operation.
pub fn run<P, Mount>(port: &P, args: &[String], mount_with: Mount) -> Result<()>
where
    P: ExecutionPort,
    P::Resident: ExposedResident,
    Mount: Fn(&Field, &Current, Constitution) -> std::result::Result<P::Resident, HnnError>,
{
    let mut arrival_context = false;
    let mut chart = InputChart::Serial;
    let mut mode_view_spec: Option<String> = None;
    let mut explore_mode_view_spec: Option<String> = None;
    let mut run_fixed_state_probe = false;
    let mut run_post_deposit_replay = false;
    let mut checkpoint_out: Option<&str> = None;
    let mut checkpoint_every = 0usize;
    let mut checkpoint_prefix: Option<&str> = None;
    let mut verbose_faces = false;
    let mut verbose_priors = false;
    let mut profile_proposals = false;
    let mut run_same_full_state_view_probe = false;
    let mut release_keys: Option<&str> = None;
    let mut observation: Option<ObservationPartition> = None;
    let mut checkpoint_in: Option<&str> = None;
    let mut arg_at = 0;
    while let Some(option) = args.get(arg_at).map(String::as_str) {
        match option {
            "--arrival-context" => {
                arrival_context = true;
                arg_at += 1;
            }
            "--mode-view" => {
                mode_view_spec = Some(
                    args.get(arg_at + 1)
                        .ok_or("--mode-view requires SOURCE:PERIOD[,SOURCE:PERIOD]")?
                        .clone(),
                );
                arg_at += 2;
            }
            "--explore-mode-view" => {
                explore_mode_view_spec = Some(
                    args.get(arg_at + 1)
                        .ok_or("--explore-mode-view requires SOURCE:PERIOD[,SOURCE:PERIOD]")?
                        .clone(),
                );
                arg_at += 2;
            }
            "--chart" => {
                let name = args
                    .get(arg_at + 1)
                    .ok_or("--chart requires `serial` or `placed`")?;
                chart = match name.as_str() {
                    "serial" => InputChart::Serial,
                    "placed" => InputChart::Placed,
                    other => {
                        return Err(format!(
                            "unknown chart {other:?}; choose `serial` or `placed`"
                        )
                        .into());
                    }
                };
                arg_at += 2;
            }
            "--fixed-state-probe" => {
                run_fixed_state_probe = true;
                arg_at += 1;
            }
            "--post-deposit-replay" => {
                run_post_deposit_replay = true;
                arg_at += 1;
            }
            "--checkpoint-out" => {
                checkpoint_out = Some(
                    args.get(arg_at + 1)
                        .ok_or("--checkpoint-out requires a path")?,
                );
                arg_at += 2;
            }
            "--checkpoint-every" => {
                checkpoint_every = args
                    .get(arg_at + 1)
                    .ok_or("--checkpoint-every requires a positive image count")?
                    .parse()?;
                if checkpoint_every == 0 {
                    return Err("--checkpoint-every must be positive".into());
                }
                arg_at += 2;
            }
            "--checkpoint-prefix" => {
                checkpoint_prefix = Some(
                    args.get(arg_at + 1)
                        .ok_or("--checkpoint-prefix requires a path prefix")?,
                );
                arg_at += 2;
            }
            "--verbose-faces" => {
                verbose_faces = true;
                arg_at += 1;
            }
            "--verbose-priors" => {
                verbose_priors = true;
                arg_at += 1;
            }
            "--profile-proposals" => {
                profile_proposals = true;
                arg_at += 1;
            }
            "--same-full-state-view-probe" => {
                run_same_full_state_view_probe = true;
                arg_at += 1;
            }
            "--checkpoint-in" => {
                checkpoint_in = Some(
                    args.get(arg_at + 1)
                        .ok_or("--checkpoint-in requires a path")?,
                );
                arg_at += 2;
            }
            "--release-keys" => {
                release_keys = Some(
                    args.get(arg_at + 1)
                        .ok_or("--release-keys requires a path to the declared key bytes")?,
                );
                arg_at += 2;
            }
            "--observation" => {
                let name = args
                    .get(arg_at + 1)
                    .ok_or("--observation requires `maximum-set` or `section`")?;
                observation = Some(match name.as_str() {
                    "maximum-set" => ObservationPartition::MaximumRealGrainSet,
                    "section" => ObservationPartition::ReceivingSection,
                    other => {
                        return Err(format!(
                            "unknown observation {other:?}; choose `maximum-set` or `section`"
                        )
                        .into());
                    }
                });
                arg_at += 2;
            }
            _ => break,
        }
    }
    if checkpoint_every != 0 && checkpoint_prefix.is_none() {
        return Err("--checkpoint-every requires --checkpoint-prefix".into());
    }
    if mode_view_spec.is_some() && explore_mode_view_spec.is_some() {
        return Err("--mode-view and --explore-mode-view are mutually exclusive".into());
    }
    if explore_mode_view_spec.is_some() && run_post_deposit_replay {
        return Err("--explore-mode-view and --post-deposit-replay are mutually exclusive".into());
    }
    if explore_mode_view_spec.is_some() && run_fixed_state_probe {
        return Err("--explore-mode-view and --fixed-state-probe are mutually exclusive; fixed-state probes use a single declared view".into());
    }
    if profile_proposals && explore_mode_view_spec.is_none() {
        return Err("--profile-proposals requires --explore-mode-view".into());
    }
    let args = &args[arg_at..];
    if arrival_context && run_fixed_state_probe {
        return Err("--fixed-state-probe does not yet support --arrival-context".into());
    }
    let dir = args.first().ok_or("usage: mnist_observed [--arrival-context] [--mode-view SOURCE:PERIOD[,SOURCE:PERIOD] | --explore-mode-view SOURCE:PERIOD[,SOURCE:PERIOD]] [--profile-proposals] [--same-full-state-view-probe] [--post-deposit-replay] [--fixed-state-probe] [--verbose-faces] [--verbose-priors] [--checkpoint-out PATH] [--checkpoint-every N --checkpoint-prefix PREFIX] [--chart serial|placed] [--release-keys PATH] [--checkpoint-in PATH] [--observation maximum-set|section] DATA_DIR [TRAIN=60000] [TEST=10000] [PERIODS] [OFFSETS] [EXPONENT=2] [DEPTH=6]")?;
    let mut exterior_cost = cost::CostLedger::default();
    let setup_owner_before = holonics::hnn::word::work::read();
    let train_count = args
        .get(1)
        .map(|x| x.parse())
        .transpose()?
        .unwrap_or(60_000usize);
    let test_count = args
        .get(2)
        .map(|x| x.parse())
        .transpose()?
        .unwrap_or(10_000usize);
    if checkpoint_in.is_some() && train_count != 0 {
        return Err("--checkpoint-in is evaluation-only and requires TRAIN=0".into());
    }
    if train_count > 60_000 || test_count > 10_000 {
        return Err("counts exceed official split".into());
    }
    if run_fixed_state_probe && train_count == 0 {
        return Err("--fixed-state-probe requires at least one training image".into());
    }
    if run_same_full_state_view_probe && test_count == 0 {
        return Err("--same-full-state-view-probe requires at least one held-out image".into());
    }
    let train_images_bytes = read(&format!("{dir}/train-images-idx3-ubyte"))?;
    let train_labels_bytes = read(&format!("{dir}/train-labels-idx1-ubyte"))?;
    let test_images_bytes = read(&format!("{dir}/t10k-images-idx3-ubyte"))?;
    let test_labels_bytes = read(&format!("{dir}/t10k-labels-idx1-ubyte"))?;
    exterior_cost.exterior("dataset_file_reads", 4);
    println!(
        "{}",
        cost::input_storage_summary(
            &train_images_bytes,
            &train_labels_bytes,
            &test_images_bytes,
            &test_labels_bytes
        )
    );
    let train_images = Images::parse(&train_images_bytes)?;
    let train_labels = Labels::parse(&train_labels_bytes)?;
    let test_images = Images::parse(&test_images_bytes)?;
    let test_labels = Labels::parse(&test_labels_bytes)?;
    exterior_cost.exterior("IDX_parsers", 4);
    if train_images.len() != 60_000
        || train_labels.len() != 60_000
        || test_images.len() != 10_000
        || test_labels.len() != 10_000
    {
        return Err("expected official 60000/10000 MNIST counts".into());
    }
    for images in [&train_images, &test_images] {
        if images.grid().width() != 28 || images.grid().height() != 28 {
            return Err("MNIST requires 28 by 28 images".into());
        }
    }
    // Provisional authored bootstrap geometry, independently configurable; no spatial-structure,
    // invariance or optimality claim. The depth is an explicit context/address and exact-work knob.
    let periods_vec: Vec<u64> = args
        .get(3)
        .map(String::as_str)
        .unwrap_or(chart.default_periods())
        .split(',')
        .map(str::parse)
        .collect::<std::result::Result<_, _>>()?;
    let periods: [u64; 3] = periods_vec
        .try_into()
        .map_err(|_| "exactly three ring periods required")?;
    let mut offsets: Vec<usize> = args
        .get(4)
        .map(String::as_str)
        .unwrap_or(chart.default_offsets())
        .split(',')
        .map(str::parse)
        .collect::<std::result::Result<_, _>>()?;
    offsets.sort_unstable();
    offsets.dedup();
    let exponent = args.get(5).map(|x| x.parse()).transpose()?.unwrap_or(2i64);
    // Serial passage has 4704 digits; placed x/y passage has 1568. Depth six is a configurable
    // pilot horizon, not a claim that the model learned a six-cell image structure.
    let depth = args
        .get(6)
        .map(|x| x.parse())
        .transpose()?
        .unwrap_or(6usize);
    if chart == InputChart::Placed && (periods[0] < 28 || periods[1] < 28) {
        return Err("the placed MNIST x=column/y=row chart needs source-ring periods at least 28, without coordinate aliasing".into());
    }
    let sources = chart.source_rings();
    // Bound the full training horizon, the largest live image moment and the native located
    // capacity derived from this exact field geometry. The pilot subset never changes the machine.
    // Do not multiply by all dataset symbols or hand-tune a capacity threshold.
    let located_n_star = holonics::hnn::moment::capacity_located(
        &periods,
        &vec![holonics::hnn::RingAdvance::Lock; periods.len()],
        sources,
        MNIST_ALPHABET,
        &offsets,
    )?
    .n_star();
    let population = 60_000usize.max(chart.digits_per_image()).max(
        usize::try_from(located_n_star).map_err(|_| "located capacity does not fit host usize")?,
    ) as u64;
    let field = field(
        periods,
        offsets.clone(),
        exponent,
        depth,
        sources,
        population,
    )?;
    // The receiver's declared observation partition, read beside each phase's causal address.
    let field = match observation {
        Some(partition) => {
            let receiver = field.receivers()[0].ring;
            println!(
                "observation {} on ring {receiver}: {} letters a phase",
                partition.tag(),
                partition.outcome_bits(&field, receiver)
            );
            field.with_receiving_context(receiver, partition)?
        }
        None => field,
    };
    let mode_view = if let Some(spec) = mode_view_spec.as_deref() {
        parse_mode_view(&field, spec)?
    } else {
        ModeView::whole()
    };
    mode_view.check(&field)?;
    let exploration_view = if let Some(spec) = explore_mode_view_spec.as_deref() {
        if chart != InputChart::Placed {
            return Err(
                "--explore-mode-view is currently declared only for the occurrence-placed chart"
                    .into(),
            );
        }
        let view = parse_mode_view(&field, spec)?;
        if view.is_whole() {
            return Err("--explore-mode-view must include at least one source mode".into());
        }
        Some(view)
    } else {
        None
    };
    let continued_view_probe_views = if run_same_full_state_view_probe {
        if chart != InputChart::Placed || periods != [28, 28, 11] {
            return Err("--same-full-state-view-probe currently requires --chart placed with periods 28,28,11".into());
        }
        let whole = ModeView::whole();
        let union = parse_mode_view(&field, "0:4,0:28,1:4,1:28")?;
        let complement = parse_mode_view(&field, "0:1,0:2,0:7,0:14,1:1,1:2,1:7,1:14")?;
        Some(vec![
            ("whole", whole),
            ("q4_plus_q28", union),
            ("complement", complement),
        ])
    } else {
        None
    };
    let main_explorer_budget = if exploration_view.is_some() {
        let arrivals = train_count
            .checked_add(test_count)
            .ok_or("adaptive arrival count overflowed usize")?;
        let arrivals =
            u64::try_from(arrivals).map_err(|_| "adaptive arrival count does not fit u64")?;
        // The declared receiver aperture is one station, so one state-advancing refine costs
        // exactly one traversal and one station in this exterior budget.
        Some(ExplorationBudget {
            traversals: arrivals,
            receiving_stations: arrivals,
        })
    } else {
        None
    };
    let mut main_explorer = match (&exploration_view, &main_explorer_budget) {
        (Some(view), Some(budget)) => Some(ModeExplorer::new(
            &field,
            vec![ModeView::whole(), view.clone()],
            budget.clone(),
        )?),
        _ => None,
    };
    exterior_cost.exterior("field_declaration", 1);
    let material = Constitution::initial(&field, BUDGET)?;
    exterior_cost.exterior("initial_constitution", 1);
    let pairing = PairingDeclaration::Family {
        table: (0..MNIST_ALPHABET).map(|c| (c, c ^ 1)).collect(),
    };
    let mut material = material;
    for &source in sources {
        material = PairedCarrier::found(&field, material, source, &pairing)?.0;
    }
    configure_arrival_context(&field, &mut material, arrival_context)?;
    let full_opening = material.clone();
    if let Some(path) = checkpoint_in {
        material = load_evaluation_material(&field, path, &full_opening)?;
        exterior_cost.exterior("evaluation_checkpoint_reads", 1);
        exterior_cost.exterior("evaluation_checkpoint_restores", 1);
    }
    for receiver in field.receivers() {
        let layout = material.receiving_layout(receiver.ring);
        if arrival_context != matches!(layout, Some(ReceivingLayout::ArrivalContext { .. })) {
            return Err("requested receiving layout does not match restored material".into());
        }
        println!(
            "receiving_configuration ring={} layout={layout:?} arrival_context={arrival_context} finite_candidate_admission={arrival_context} operand_chart_founding=first_nonzero_actual_feature fresh_training_required_for_old_phase_chart=true",
            receiver.ring
        );
    }
    exterior_cost.exterior("initial_source_admissions", sources.len() as u128);
    PairedObservation::admit(&field, &material, &pairing)?;
    exterior_cost.exterior("initial_boundary_admission_validation", 1);
    let mut resident = mount_with(&field, &Current::at_rest(&field), material)?;
    exterior_cost.exterior("resident_mount", 1);
    exterior_cost.native_word_work_since(setup_owner_before);
    println!("{}", cost::exact_state_summary("initial_mount", &resident));
    let started = Instant::now();
    println!(
        "chart={} digits_per_image={} alphabet={} rings={periods:?} offsets={offsets:?} sources={sources:?} train={train_count}/60000 test={test_count}/10000 depth={depth} population={} identity_n_star={} located_n_star={} spatial_equivariance=false coordinate_orientation={} mode_view_selections={:?} mode_view_bits={} mode_view_default_whole={} explore_menu={:?} explore_budget={main_explorer_budget:?} explore_menu_order=[Whole,authored_view] exploration_policy=input_only_unmeasured_then_contextual_novelty post_deposit_replay={}",
        chart.label(),
        chart.digits_per_image(),
        field.alphabet(),
        field.population(),
        field.capacity().n_star(),
        located_n_star,
        if chart == InputChart::Placed {
            "x=column,y=row"
        } else {
            "serial_passage_contains_row_column"
        },
        mode_view.selections(),
        mode_view.bits(),
        mode_view.is_whole(),
        exploration_view.as_ref().map(ModeView::selections),
        run_post_deposit_replay
    );
    println!(
        "timing_scope=exterior_monotonic_Instant_elapsed_ns integer wall time; ingest_ns=sum of port.ingest calls; ingest_wall_ns includes chunking/carry-close/progress wrapper; default_one_traversal_per_arrival=true; optional_post_deposit_replay_is_a_second_state_changing_forward_traversal=true; no device-event timing"
    );
    if profile_proposals {
        println!(
            "proposal_profile_scope=opt_in --profile-proposals; timings are sequential host Instant intervals inside propose; timer_intervals_per_proposal=5+3*menu_views; no extra resident read/open/projection/scoring operations; source_storage_audit is an explicit opt-in exact coefficient scan whose time is separately reported; reports source shape, entry/nonzero counts, and summed numerator+denominator magnitude bits (not allocated RAM); selection_unattributed is outer propose duration minus measured substeps; no GPU event timing or hardware instruction count"
        );
    }
    if run_same_full_state_view_probe {
        println!(
            "same_full_state_view_probe_scope=opt_in first learned heldout input after actual ingest; views=[Whole,Q4+Q28,complement]; exact full continuation restored per diagnostic view; three additional clone traversals plus release; labels not passed; production resident then follows its ordinary single traversal; probe time is separate"
        );
    }

    let mut train_metrics = Metrics::default();
    let mut finite_strict_updates = 0usize;
    let mut finite_neutral_updates = 0usize;
    let mut train_timings = TimingTotals::default();
    let mut train_cost = cost::CostLedger::default();
    for index in 0..train_count {
        let report_update = index == 0 || index + 1 == train_count;
        let sample_owner_before = holonics::hnn::word::work::read();
        let mut sample_cost = cost::CostLedger::default();
        // The authored observation boundary is re-admitted on the current material for every image.
        let progress = StageProgress {
            role: "train",
            image: index + 1,
            enabled: index == 0,
        };
        progress.begin("boundary_admission");
        let boundary_started = Instant::now();
        let boundary = PairedObservation::admit(&field, resident.constitution(), &pairing)?;
        sample_cost.exterior("observed_boundary_admission", 1);
        let boundary_admission_ns = boundary_started.elapsed().as_nanos();
        progress.done("boundary_admission", boundary_admission_ns);
        let sample = Raster::new(train_images.grid(), train_images.image(index)?.to_vec())?;
        let (read, prediction_timing) = predict(
            port,
            &mut resident,
            &field,
            chart,
            periods,
            &mode_view,
            main_explorer.as_mut(),
            profile_proposals,
            None,
            &boundary,
            sample,
            progress,
            ClassGrain::Off,
        )?;
        sample_cost.merge(&prediction_timing.cost);
        let mut stages = prediction_timing.stages;
        stages.boundary_admission_ns = Some(boundary_admission_ns);
        // First per-index label lookup is after the face and actual release/abstention decision.
        let label = train_labels.label(index)? as usize;
        sample_cost.exterior("label_lookup", 1);
        if label >= 10 {
            return Err("invalid MNIST label".into());
        }
        train_metrics.record(&read, &boundary, label);
        progress.begin("target_encode");
        let target_encode_started = Instant::now();
        let target = boundary.encode(&[label])?;
        sample_cost.exterior("target_encode", 1);
        let target_encode_ns = target_encode_started.elapsed().as_nanos();
        progress.done("target_encode", target_encode_ns);
        stages.target_encode_ns = Some(target_encode_ns);
        let material_before = report_update.then(|| resident.constitution().clone());
        progress.begin("compare");
        let compare_started = Instant::now();
        let (staged, comparison_return) = port.compare(&mut resident, read.pending, &target)?;
        sample_cost.port("compare", &comparison_return.receipt, &field);
        let compare_ns = compare_started.elapsed().as_nanos();
        stages.compare_ns = Some(compare_ns);
        progress.done("compare", compare_ns);
        let active_phases = resident
            .admitted()
            .first()
            .ok_or("no admitted receiver for precision event")?
            .clone();
        // Capture only the real receiver operands from the actual staged linear deposit. The
        // precision decision never reads the target, covector, masses, class, or label.
        let receiver_features = comparison_return
            .deposit
            .present()
            .ok_or("compare returned no staged deposit")
            .map(|deposit| receiving_features(deposit, active_phases.ring()))?;
        if report_update {
            diagnostics::gradient_report(
                index + 1,
                comparison_return
                    .pullback
                    .present()
                    .ok_or("compare returned no pullback")?,
                comparison_return
                    .deposit
                    .present()
                    .ok_or("compare returned no staged deposit")?,
            );
            diagnostics::return_precision_report(
                index + 1,
                &field,
                resident.constitution(),
                comparison_return
                    .deposit
                    .present()
                    .ok_or("compare returned no staged deposit")?,
                &comparison_return.receipt,
            )?;
        }
        if report_update || verbose_priors {
            let comparison = comparison_return
                .forward
                .present()
                .ok_or("compare returned no producing HolonRatio")?;
            for step in comparison_return
                .deposit
                .present()
                .ok_or("compare returned no staged deposit")?
                .linear()
            {
                let LinearLocus::Receiving(ring) = &step.locus else {
                    continue;
                };
                let map = resident
                    .constitution()
                    .receiving_map(*ring)
                    .ok_or("prior-window diagnostic has no contemporary receiving map")?;
                let diagnostic = holonics::hnn::constitution::prior_window_diagnostic(
                    &step.samples,
                    map,
                    comparison,
                )?;
                sample_cost.exterior("prior_window_diagnostic_calls", 1);
                sample_cost.exterior(
                    "prior_window_diagnostic_samples",
                    step.samples.len() as u128,
                );
                println!(
                    "prior_window_math image={} receiving_ring={ring} samples={} alpha_odometer={:?} correction_bound={:?} alpha_face={:?} curvature_odometer={:?} curvature_face={:?} units=prior_A0_alignment_and_curvature exact_combined_faces=true read_only=true",
                    index + 1,
                    step.samples.len(),
                    diagnostic.alpha_odometer,
                    diagnostic.correction_bound,
                    diagnostic.alpha_face,
                    diagnostic.curvature_odometer,
                    diagnostic.curvature_face,
                );
            }
        }
        progress.begin("deposit");
        let deposit_started = Instant::now();
        let deposit = match port.deposit(&mut resident, staged) {
            Ok(deposit) => deposit,
            Err(error) => {
                println!(
                    "finite_deposit_refusal image={} accepted_updates=0 error={error:?}",
                    index + 1
                );
                return Err(error.into());
            }
        };
        if arrival_context {
            let ReceiptDetail::Deposit {
                finite_comparison: Some(finite),
                reading,
                ..
            } = &deposit.receipt.detail
            else {
                return Err(
                    "paired deposit omitted its finite-candidate acceptance receipt".into(),
                );
            };
            finite_strict_updates += usize::from(finite.comparison.strictly_improved);
            finite_neutral_updates += usize::from(finite.comparison.objective_equal());
            println!(
                "finite_deposit_accepted image={} accepted_updates=1 strict_improvement={} neutral_plateau={} raw_wave_unchanged={} receipt={finite:?} applied_steps={:?}",
                index + 1,
                finite.comparison.strictly_improved,
                finite.comparison.objective_equal(),
                finite.comparison.unchanged,
                reading.steps
            );
            for receiver in field.receivers() {
                let blocks = resident
                    .constitution()
                    .receiving_blocks(receiver.ring)
                    .ok_or("paired material lost its receiving blocks")?;
                for (block_index, block) in blocks.iter().enumerate() {
                    println!(
                        "receiving_block image={} ring={} block={} operand_sigma={:?} prior_scale={} founding_prior={:?}",
                        index + 1,
                        receiver.ring,
                        block_index,
                        block.chart().map(|chart| chart.scale()),
                        block.law().prior_scale(),
                        block.law().receiving_prior()
                    );
                }
            }
        }
        sample_cost.port("deposit", &deposit.receipt, &field);
        let deposit_ns = deposit_started.elapsed().as_nanos();
        stages.deposit_ns = Some(deposit_ns);
        progress.done("deposit", deposit_ns);
        let deposit_reading = deposit
            .deposit
            .present()
            .ok_or("deposit returned no published material reading")?;
        let chart_prior_readings = deposit_reading
            .charts
            .iter()
            .map(|(locus, chart)| {
                (
                    locus.clone(),
                    chart.exponent,
                    chart.prior.as_ref().map(|prior| {
                        (
                            prior.from,
                            prior.to,
                            prior.held.clone(),
                            prior.certificate.clone(),
                        )
                    }),
                )
            })
            .collect::<Vec<_>>();
        sample_cost.exterior(
            "deposit_chart_prior_readings_emitted",
            chart_prior_readings.len() as u128,
        );
        let mut prior_up = 0usize;
        let mut prior_down = 0usize;
        let mut prior_same = 0usize;
        let mut prior_held = 0usize;
        let mut prior_present = 0usize;
        for (_, _, prior) in &chart_prior_readings {
            if let Some((from, to, held, _)) = prior {
                prior_present += 1;
                match to.cmp(from) {
                    std::cmp::Ordering::Greater => prior_up += 1,
                    std::cmp::Ordering::Less => prior_down += 1,
                    std::cmp::Ordering::Equal => prior_same += 1,
                }
                prior_held += usize::from(held.is_some());
            }
        }
        println!(
            "prior_summary image={} charts={} prior_records={} moved_up={} moved_down={} unchanged={} held={} unreported={}",
            index + 1,
            chart_prior_readings.len(),
            prior_present,
            prior_up,
            prior_down,
            prior_same,
            prior_held,
            chart_prior_readings.len().saturating_sub(prior_present),
        );
        if verbose_priors || report_update {
            println!(
                "prior_detail image={} deposit_chart_prior_readings={chart_prior_readings:?}",
                index + 1
            );
        }
        if let Some(before) = material_before.as_ref() {
            diagnostics::material_report(index + 1, &field, before, resident.constitution());
        }
        let before_bits = read.faces.faces[0].code_length(label)?;
        sample_cost.exterior("true_label_code_length", 1);
        let mut after_bits = None;
        let mut replay_pending = None;
        if run_post_deposit_replay {
            // This explicit second look runs a real forward traversal and advances the resident's
            // reception carry. The default remains one traversal per arrival.
            let phases = resident
                .admitted()
                .first()
                .ok_or("no admitted receiver after deposit")?
                .clone();
            progress.begin("post_deposit_replay");
            let replay_started = Instant::now();
            let (pending, reread) =
                port.refine_view(&mut resident, &read.moment, &phases, &mode_view)?;
            sample_cost.port("post_deposit_replay", &reread.receipt, &field);
            let post_faces = reread
                .forward
                .present()
                .ok_or("post-deposit replay returned no face")?;
            if post_faces.faces.len() != 1 {
                return Err("post-deposit replay returned the wrong label-phase count".into());
            }
            after_bits = Some(post_faces.faces[0].code_length(label)?);
            sample_cost.exterior("true_label_code_length", 1);
            replay_pending = Some(pending);
            let replay_ns = replay_started.elapsed().as_nanos();
            stages.post_deposit_reread_ns = Some(replay_ns);
            progress.done("post_deposit_replay", replay_ns);
        }
        println!(
            "target_score image={} true_label={label} true_label_code_before_deposit={before_bits:?} true_label_code_after_optional_replay={after_bits:?} published_deposit=true replay_enabled={} replay_semantics=second_state_changing_forward_traversal score_after_replay_unavailable_when_disabled={}",
            index + 1,
            run_post_deposit_replay,
            !run_post_deposit_replay,
        );
        if report_update {
            if let Some(moment) = resident.moment(&read.moment) {
                println!(
                    "retained_moment phase=post_deposit_before_handle_cleanup image={} dense_logical_bits={}",
                    index + 1,
                    moment.dense_bits()
                );
            }
            println!(
                "{}",
                cost::exact_state_summary(
                    if index == 0 {
                        "post_deposit_before_handle_cleanup_first"
                    } else {
                        "post_deposit_before_handle_cleanup_last"
                    },
                    &resident
                )
            );
        }
        if let Some(post_deposit) = replay_pending {
            let discarded_pending = port.discard(&mut resident, Handle::Pending(post_deposit))?;
            sample_cost.port("discard", &discarded_pending.receipt, &field);
        }
        let discarded_moment = port.discard(&mut resident, Handle::Moment(read.moment))?;
        sample_cost.port("discard", &discarded_moment.receipt, &field);
        // The evidence is checked against the current post-deposit material, after all handles
        // tied to the predecessor comparison are consumed and before the next image is opened.
        // Applying the event changes only representation/publication; it runs no extra model read.
        progress.begin("receiving_precision_event");
        let precision_started = Instant::now();
        progress.begin("receiving_precision_check");
        let precision_check_started = Instant::now();
        sample_cost.exterior("receiving_precision_event_checks", 1);
        let precision = resident.constitution().receiving_precision_event(
            active_phases.ring(),
            &receiver_features,
            active_phases.tolerance(),
        )?;
        let precision_check_ns = precision_check_started.elapsed().as_nanos();
        stages.receiving_precision_check_ns = Some(precision_check_ns);
        progress.done("receiving_precision_check", precision_check_ns);
        if let Some(event) = precision {
            let commit_before = resident.constitution().commit();
            let exact_bits_before = resident.constitution().exact_bits();
            let state_bits_before = resident.state_bits();
            let current_before = resident.current().clone();
            let admitted_before = resident.admitted().to_vec();
            let reception_carry_before = resident.carried().cloned();
            let (promoted_real, promoted_phase_turns) =
                split_receiver_reads(event.promoted_reads());
            let (unresolved_real, unresolved_phase_turns) =
                split_receiver_reads(event.unresolved_reads());
            progress.begin("receiving_precision_publish");
            let publish_started = Instant::now();
            let publication_result = resident.publish_receiving_precision(&event);
            let precision_publish_ns = publish_started.elapsed().as_nanos();
            stages.receiving_precision_publish_ns = Some(precision_publish_ns);
            progress.done("receiving_precision_publish", precision_publish_ns);
            let (applied, budget_refusal) = match publication_result {
                Ok(()) => {
                    sample_cost.exterior("receiving_precision_publications", 1);
                    if resident.current() != &current_before
                        || resident.admitted() != admitted_before.as_slice()
                        || resident.carried() != reception_carry_before.as_ref()
                    {
                        return Err("receiving precision publication changed current, admitted phases, or reception carry".into());
                    }
                    if resident.constitution().commit() != commit_before + 1 {
                        return Err(
                            "receiving precision publication did not create exactly one commit"
                                .into(),
                        );
                    }
                    (true, None)
                }
                Err(HnnError::ConstitutionBudget { bits, budget, .. }) => {
                    // A derived refinement can still exceed the concrete resident budget after
                    // retained loci and receiver precision are accounted for. The native rebase
                    // and CUDA publication construct successors before replacing resident state;
                    // check that atomic-failure contract before continuing the run.
                    if resident.current() != &current_before
                        || resident.admitted() != admitted_before.as_slice()
                        || resident.carried() != reception_carry_before.as_ref()
                        || resident.constitution().commit() != commit_before
                        || resident.constitution().exact_bits() != exact_bits_before
                        || resident.state_bits() != state_bits_before
                    {
                        return Err(
                            "budget-refused receiving precision publication mutated resident state"
                                .into(),
                        );
                    }
                    (false, Some((bits, budget)))
                }
                Err(error) => return Err(error.into()),
            };
            println!(
                "receiving_precision_event image={} applied={} refusal={} refusal_candidate_bits={:?} refusal_budget_bits={:?} applied_after=deposit_and_handle_cleanup_before_next_read commit_before={} commit_after={} budget_bits={} exact_constitution_bits_before={} exact_constitution_bits_after={} resident_state_bits_before={} resident_state_bits_after={} tolerance_units=continuous_code_length_bits phase_units=turns face_decision_bound=false event={event:?} promoted_real_logits={promoted_real:?} promoted_phase_turns={promoted_phase_turns:?} unresolved_real_logits={unresolved_real:?} unresolved_phase_turns={unresolved_phase_turns:?}",
                index + 1,
                applied,
                if applied {
                    "none"
                } else {
                    "constitution_budget"
                },
                budget_refusal.map(|(bits, _)| bits),
                budget_refusal.map(|(_, budget)| budget),
                commit_before,
                resident.constitution().commit(),
                resident.constitution().budget(),
                exact_bits_before,
                resident.constitution().exact_bits(),
                state_bits_before,
                resident.state_bits(),
            );
        } else {
            println!(
                "receiving_precision_event image={} applied=false reason=no_erased_nonzero_retained_read current_receiver_features={}",
                index + 1,
                receiver_features.len(),
            );
        }
        let precision_ns = precision_started.elapsed().as_nanos();
        stages.receiving_precision_event_ns = Some(precision_ns);
        progress.done("receiving_precision_event", precision_ns);
        sample_cost.native_word_work_since(sample_owner_before);
        train_timings.record(&stages);
        train_cost.merge(&sample_cost);
        print_sample_timing(
            "train",
            index + 1,
            &stages,
            &field,
            prediction_timing.current_rings,
            prediction_timing.input_symbols,
            periods,
        );
        if report_update {
            println!("{}", sample_cost.summary("train", Some(index + 1)));
            println!(
                "{}",
                cost::exact_state_summary(
                    if index == 0 {
                        "after_first_train_image"
                    } else {
                        "after_last_train_image"
                    },
                    &resident
                )
            );
        }
        println!(
            "train image={} pre_release_choice={} release_action={} released_choice={} observation={label} {} elapsed_ms={}",
            index + 1,
            read.pre_release.description(&boundary),
            if read.released_face() {
                "released_face"
            } else {
                "hold_abstain"
            },
            read.released.as_ref().map_or_else(
                || "no_released_face".to_owned(),
                |scores| scores.description(&boundary)
            ),
            train_metrics.summary("prequential"),
            started.elapsed().as_millis(),
        );
        if verbose_faces {
            println!(
                "face_audit role=train image={} pre_release_class_code_lengths={:?} released_class_code_lengths={:?}",
                index + 1,
                read.pre_release.code_lengths,
                read.released.as_ref().map(|scores| &scores.code_lengths),
            );
        }
        if checkpoint_every != 0 && (index + 1) % checkpoint_every == 0 {
            let prefix = checkpoint_prefix.expect("validated when options were parsed");
            let path = format!("{prefix}-train-{:05}-constitution.txt", index + 1);
            write_constitution_checkpoint::<P>(
                &field,
                &resident,
                &full_opening,
                sources,
                &path,
                "periodic_handle_clean_post_deposit_before_next_image",
                &mut exterior_cost,
            )?;
            if let (Some(explorer), Some(budget)) = (&main_explorer, &main_explorer_budget) {
                report_mode_explorer_checkpoint(
                    explorer,
                    budget,
                    &field,
                    "learned",
                    "periodic_handle_clean_post_deposit_before_next_image",
                )?;
            }
        }
    }

    // Optional final checkpoint at the handle-clean post-training boundary, before test-time reads.
    // The periodic checkpoint path uses the same equality-checked constitution-only format.
    if let Some(path) = checkpoint_out {
        write_constitution_checkpoint::<P>(
            &field,
            &resident,
            &full_opening,
            sources,
            path,
            "handle_clean_post_training_before_test",
            &mut exterior_cost,
        )?;
    }
    if exploration_view.is_none() && (mode_view.is_whole() || train_count > 0) {
        report_mode_projector_storage(
            &field,
            "learned",
            "handle_clean_post_training_before_test",
            0,
            &mode_view,
        )?;
    }
    if let (Some(explorer), Some(budget)) = (&main_explorer, &main_explorer_budget) {
        report_mode_explorer_checkpoint(
            explorer,
            budget,
            &field,
            "learned",
            "handle_clean_post_training_before_test",
        )?;
    }

    let test_boundary_owner_before = holonics::hnn::word::work::read();
    let learned_boundary_progress = StageProgress {
        role: "learned_test",
        image: 1,
        enabled: test_count != 0,
    };
    learned_boundary_progress.begin("boundary_admission");
    let learned_boundary_started = Instant::now();
    let boundary = PairedObservation::admit(&field, resident.constitution(), &pairing)?;
    exterior_cost.exterior("learned_test_boundary_admission", 1);
    let learned_boundary_admission_ns = learned_boundary_started.elapsed().as_nanos();
    learned_boundary_progress.done("boundary_admission", learned_boundary_admission_ns);
    exterior_cost.native_word_work_since(test_boundary_owner_before);
    let frozen = resident.constitution().clone();
    if run_fixed_state_probe {
        let original = Raster::new(train_images.grid(), train_images.image(0)?.to_vec())?;
        let probe_started = Instant::now();
        let probe_owner_before = holonics::hnn::word::work::read();
        diagnostics::fixed_state(
            port,
            &mount_with,
            &field,
            chart,
            periods,
            &mode_view,
            &pairing,
            &frozen,
            resident.current(),
            &original,
        )?;
        println!(
            "{}",
            cost::native_word_owner_delta("fixed_state_probe", probe_owner_before)
        );
        println!(
            "fixed_state_probe_complete mode=reset_address elapsed_ns={}",
            probe_started.elapsed().as_nanos()
        );
    }
    // Descriptive initial-material reference: it starts at the learned resident's test-time
    // current, but has not seen the training images. It is not a paired no-deposition control, so
    // learned/reference differences do not isolate deposition from training-history effects.
    let initial_material_setup_owner_before = holonics::hnn::word::work::read();
    let initial = Constitution::initial(&field, BUDGET)?;
    exterior_cost.exterior("initial_material_constitution", 1);
    let mut initial = initial;
    for &source in sources {
        initial = PairedCarrier::found(&field, initial, source, &pairing)?.0;
    }
    configure_arrival_context(&field, &mut initial, arrival_context)?;
    exterior_cost.exterior("initial_material_source_admissions", sources.len() as u128);
    let initial_boundary_progress = StageProgress {
        role: "initial_material_test",
        image: 1,
        enabled: test_count != 0,
    };
    initial_boundary_progress.begin("boundary_admission");
    let initial_boundary_started = Instant::now();
    let initial_boundary = PairedObservation::admit(&field, &initial, &pairing)?;
    exterior_cost.exterior("initial_material_test_boundary_admission", 1);
    let initial_boundary_admission_ns = initial_boundary_started.elapsed().as_nanos();
    initial_boundary_progress.done("boundary_admission", initial_boundary_admission_ns);
    let mut initial_material = mount_with(&field, resident.current(), initial)?;
    exterior_cost.exterior("initial_material_mount", 1);
    exterior_cost.native_word_work_since(initial_material_setup_owner_before);
    let initial_explorer_budget = if exploration_view.is_some() {
        let arrivals = u64::try_from(test_count)
            .map_err(|_| "held-out adaptive arrival count does not fit u64")?;
        Some(ExplorationBudget {
            traversals: arrivals,
            receiving_stations: arrivals,
        })
    } else {
        None
    };
    let mut initial_explorer = match (&exploration_view, &initial_explorer_budget) {
        (Some(view), Some(budget)) => Some(ModeExplorer::new(
            &field,
            vec![ModeView::whole(), view.clone()],
            budget.clone(),
        )?),
        _ => None,
    };
    // [agent-inferred, October 16] Both held-out roles read the same declared key at the same
    // image: one exterior stream, its bytes read once, so the learned and the initial-material
    // draws are matched key for key. Each role keeps its own continuing carry and any input-only
    // selector history; equal keys do not assert identical later causal trajectories.
    let (mut learned_keys, mut initial_keys) = match release_keys {
        Some(path) => {
            let bytes = read(path)?;
            println!(
                "release_keys declared_bytes={} key_bytes={RELEASE_KEY_BYTES} keys={} remainder_bytes={} key_cells=2^{}",
                bytes.len(),
                bytes.len() / RELEASE_KEY_BYTES,
                bytes.len() % RELEASE_KEY_BYTES,
                8 * RELEASE_KEY_BYTES,
            );
            (
                Some(KeyStream::new(bytes.clone(), RELEASE_KEY_BYTES)?),
                Some(KeyStream::new(bytes, RELEASE_KEY_BYTES)?),
            )
        }
        None => (None, None),
    };
    let mut initial_metrics = Metrics::default();
    let mut learned_metrics = Metrics::default();
    let mut learned_timings = TimingTotals::default();
    let mut initial_timings = TimingTotals::default();
    let mut learned_cost = cost::CostLedger::default();
    let mut initial_cost = cost::CostLedger::default();
    for index in 0..test_count {
        let sample = Raster::new(test_images.grid(), test_images.image(index)?.to_vec())?;
        let learned_progress = StageProgress {
            role: "learned_test",
            image: index + 1,
            enabled: index == 0,
        };
        let learned_owner_before = holonics::hnn::word::work::read();
        let (learned, learned_prediction_timing) = predict(
            port,
            &mut resident,
            &field,
            chart,
            periods,
            &mode_view,
            main_explorer.as_mut(),
            profile_proposals,
            if index == 0 {
                continued_view_probe_views
                    .as_ref()
                    .map(|views| (&full_opening, views.as_slice(), &[][..]))
            } else {
                None
            },
            &boundary,
            sample,
            learned_progress,
            ClassGrain::Read(learned_keys.as_mut()),
        )?;
        let mut learned_sample_cost = learned_prediction_timing.cost;
        learned_sample_cost.native_word_work_since(learned_owner_before);
        if index == 0 {
            learned_sample_cost.exterior("learned_test_boundary_admission", 1);
        }
        let mut learned_stages = learned_prediction_timing.stages;
        if index == 0 {
            learned_stages.boundary_admission_ns = Some(learned_boundary_admission_ns);
        }
        let initial_sample = Raster::new(test_images.grid(), test_images.image(index)?.to_vec())?;
        let initial_progress = StageProgress {
            role: "initial_material_test",
            image: index + 1,
            enabled: index == 0,
        };
        let initial_owner_before = holonics::hnn::word::work::read();
        let (initial_read, initial_prediction_timing) = predict(
            port,
            &mut initial_material,
            &field,
            chart,
            periods,
            &mode_view,
            initial_explorer.as_mut(),
            profile_proposals,
            None,
            &initial_boundary,
            initial_sample,
            initial_progress,
            ClassGrain::Read(initial_keys.as_mut()),
        )?;
        let mut initial_sample_cost = initial_prediction_timing.cost;
        initial_sample_cost.native_word_work_since(initial_owner_before);
        if index == 0 {
            initial_sample_cost.exterior("initial_material_test_boundary_admission", 1);
        }
        let mut initial_stages = initial_prediction_timing.stages;
        if index == 0 {
            initial_stages.boundary_admission_ns = Some(initial_boundary_admission_ns);
        }
        // Held-out labels are read only after both inference/release decisions; they are never
        // encoded or passed to compare/deposit.
        let label = test_labels.label(index)? as usize;
        exterior_cost.exterior("heldout_label_lookup", 1);
        if label >= 10 {
            return Err("invalid MNIST label".into());
        }
        learned_metrics.record(&learned, &boundary, label);
        initial_metrics.record(&initial_read, &initial_boundary, label);
        if let Some(cells) = &learned.cells {
            cells.report("learned", index + 1, label, &boundary);
        }
        if let Some(cells) = &initial_read.cells {
            cells.report("initial_material", index + 1, label, &initial_boundary);
        }
        learned_timings.record(&learned_stages);
        initial_timings.record(&initial_stages);
        print_sample_timing(
            "learned_test",
            index + 1,
            &learned_stages,
            &field,
            learned_prediction_timing.current_rings,
            learned_prediction_timing.input_symbols,
            periods,
        );
        print_sample_timing(
            "initial_material_test",
            index + 1,
            &initial_stages,
            &field,
            initial_prediction_timing.current_rings,
            initial_prediction_timing.input_symbols,
            periods,
        );
        learned_sample_cost.exterior("true_label_code_length", 1);
        initial_sample_cost.exterior("true_label_code_length", 1);
        if index == 0 || index + 1 == test_count {
            if let Some(moment) = resident.moment(&learned.moment) {
                println!(
                    "retained_moment phase=heldout_before_handle_cleanup role=learned image={} dense_logical_bits={}",
                    index + 1,
                    moment.dense_bits()
                );
            }
            if let Some(moment) = initial_material.moment(&initial_read.moment) {
                println!(
                    "retained_moment phase=heldout_before_handle_cleanup role=initial_material image={} dense_logical_bits={}",
                    index + 1,
                    moment.dense_bits()
                );
            }
            println!(
                "{}",
                cost::exact_state_summary(
                    if index == 0 {
                        "heldout_before_handle_cleanup_first"
                    } else {
                        "heldout_before_handle_cleanup_last"
                    },
                    &resident
                )
            );
        }
        println!(
            "held_out_score image={} true_label={label} learned_true_label_code={:?} initial_material_true_label_code={:?} learned_pre_release_choice={} learned_release_action={} learned_released_choice={} initial_material_pre_release_choice={} initial_material_release_action={} initial_material_released_choice={}",
            index + 1,
            learned.faces.faces[0].code_length(label)?,
            initial_read.faces.faces[0].code_length(label)?,
            learned.pre_release.description(&boundary),
            if learned.released_face() {
                "released_face"
            } else {
                "hold_abstain"
            },
            learned.released.as_ref().map_or_else(
                || "no_released_face".to_owned(),
                |scores| scores.description(&boundary)
            ),
            initial_read.pre_release.description(&initial_boundary),
            if initial_read.released_face() {
                "released_face"
            } else {
                "hold_abstain"
            },
            initial_read.released.as_ref().map_or_else(
                || "no_released_face".to_owned(),
                |scores| scores.description(&initial_boundary)
            ),
        );
        if verbose_faces {
            println!(
                "face_audit role=held_out image={} learned_pre_release_class_code_lengths={:?} learned_released_class_code_lengths={:?} initial_pre_release_class_code_lengths={:?} initial_released_class_code_lengths={:?}",
                index + 1,
                learned.pre_release.code_lengths,
                learned.released.as_ref().map(|scores| &scores.code_lengths),
                initial_read.pre_release.code_lengths,
                initial_read
                    .released
                    .as_ref()
                    .map(|scores| &scores.code_lengths),
            );
        }
        let discarded_pending =
            port.discard(&mut initial_material, Handle::Pending(initial_read.pending))?;
        initial_sample_cost.port("discard", &discarded_pending.receipt, &field);
        let discarded_moment =
            port.discard(&mut initial_material, Handle::Moment(initial_read.moment))?;
        initial_sample_cost.port("discard", &discarded_moment.receipt, &field);
        // Held-out labels never become Encoded or reach comparison/deposition.
        let discarded_pending = port.discard(&mut resident, Handle::Pending(learned.pending))?;
        learned_sample_cost.port("discard", &discarded_pending.receipt, &field);
        let discarded_moment = port.discard(&mut resident, Handle::Moment(learned.moment))?;
        learned_sample_cost.port("discard", &discarded_moment.receipt, &field);
        if resident.constitution() != &frozen {
            return Err("held-out inference mutated trained constitution".into());
        }
        learned_cost.merge(&learned_sample_cost);
        initial_cost.merge(&initial_sample_cost);
        if index == 0 || index + 1 == test_count {
            println!(
                "{}",
                learned_sample_cost.summary("learned_test", Some(index + 1))
            );
            println!(
                "{}",
                initial_sample_cost.summary("initial_material_test", Some(index + 1))
            );
            println!(
                "{}",
                cost::exact_state_summary(
                    if index == 0 {
                        "first_heldout_read"
                    } else {
                        "last_heldout_read"
                    },
                    &resident
                )
            );
            println!(
                "{}",
                cost::exact_state_summary(
                    if index == 0 {
                        "first_initial_material_read"
                    } else {
                        "last_initial_material_read"
                    },
                    &initial_material
                )
            );
        }
        println!(
            "test image={} observation={label} {} {} frozen=true elapsed_ms={}",
            index + 1,
            learned_metrics.summary("learned"),
            initial_metrics.summary("initial_material_same_clock"),
            started.elapsed().as_millis(),
        );
    }
    if let (Some(explorer), Some(budget)) = (&main_explorer, &main_explorer_budget) {
        report_mode_explorer_checkpoint(
            explorer,
            budget,
            &field,
            "learned",
            "after_heldout_stream",
        )?;
    }
    if let (Some(explorer), Some(budget)) = (&initial_explorer, &initial_explorer_budget) {
        report_mode_explorer_checkpoint(
            explorer,
            budget,
            &field,
            "initial_material_reference",
            "after_heldout_stream",
        )?;
    }
    if exploration_view.is_none() && !mode_view.is_whole() && train_count == 0 && test_count > 0 {
        report_mode_projector_storage(&field, "learned", "after_heldout_stream", 0, &mode_view)?;
    }
    println!(
        "complete {} {} elapsed_ms={}",
        train_metrics.summary("train_prequential"),
        learned_metrics.summary("held_out_learned"),
        started.elapsed().as_millis(),
    );
    println!(
        "complete {}",
        initial_metrics.summary("held_out_initial_material_same_clock")
    );
    println!(
        "finite_deposit_summary arrival_context={arrival_context} strict_updates={finite_strict_updates} neutral_updates={finite_neutral_updates} neutral_is_improvement=false"
    );
    println!("{}", train_timings.summary("train"));
    println!("{}", learned_timings.summary("learned_test"));
    println!("{}", initial_timings.summary("initial_material_test"));
    println!("{}", train_cost.summary("train_aggregate", None));
    println!("{}", learned_cost.summary("learned_test_aggregate", None));
    println!(
        "{}",
        initial_cost.summary("initial_material_test_aggregate", None)
    );
    println!("{}", exterior_cost.summary("setup_and_shared_labels", None));
    Ok(())
}

fn configure_arrival_context(
    field: &Field,
    material: &mut Constitution,
    enabled: bool,
) -> Result<()> {
    if enabled {
        for receiver in field.receivers() {
            material.bind_arrival_context_receiving(receiver.ring)?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod arrival_context_tests {
    use super::*;

    #[test]
    fn explicit_arrival_context_founds_zero_independent_blocks_after_source_admission() {
        let field = field([28, 28, 11], vec![1], 2, 2, &[0], 60_000).unwrap();
        let pairing = PairingDeclaration::Family {
            table: (0..MNIST_ALPHABET).map(|c| (c, c ^ 1)).collect(),
        };
        let initial = Constitution::initial(&field, BUDGET).unwrap();
        let mut material = PairedCarrier::found(&field, initial, 0, &pairing)
            .unwrap()
            .0;
        let receiver = field.receivers()[0].ring;
        configure_arrival_context(&field, &mut material, false).unwrap();
        assert_eq!(
            material.receiving_layout(receiver),
            Some(ReceivingLayout::Single)
        );
        let single_opening = material.clone();
        configure_arrival_context(&field, &mut material, true).unwrap();
        assert!(matches!(
            material.receiving_layout(receiver),
            Some(ReceivingLayout::ArrivalContext { .. })
        ));
        let blocks = material.receiving_blocks(receiver).unwrap();
        assert!(blocks.iter().all(|block| block.chart().is_none()));
        assert!(
            material
                .receiving_map(receiver)
                .unwrap()
                .entries()
                .iter()
                .all(|value| value == &integer(0))
        );
        PairedObservation::admit(&field, &material, &pairing).unwrap();
        let state = material.continuing_state(0).unwrap();
        let parsed = ContinuingState::from_text(&state.to_text()).unwrap();
        assert!(matches!(
            single_opening.continued(&parsed),
            Err(HnnError::ContinuingState { .. })
        ));
        assert_eq!(material.clone().continued(&parsed).unwrap(), material);
    }
}
