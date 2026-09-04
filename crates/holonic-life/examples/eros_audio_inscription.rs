#[path = "audio_inscription/exact_pcm.rs"]
mod exact_pcm;

use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::Instant;

use body::incidence::IncidenceHand;
use body::manifold::FeltDeed;
use body::num::Cog;
use exact_pcm::{ButterflyAtlas, ExactPathChart, PcmWave};
use life::current_world::{
    present_native_event_with_regional, NativeEventCurrent, NativeRegionalArc,
    NativeRegionalRelation, NativeRelationOrgan, NativeRelationOrganImage,
};
use life::form_mouth::deposit_form_or_message;
use serde::Serialize;
use sha2::{Digest, Sha256};
use soma_abi::active::ActionCurrent;
use soma_membrane::{
    CpuLiveCurrentExecutor, CurrentBoundaryPort, CurrentExecutionRequest, DirectedExecutionRequest,
    ExecutedContemporaryEvent, InterfaceCapability, LiveBoundaryTransition, LiveConstituent,
    LiveCurrentError, LiveCurrentExecutor, LiveCurrentMachine, LiveCurrentRestImage, LiveMemory,
    RegionalArcRadiation, RegionalExecutionRequest, SparseStandingSurface,
};

/// This driver's name at the plate mouth: `.local/artifacts/eros_audio_inscription/<name>-<sha256>.form`.
const FORM_DRIVER: &str = "eros_audio_inscription";
/// The two live-current rests this driver seals, at its two named passages. `ERST` reads both.
const SUCCESSOR_REST_FORM: &str = "successor-rest";
const PREFLIGHT_REST_FORM: &str = "preflight-rest";

const PREFLIGHT_RANKS: [u32; 3] = [6, 7, 8];
const PREFLIGHT_WORD: &str = "zero";
const AUDIO_CURRENTS: usize = PREFLIGHT_RANKS.len() * 2 * 2;
const PAIRED_CURRENTS: usize = AUDIO_CURRENTS + 1;
const ACOUSTIC_RECEIVER: usize = 4;

#[derive(Clone, Copy)]
struct ClipSpec {
    digit: u8,
    speaker: &'static str,
    recording: u8,
}

impl ClipSpec {
    fn path(self) -> PathBuf {
        audio_root()
            .join("audiomnist-src/data")
            .join(self.speaker)
            .join(format!(
                "{}_{}_{}.wav",
                self.digit, self.speaker, self.recording
            ))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct MemoryRead {
    standing_cells: usize,
    standing_constituents: usize,
    constituent_cells: usize,
    constituent_incidences: usize,
    constituent_pins: usize,
    constituent_paths: usize,
    constituent_transport_terms: usize,
    live_lineages: usize,
    carrier_words: usize,
    overflow_nodes: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct ShapeRead {
    grain: u32,
    axes: u32,
    cells: usize,
    incidences: usize,
    pins: usize,
    boundaries: usize,
    paths: usize,
    folded_paths: usize,
    transport_terms: usize,
    exposed_pins: usize,
    open_boundaries: usize,
    ride_boundaries: usize,
    found_boundaries: usize,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize)]
struct ContactRead {
    open: usize,
    ride: usize,
    found_this: usize,
    found_that: usize,
    dark: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct AcousticEventRead {
    role: &'static str,
    source_path: String,
    source_sha256: String,
    digit: u8,
    speaker: &'static str,
    recording: u8,
    inscription: Option<String>,
    samples: usize,
    reconstruction_exact: bool,
    currents: usize,
    regional_arcs: usize,
    touched_predecessors: Vec<usize>,
    contacts: ContactRead,
    elapsed_microseconds: u128,
    emitted: ShapeRead,
    before: MemoryRead,
    after: MemoryRead,
    successor_rest_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct RecurrenceFixtureRead {
    admitted_ranks: [u32; 3],
    acoustic_receiver: &'static str,
    seed: &'static str,
    exact_repeat: &'static str,
    alternate_recording: &'static str,
    held_speaker: &'static str,
    seed_inscription: &'static str,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct RecurrenceReport {
    schema: &'static str,
    status: &'static str,
    stop_boundary: &'static str,
    fixture: RecurrenceFixtureRead,
    rest_remount_exact: bool,
    seed: AcousticEventRead,
    exact_repeat: AcousticEventRead,
    alternate_recording: Option<AcousticEventRead>,
    held_speaker: Option<AcousticEventRead>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct SheetRead {
    direction: &'static str,
    rank: u32,
    kind: &'static str,
    values: usize,
    cells: usize,
    incidences: usize,
    exposed_ports: usize,
}

#[derive(Clone, Debug, Serialize)]
struct PreflightReport {
    schema: &'static str,
    status: &'static str,
    source_path: String,
    source_sha256: String,
    channels: u16,
    bits_per_sample: u16,
    sample_rate: u32,
    samples: usize,
    admitted_ranks: [u32; 3],
    forward_reconstruction_exact: bool,
    reverse_reconstruction_exact: bool,
    sheets: Vec<SheetRead>,
    currents: usize,
    regional_arcs: usize,
    elapsed_microseconds: u128,
    emitted: ShapeRead,
    memory: MemoryRead,
    rest_sha256: String,
}

struct ChartSpec {
    direction: &'static str,
    rank: u32,
    kind: &'static str,
    chart: ExactPathChart,
}

#[derive(Clone, Copy)]
struct PairedCharts {
    sum: usize,
    difference: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct AudioCheckpoint {
    machine: LiveCurrentRestImage,
    organs: Vec<NativeRelationOrganImage>,
}

struct AudioWorld {
    machine: LiveCurrentMachine,
    organs: Vec<NativeRelationOrgan>,
}

impl AudioWorld {
    fn new() -> Result<Self, String> {
        Ok(Self {
            machine: LiveCurrentMachine::new(SparseStandingSurface::empty_rank(10).map_err(debug)?),
            organs: (0..PAIRED_CURRENTS)
                .map(|_| NativeRelationOrgan::new())
                .collect(),
        })
    }

    fn from_checkpoint(checkpoint: &AudioCheckpoint) -> Result<Self, String> {
        let machine =
            LiveCurrentMachine::from_rest_image(checkpoint.machine.clone()).map_err(debug)?;
        let organs = checkpoint
            .organs
            .iter()
            .copied()
            .map(|image| NativeRelationOrgan::recover(image, &machine).map_err(debug))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self { machine, organs })
    }

    fn checkpoint(&self) -> Result<AudioCheckpoint, String> {
        Ok(AudioCheckpoint {
            machine: self.machine.rest_image().map_err(debug)?,
            organs: self
                .organs
                .iter()
                .map(NativeRelationOrgan::checkpoint)
                .collect(),
        })
    }

    fn present(
        &mut self,
        clip: ClipSpec,
        inscription: Option<&str>,
        role: &'static str,
    ) -> Result<AcousticEventRead, String> {
        let source = clip.path();
        let source_bytes = std::fs::read(&source)
            .map_err(|error| format!("{} reads completely: {error}", source.display()))?;
        let wave = PcmWave::read(&source)?;
        if wave.sample_rate != 48_000 {
            return Err(format!(
                "{} sample rate is {}, expected source-native 48000",
                source.display(),
                wave.sample_rate
            ));
        }
        let atlas = ButterflyAtlas::new(&wave.samples)?;
        let (forward_exact, reverse_exact) = atlas.reconstructs(&wave.samples)?;
        if !forward_exact || !reverse_exact {
            return Err(format!(
                "{} failed exact forward/reverse reconstruction",
                source.display()
            ));
        }
        let (mut specs, pairs) = chart_specs(&atlas)?;
        let text = if let Some(text) = inscription {
            let at = specs.len();
            specs.push(ChartSpec {
                direction: "inscription",
                rank: 0,
                kind: "utf8-path",
                chart: ExactPathChart::new(
                    &text
                        .as_bytes()
                        .iter()
                        .copied()
                        .map(i64::from)
                        .collect::<Vec<_>>(),
                )?,
            });
            Some(at)
        } else {
            None
        };
        if specs.len() > self.organs.len() {
            return Err(format!(
                "event needs {} organs but the bounded audio world carries {}",
                specs.len(),
                self.organs.len()
            ));
        }
        let arcs = regional_arcs(&specs, &pairs, text)?;
        let before = memory_read(self.machine.memory());
        let mut currents = Vec::with_capacity(specs.len());
        for (organ, spec) in self.organs.iter_mut().zip(&specs) {
            currents.push(NativeEventCurrent::continuing_complex(
                organ,
                spec.chart.complex(),
                action(),
            ));
        }
        let regional = [NativeRegionalRelation::new(ACOUSTIC_RECEIVER, &arcs)];
        let mut witness = WitnessCpu::default();
        let started = Instant::now();
        let radiation = present_native_event_with_regional(
            &mut self.machine,
            &mut witness,
            &mut currents,
            &[],
            &regional,
        )
        .map_err(debug)?;
        let elapsed_microseconds = started.elapsed().as_micros();
        let touched_predecessors = witness.one_touched()?;
        let region = radiation
            .regional()
            .first()
            .ok_or_else(|| "the acoustic event returned no regional constituent".to_owned())?;
        let rest = self.machine.rest_image().map_err(debug)?;
        let successor_rest_octets = rest.encode_native_bytes().map_err(debug)?;
        // THE_ASSEMBLY.md step 5, loop (d): *the signal is the octets*. The hash below is untouched
        // and still reported; these are the same octets reaching the plate's mouth instead of being
        // hashed and dropped. This runs at every acoustic event; the address is the content, so
        // every distinct rest is deposited at its own address rather than overwriting the previous.
        let deposited =
            deposit_form_or_message(FORM_DRIVER, SUCCESSOR_REST_FORM, &successor_rest_octets)?;
        eprintln!("form deposited: {}", deposited.path.display());
        Ok(AcousticEventRead {
            role,
            source_path: source.display().to_string(),
            source_sha256: sha256(&source_bytes),
            digit: clip.digit,
            speaker: clip.speaker,
            recording: clip.recording,
            inscription: inscription.map(str::to_owned),
            samples: wave.samples.len(),
            reconstruction_exact: forward_exact && reverse_exact,
            currents: specs.len(),
            regional_arcs: arcs.len(),
            touched_predecessors,
            contacts: contact_read(region.arcs()),
            elapsed_microseconds,
            emitted: shape_read(region.constituent()),
            before,
            after: memory_read(self.machine.memory()),
            successor_rest_sha256: sha256(&successor_rest_octets),
        })
    }
}

#[derive(Default)]
struct WitnessCpu {
    cpu: CpuLiveCurrentExecutor,
    touched: Vec<Vec<usize>>,
}

impl WitnessCpu {
    fn one_touched(&self) -> Result<Vec<usize>, String> {
        match self.touched.as_slice() {
            [one] => Ok(one.clone()),
            _ => Err(format!(
                "one acoustic region produced {} touched populations",
                self.touched.len()
            )),
        }
    }
}

impl LiveCurrentExecutor for WitnessCpu {
    fn enact(
        &mut self,
        physical_revision: u64,
        standing: &SparseStandingSurface,
        currents: &[CurrentExecutionRequest<'_>],
        relations: &[DirectedExecutionRequest],
        regional: &[RegionalExecutionRequest<'_>],
    ) -> Result<ExecutedContemporaryEvent, LiveCurrentError> {
        let executed =
            self.cpu
                .enact(physical_revision, standing, currents, relations, regional)?;
        self.touched.clear();
        self.touched
            .try_reserve_exact(executed.regional().len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        for region in executed.regional() {
            self.touched.push(region.touched().to_vec());
        }
        Ok(executed)
    }

    fn settle_physical_successor(
        &mut self,
        physical_revision: u64,
        successor: &SparseStandingSurface,
    ) -> Result<(), LiveCurrentError> {
        self.cpu
            .settle_physical_successor(physical_revision, successor)
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros audio inscription: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let mode = arguments
        .next()
        .and_then(|value| value.into_string().ok())
        .ok_or_else(usage)?;
    let output = PathBuf::from(arguments.next().ok_or_else(usage)?);
    if arguments.next().is_some() {
        return Err(usage());
    }
    match mode.as_str() {
        "preflight" => {
            let source = ClipSpec {
                digit: 0,
                speaker: "01",
                recording: 0,
            }
            .path();
            let report = preflight(&source)?;
            write_new_json(&output, &report)?;
            eprintln!(
                "eros audio inscription: {} · {} samples · {} arcs · {} us · {}",
                report.status,
                report.samples,
                report.regional_arcs,
                report.elapsed_microseconds,
                output.display()
            );
            Ok(())
        }
        "recurrence" => {
            let report = recurrence()?;
            write_new_json(&output, &report)?;
            eprintln!(
                "eros audio inscription: {} · {} · {}",
                report.status,
                report.stop_boundary,
                output.display()
            );
            Ok(())
        }
        _ => Err(usage()),
    }
}

fn usage() -> String {
    "usage: eros_audio_inscription <preflight|recurrence> <new-report.json>".to_owned()
}

fn recurrence() -> Result<RecurrenceReport, String> {
    let seed_clip = ClipSpec {
        digit: 0,
        speaker: "01",
        recording: 0,
    };
    let exact_clip = seed_clip;
    let alternate_clip = ClipSpec {
        recording: 1,
        ..seed_clip
    };
    let held_clip = ClipSpec {
        speaker: "02",
        recording: 0,
        ..seed_clip
    };
    let fixture = RecurrenceFixtureRead {
        admitted_ranks: PREFLIGHT_RANKS,
        acoustic_receiver: "forward rank-8 sum current",
        seed: "0_01_0.wav",
        exact_repeat: "0_01_0.wav",
        alternate_recording: "0_01_1.wav",
        held_speaker: "0_02_0.wav",
        seed_inscription: PREFLIGHT_WORD,
    };

    let mut world = AudioWorld::new()?;
    let seed = world.present(seed_clip, Some(PREFLIGHT_WORD), "paired-seed")?;
    let checkpoint = world.checkpoint()?;
    let remounted = AudioWorld::from_checkpoint(&checkpoint)?;
    let rest_remount_exact = remounted.checkpoint()? == checkpoint;
    if !rest_remount_exact {
        return Err("the paired acoustic world changed across exact rest/remount".to_owned());
    }

    let mut exact_world = AudioWorld::from_checkpoint(&checkpoint)?;
    let exact_repeat = exact_world.present(exact_clip, None, "audio-only-exact-repeat")?;
    if exact_repeat.touched_predecessors.is_empty() {
        return Ok(RecurrenceReport {
            schema: "eros.audio-inscription.recurrence.v1",
            status: "standing-obstruction",
            stop_boundary: "an exact audio-only repeat did not recruit the paired predecessor",
            fixture,
            rest_remount_exact,
            seed,
            exact_repeat,
            alternate_recording: None,
            held_speaker: None,
        });
    }

    let mut alternate_world = AudioWorld::from_checkpoint(&checkpoint)?;
    let alternate_recording = alternate_world.present(
        alternate_clip,
        None,
        "audio-only-same-speaker-alternate-recording",
    )?;
    if alternate_recording.touched_predecessors.is_empty() {
        return Ok(RecurrenceReport {
            schema: "eros.audio-inscription.recurrence.v1",
            status: "exact-recurrence-only",
            stop_boundary: "exact repetition recruited Standing but a nonidentical same-speaker recording did not",
            fixture,
            rest_remount_exact,
            seed,
            exact_repeat,
            alternate_recording: Some(alternate_recording),
            held_speaker: None,
        });
    }

    let mut held_world = AudioWorld::from_checkpoint(&checkpoint)?;
    let held_speaker = held_world.present(held_clip, None, "audio-only-held-speaker-same-word")?;
    let (status, stop_boundary) = if held_speaker.touched_predecessors.is_empty() {
        (
            "same-speaker-recurrence",
            "nonidentical recurrence crossed within one speaker but not across the fixed held speaker",
        )
    } else {
        (
            "speaker-disjoint-recurrence",
            "exact, nonidentical same-speaker, and held-speaker sound all recruited the paired predecessor",
        )
    };
    Ok(RecurrenceReport {
        schema: "eros.audio-inscription.recurrence.v1",
        status,
        stop_boundary,
        fixture,
        rest_remount_exact,
        seed,
        exact_repeat,
        alternate_recording: Some(alternate_recording),
        held_speaker: Some(held_speaker),
    })
}

fn preflight(source: &Path) -> Result<PreflightReport, String> {
    let source_bytes = std::fs::read(source)
        .map_err(|error| format!("{} reads completely: {error}", source.display()))?;
    let wave = PcmWave::read(source)?;
    if wave.sample_rate != 48_000 {
        return Err(format!(
            "{} sample rate is {}, expected source-native 48000",
            source.display(),
            wave.sample_rate
        ));
    }
    let atlas = ButterflyAtlas::new(&wave.samples)?;
    let (forward_exact, reverse_exact) = atlas.reconstructs(&wave.samples)?;
    if !forward_exact || !reverse_exact {
        return Err("the exact butterfly failed source reconstruction".to_owned());
    }

    let (mut specs, pairs) = chart_specs(&atlas)?;
    let text_index = specs.len();
    specs.push(ChartSpec {
        direction: "inscription",
        rank: 0,
        kind: "utf8-path",
        chart: ExactPathChart::new(
            &PREFLIGHT_WORD
                .as_bytes()
                .iter()
                .copied()
                .map(i64::from)
                .collect::<Vec<_>>(),
        )?,
    });
    let arcs = regional_arcs(&specs, &pairs, Some(text_index))?;

    let mut machine =
        LiveCurrentMachine::new(SparseStandingSurface::empty_rank(10).map_err(debug)?);
    let mut organs: Vec<NativeRelationOrgan> = (0..specs.len())
        .map(|_| NativeRelationOrgan::new())
        .collect();
    let mut currents = Vec::with_capacity(specs.len());
    for (organ, spec) in organs.iter_mut().zip(&specs) {
        currents.push(NativeEventCurrent::ending_complex(
            organ,
            spec.chart.complex(),
            action(),
        ));
    }
    let regional = [NativeRegionalRelation::new(ACOUSTIC_RECEIVER, &arcs)];
    let mut cpu = CpuLiveCurrentExecutor;
    let started = Instant::now();
    let radiation =
        present_native_event_with_regional(&mut machine, &mut cpu, &mut currents, &[], &regional)
            .map_err(debug)?;
    let elapsed_microseconds = started.elapsed().as_micros();
    let constituent = radiation
        .regional()
        .first()
        .ok_or_else(|| "the preflight returned no regional constituent".to_owned())?
        .constituent();
    let rest = machine.rest_image().map_err(debug)?;
    let preflight_rest_octets = rest.encode_native_bytes().map_err(debug)?;
    // THE_ASSEMBLY.md step 5, loop (d): *the signal is the octets*. The hash below is untouched.
    let deposited =
        deposit_form_or_message(FORM_DRIVER, PREFLIGHT_REST_FORM, &preflight_rest_octets)?;
    eprintln!("form deposited: {}", deposited.path.display());

    Ok(PreflightReport {
        schema: "eros.audio-inscription.preflight.v1",
        status: "carrier-closed",
        source_path: source.display().to_string(),
        source_sha256: sha256(&source_bytes),
        channels: 1,
        bits_per_sample: 16,
        sample_rate: wave.sample_rate,
        samples: wave.samples.len(),
        admitted_ranks: PREFLIGHT_RANKS,
        forward_reconstruction_exact: forward_exact,
        reverse_reconstruction_exact: reverse_exact,
        sheets: specs
            .iter()
            .map(|spec| SheetRead {
                direction: spec.direction,
                rank: spec.rank,
                kind: spec.kind,
                values: (spec.chart.cells() + 1) / 2,
                cells: spec.chart.cells(),
                incidences: spec.chart.incidences(),
                exposed_ports: spec.chart.exposed(),
            })
            .collect(),
        currents: specs.len(),
        regional_arcs: arcs.len(),
        elapsed_microseconds,
        emitted: shape_read(constituent),
        memory: memory_read(machine.memory()),
        rest_sha256: sha256(&preflight_rest_octets),
    })
}

fn chart_specs(atlas: &ButterflyAtlas) -> Result<(Vec<ChartSpec>, Vec<PairedCharts>), String> {
    let mut specs = Vec::new();
    let mut pairs = Vec::new();
    for (direction, directed) in [("forward", &atlas.forward), ("reverse", &atlas.reverse)] {
        for rank in PREFLIGHT_RANKS {
            let sheet = directed
                .sheet(rank)
                .ok_or_else(|| format!("source has no complete rank-{rank} butterfly sheet"))?;
            if sheet.sums.len() < 2 || sheet.differences.len() < 2 {
                return Err(format!(
                    "rank-{rank} {direction} sheet has fewer than two values"
                ));
            }
            let sum = specs.len();
            specs.push(ChartSpec {
                direction,
                rank,
                kind: "sum",
                chart: ExactPathChart::new(&sheet.sums)?,
            });
            let difference = specs.len();
            specs.push(ChartSpec {
                direction,
                rank,
                kind: "difference",
                chart: ExactPathChart::new(&sheet.differences)?,
            });
            pairs.push(PairedCharts { sum, difference });
        }
    }
    Ok((specs, pairs))
}

fn regional_arcs(
    specs: &[ChartSpec],
    pairs: &[PairedCharts],
    text: Option<usize>,
) -> Result<Vec<NativeRegionalArc>, String> {
    let mut arcs = Vec::new();
    let mut boundary_slot = 0u32;
    for pair in pairs {
        let count = specs[pair.sum]
            .chart
            .exposed()
            .min(specs[pair.difference].chart.exposed());
        for port in 0..count {
            arcs.push(NativeRegionalArc::new(
                pair.sum,
                CurrentBoundaryPort::Exposed(port as u32),
                pair.difference,
                CurrentBoundaryPort::Exposed(port as u32),
                InterfaceCapability::new(0x4155_4449_4f, boundary_slot as u64),
                boundary_slot,
                0,
                IncidenceHand::Against,
            ));
            boundary_slot = boundary_slot
                .checked_add(1)
                .ok_or_else(|| "regional boundary slots exceeded u32".to_owned())?;
        }
    }
    if let Some(text) = text {
        for pair in [pairs.first(), pairs.get(PREFLIGHT_RANKS.len())]
            .into_iter()
            .flatten()
        {
            arcs.push(NativeRegionalArc::new(
                pair.sum,
                CurrentBoundaryPort::Exposed(0),
                text,
                CurrentBoundaryPort::Exposed(0),
                InterfaceCapability::new(0x4155_4449_4f, boundary_slot as u64),
                boundary_slot,
                0,
                IncidenceHand::Against,
            ));
            boundary_slot = boundary_slot
                .checked_add(1)
                .ok_or_else(|| "regional boundary slots exceeded u32".to_owned())?;
        }
    }
    Ok(arcs)
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("one is a resolving audio-world action")
}

fn shape_read(constituent: &LiveConstituent) -> ShapeRead {
    let mut paths = 0usize;
    let mut folded_paths = 0usize;
    let mut transport_terms = 0usize;
    let mut open_boundaries = 0usize;
    let mut ride_boundaries = 0usize;
    let mut found_boundaries = 0usize;
    for (at, boundary) in constituent.boundaries().iter().enumerate() {
        match constituent.boundary_transition(at) {
            Some(LiveBoundaryTransition::Open) => open_boundaries += 1,
            Some(LiveBoundaryTransition::Ride) => ride_boundaries += 1,
            Some(LiveBoundaryTransition::Found) => found_boundaries += 1,
            None => {}
        }
        paths += boundary.paths().len();
        for path in boundary.paths() {
            folded_paths += usize::from(path.interior_folded());
            transport_terms += path.transport().terms().len();
        }
    }
    ShapeRead {
        grain: constituent.grain(),
        axes: constituent.axis_count(),
        cells: constituent.cells().len(),
        incidences: constituent.incidences().len(),
        pins: constituent.pins().len(),
        boundaries: constituent.boundaries().len(),
        paths,
        folded_paths,
        transport_terms,
        exposed_pins: constituent.exposed().len(),
        open_boundaries,
        ride_boundaries,
        found_boundaries,
    }
}

fn contact_read(arcs: &[RegionalArcRadiation]) -> ContactRead {
    let mut read = ContactRead::default();
    for arc in arcs {
        match arc.contact().emission.map(|emission| emission.deed) {
            None => read.open += 1,
            Some(FeltDeed::Ride) => read.ride += 1,
            Some(FeltDeed::FoundThis) => read.found_this += 1,
            Some(FeltDeed::FoundThat) => read.found_that += 1,
            Some(FeltDeed::Dark) => read.dark += 1,
        }
    }
    read
}

fn memory_read(memory: LiveMemory) -> MemoryRead {
    MemoryRead {
        standing_cells: memory.standing_cells,
        standing_constituents: memory.standing_constituents,
        constituent_cells: memory.constituent_cells,
        constituent_incidences: memory.constituent_incidences,
        constituent_pins: memory.constituent_pins,
        constituent_paths: memory.constituent_paths,
        constituent_transport_terms: memory.constituent_transport_terms,
        live_lineages: memory.live_lineages,
        carrier_words: memory.carrier_words,
        overflow_nodes: memory.overflow_nodes,
    }
}

fn audio_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../experiments/corpora/audio-src")
}

fn write_new_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    let mut bytes = serde_json::to_vec_pretty(value)
        .map_err(|error| format!("report does not encode: {error}"))?;
    bytes.push(b'\n');
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| format!("{} opens as a new report: {error}", path.display()))?;
    file.write_all(&bytes)
        .map_err(|error| format!("{} writes completely: {error}", path.display()))?;
    file.sync_all()
        .map_err(|error| format!("{} syncs completely: {error}", path.display()))
}

fn sha256(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(64);
    for byte in digest {
        encoded.push(HEX[(byte >> 4) as usize] as char);
        encoded.push(HEX[(byte & 0x0f) as usize] as char);
    }
    encoded
}

fn debug(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}
