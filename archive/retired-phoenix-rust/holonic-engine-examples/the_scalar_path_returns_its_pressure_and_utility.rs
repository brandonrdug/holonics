//! **Deed H0 — the existing scalar path returns its physical profile.** The committed one-input
//! closure of the layer-by-layer tower is conducted for its first two layers, and everything the
//! passage already returns about the deed is written out as readable receipts: the causal front
//! population with its certificates, footprints and cover; the exact semantic work with its
//! admission coordinates; and the local pressure faces — current against capacity, per site, per
//! resource species, never summed.
//!
//! ```text
//!   --receipts                 the semantic half; needs the card
//!     source + mode identity  → source-and-mode.form
//!     fronts of layer 1       → causal-fronts.form      (layer 0 marked predecessor)
//!     exact work + admission  → exact-work.form
//!     current against capacity→ pressure.form
//!
//!   --join --telemetry-dir D   the exterior half; needs no card
//!     A's .tsv faces + the four forms above
//!                             → surface-utility.form    (product-ordered, four blocks)
//!                             → profile.form            (the rubric, applied as code)
//!                             → pressure-joined.form    (the demand columns telemetry supplies)
//! ```
//!
//! **Layer 1 is the representative layer**, not layer 0: it is a sliding-species layer that enters
//! on a CARRIED standing rather than on rows, owns its own K and V, and is therefore the shape 34
//! of the tower's 42 layers have. Layer 0 is conducted only because layer 1's entry is layer 0's
//! return, and it is written out as the predecessor it is.
//!
//! **No semantic code changed for this driver.** It composes `front_passage`, `receiver_current`
//! (through the passage's own traffic reading), `exact_work`, `hardware_cover` and the two Phoenix
//! sites; it founds no owner and it changes nothing under `src/`, `soma/` or `kernels/`.
//!
//! **What is measurement and what is not.** Every number in `--receipts` was returned by a struct
//! the passage handed back or by the device answering `cuDeviceGetAttribute`. Every number in
//! `--join` was read out of a `.tsv` the exterior profiling receiver wrote. A quantity that neither
//! supplies is written `unknown` — never `0`, never interpolated, never inferred from a neighbour.
//! Elapsed times are apparatus measurements and carry the frame they were taken in; they select
//! nothing.
//!
//! Run:
//! ```text
//! PATH=/opt/cuda/bin:$PATH ./target/release/examples/the_scalar_path_returns_its_pressure_and_utility --receipts
//! ./target/release/examples/the_scalar_path_returns_its_pressure_and_utility --join \
//!     --telemetry-dir output/the_scalar_path_returns_its_pressure_and_utility
//! ```

#[path = "phoenix/profile.rs"]
mod profile;
#[path = "phoenix/resident_layer.rs"]
mod resident_layer;
#[path = "phoenix/tower.rs"]
mod tower;

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::time::Instant;

use holonic_engine::causal::EventId;
use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::exact_work::ExactWork;
use holonic_engine::front_passage::{
    ApparatusPrediction, Ceiling, CoordinateAdmission, DeedAdmission, DeedReceiver,
    FrontDeedReading, FrontPassage, FrontPassageObstruction, FrontReceipt, MaterialAdmission,
    ResidentMaterial, TrafficReading,
};
use holonic_engine::hardware_cover::ModeIdentity;
use holonic_engine::interaction::{OccurrencePort, PortHand};
use holonic_engine::resident_section::{
    ResidentGrain, ResidentSection, ResidentSurface, Schedule, SeriesAperture,
};
use holonic_engine::source_occurrence::{RegionIdentity, SourceOccurrence};
use resident_layer::Source;
use tower::{Entry, Intervention, KvRole, Species};

// ---------------------------------------------------------------------------------------------
// the closure, as flags
// ---------------------------------------------------------------------------------------------

/// The committed Station C one-input closure, reused verbatim so no exterior tokenizer runs.
const CLOSURE_TOKENS: [usize; 5] = [818, 5279, 529, 7001, 563];
const CLOSURE_TEXT: &str = "The capital of France is";
const CLOSURE_GRAIN: u32 = 48;
const CLOSURE_TERMS: u32 = 14;
/// Layer 1 is the representative layer; layer 0 is conducted to produce its entry.
const LAYERS_CONDUCTED: [usize; 2] = [0, 1];
const REPRESENTATIVE_LAYER: usize = 1;

struct Args {
    receipts: bool,
    join: bool,
    root: String,
    out: PathBuf,
    telemetry: Option<PathBuf>,
    tokens: Vec<usize>,
    grain: u32,
    terms: u32,
    chart: tower::Chart,
    content_digest: bool,
}

fn parse_args() -> Args {
    let mut args = Args {
        receipts: false,
        join: false,
        root: "/home/b/models/gemma-4-E4B-it".to_owned(),
        out: PathBuf::from("output/the_scalar_path_returns_its_pressure_and_utility"),
        telemetry: None,
        tokens: CLOSURE_TOKENS.to_vec(),
        grain: CLOSURE_GRAIN,
        terms: CLOSURE_TERMS,
        chart: tower::Chart::Midpoint,
        content_digest: true,
    };
    let mut it = std::env::args().skip(1);
    while let Some(flag) = it.next() {
        match flag.as_str() {
            "--receipts" => args.receipts = true,
            "--join" => args.join = true,
            "--root" => args.root = it.next().expect("--root <dir>"),
            "--out" => args.out = PathBuf::from(it.next().expect("--out <dir>")),
            "--telemetry-dir" => {
                args.telemetry = Some(PathBuf::from(it.next().expect("--telemetry-dir <dir>")))
            }
            "--tokens" => {
                args.tokens = it
                    .next()
                    .expect("--tokens a,b,c")
                    .split(',')
                    .map(|t| t.trim().parse().expect("token id"))
                    .collect()
            }
            "--grain" => args.grain = it.next().expect("--grain F").parse().expect("u32"),
            "--terms" => args.terms = it.next().expect("--terms N").parse().expect("u32"),
            "--chart" => {
                args.chart = match it.next().expect("--chart interval|midpoint").as_str() {
                    "interval" => tower::Chart::Interval,
                    "midpoint" => tower::Chart::Midpoint,
                    other => panic!("unknown chart {other}"),
                }
            }
            "--no-content-digest" => args.content_digest = false,
            other => panic!("unknown argument {other}"),
        }
    }
    if !args.receipts && !args.join {
        args.receipts = true;
    }
    args
}

fn describe(obstruction: &FrontPassageObstruction) -> String {
    match obstruction {
        FrontPassageObstruction::Cover { front, barriers } => {
            format!("CoverBarrier at front {front}: {barriers:?}")
        }
        FrontPassageObstruction::Interchange { front, because, .. } => {
            format!("InterchangeRefusal at front {front}: {because:?}")
        }
        FrontPassageObstruction::Resource(resource) => format!("ResourceObstruction: {resource:?}"),
        FrontPassageObstruction::Compile(refusal) => format!("CompileRefusal: {refusal}"),
        FrontPassageObstruction::Sealed {
            occurrence,
            quotient,
            reopening,
        } => format!(
            "the section at {occurrence:?} was sealed away by the fused quotient {quotient:?}; {reopening}"
        ),
        FrontPassageObstruction::Refused {
            occurrence,
            operation,
            refusal,
            lineage,
            ..
        } => {
            format!(
                "the card refused at {occurrence:?} ({operation}): {refusal}; lineage {:?}",
                lineage.refusals
            )
        }
    }
}

/// One expensive step, with the frame the measurement was taken in.
struct Clockings(Vec<(String, f64, String)>);

impl Clockings {
    fn record(&mut self, what: &str, elapsed: f64, status: &str) {
        println!("    [{elapsed:>8.3} s] {what} — {status}");
        self.0.push((what.to_owned(), elapsed, status.to_owned()));
    }
}

// ---------------------------------------------------------------------------------------------
// what one conducted layer hands back
// ---------------------------------------------------------------------------------------------

struct LayerProfile {
    layer: usize,
    species: Species,
    role: KvRole,
    entry: Entry,
    fronts: Vec<FrontReceipt>,
    /// the measured half the deed returned, front by front
    readings: Vec<FrontDeedReading>,
    /// occurrence → (operation name as the kernel plan names it, law name as the complex names it)
    names: BTreeMap<EventId, (String, String)>,
    /// occurrence → its producers, as occurrences
    producers: BTreeMap<EventId, Vec<EventId>>,
    /// occurrence → the named bonds arriving at it: (bond name, source port, target port)
    arriving: BTreeMap<EventId, Vec<(String, OccurrencePort, OccurrencePort)>>,
    /// occurrence → (rows, width, resident octets) of the section it writes
    extents: BTreeMap<EventId, (usize, usize, u64)>,
    /// occurrence → the a-priori octave bound admitted on its output port
    octaves: BTreeMap<EventId, u32>,
    traffic: TrafficReading,
    deed: ExactWork,
    apparatus: ApparatusPrediction,
    admission: DeedAdmission,
    material: MaterialAdmission,
    graph_nodes: usize,
    graph_edges: usize,
    graph_kernel_nodes: usize,
    graph_memset_nodes: usize,
    graph_memcpy_nodes: usize,
    graph_other_nodes: usize,
    intended_nodes: usize,
    intended_edges: usize,
    schedule: Schedule,
    stood: bool,
    measured_octaves: usize,
    a_priori_held: bool,
    mount_wall_s: f64,
    bind_wall_s: f64,
    launch_wall_s: f64,
}

impl LayerProfile {
    fn members(&self) -> usize {
        self.fronts.iter().map(|f| f.members.len()).sum()
    }
    fn plural_fronts(&self) -> usize {
        self.fronts.iter().filter(|f| f.members.len() >= 2).count()
    }
}

fn port_name(port: &OccurrencePort) -> String {
    let hand = match port.hand {
        PortHand::Input => "in",
        PortHand::Output => "out",
    };
    format!("e{}:{hand}{}", port.event.0, port.ordinal)
}

// ---------------------------------------------------------------------------------------------
// MODE 1 — the semantic half, on the card
// ---------------------------------------------------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn conduct_layers(
    surface: &'static ResidentSurface<'static>,
    readout: &'static ResidentReadout,
    source: &mut Source,
    root: &str,
    header_regions: &BTreeMap<String, RegionIdentity>,
    content_sha256: Option<&str>,
    tokens: &[usize],
    grain: ResidentGrain,
    terms: SeriesAperture,
    chart: tower::Chart,
    clock: &mut Clockings,
) -> Result<(Vec<LayerProfile>, SourceOccurrence), String> {
    let passage = FrontPassage::new(surface, grain);
    let receiver = DeedReceiver::unbounded();
    let scales = tower::algebraic_scales()?;
    let mut regions = header_regions.clone();
    let mut carried: Option<(Rc<ResidentSection<'static>>, u32)> = None;
    let sliding_bands = tower::found_bands(Species::Sliding, resident_layer::BAND_TERMS)?;
    let full_bands = tower::found_bands(Species::Full, resident_layer::BAND_TERMS)?;
    let positions: Vec<u32> = (0..tokens.len() as u32).collect();
    let mut profiles: Vec<LayerProfile> = Vec::new();
    let mut last_occurrence: Option<SourceOccurrence> = None;

    for layer in LAYERS_CONDUCTED {
        let species = Species::of(layer);
        let role = KvRole::of(layer);
        let mut material = ResidentMaterial::empty();
        let plan = tower::material_plan(source, layer, tokens.len())?;
        let prediction = passage.predict_material(&plan);
        let admission: MaterialAdmission = passage
            .admit_material(&prediction)
            .map_err(|o| format!("layer {layer} material refused: {}", describe(&o)))?;

        let mount_clock = Instant::now();
        let mount = tower::mount_layer(source, readout, &mut material, layer)?;
        let mount_wall_s = mount_clock.elapsed().as_secs_f64();
        clock.record(
            &format!(
                "layer {layer}: mount {} populations from the source",
                mount.populations
            ),
            mount_wall_s,
            "mounted",
        );
        for (name, region) in mount.regions {
            regions.insert(name, region);
        }
        let layer_scalar = mount.layer_scalar.ok_or("layer_scalar")?;
        let bands = match species {
            Species::Sliding => &sliding_bands,
            Species::Full => &full_bands,
        };
        let mounted_bands = surface
            .mount_bands(bands, tower::BAND_GRAIN)
            .map_err(|e| e.to_string())?;
        material.bands.insert(
            species.bands().to_owned(),
            (mounted_bands, (tokens.len() - 1) as u32),
        );
        material.positions = Some(
            surface
                .mount_positions(&positions)
                .map_err(|e| e.to_string())?,
        );
        tower::enter(source, tokens, layer, &mut material)?;
        let entry = if layer == 0 {
            Entry::Rows
        } else {
            Entry::Carried
        };
        if let Some((section, bound)) = &carried {
            material.standings.insert(
                tower::CARRIED_STANDING.to_owned(),
                (Rc::clone(section), *bound),
            );
        }
        let occurrence: SourceOccurrence = resident_layer::source_occurrence(
            root,
            regions.clone(),
            content_sha256.map(|s| s.to_owned()),
        )?;
        let founded = tower::found_layer(
            layer,
            entry,
            chart,
            &scales,
            terms,
            layer_scalar,
            &Intervention::None,
            tokens.len(),
        )?;

        let bind_clock = Instant::now();
        let mut bound = passage
            .bind(
                &founded.complex,
                &founded.realization,
                &material,
                &occurrence,
                &receiver,
                Some(&admission),
                founded.returns[tower::LAYER_RETURN],
            )
            .map_err(|o| format!("layer {layer} refused at bind: {}", describe(&o)))?;
        let bind_wall_s = bind_clock.elapsed().as_secs_f64();
        clock.record(
            &format!("layer {layer}: compile, admit, allocate and capture the graph"),
            bind_wall_s,
            "bound",
        );

        let launch_clock = Instant::now();
        let returned = bound
            .launch(&surface.mode())
            .map_err(|o| format!("layer {layer} refused at launch: {}", describe(&o)))?;
        let launch_wall_s = launch_clock.elapsed().as_secs_f64();
        clock.record(
            &format!("layer {layer}: one graph launch and one synchronize"),
            launch_wall_s,
            if returned.stands() {
                "stood"
            } else {
                "REFUSED somewhere"
            },
        );

        let stood = bound.standing(&returned).is_ok();
        let mut a_priori_held = true;
        for (port, measured) in &returned.measured_octaves {
            let b = bound.octave_field.get(port).copied().unwrap_or(0);
            if b < *measured {
                a_priori_held = false;
            }
        }
        let (census, intended) = bound.graph();
        let (graph_nodes, graph_edges) = (census.nodes, census.edges);
        let (graph_kernel_nodes, graph_memset_nodes, graph_memcpy_nodes, graph_other_nodes) = (
            census.kernel_nodes,
            census.memset_nodes,
            census.memcpy_nodes,
            census.other_nodes,
        );

        // every name, extent, octave bound and predecessor — taken from the bound passage before
        // it is released
        let mut names: BTreeMap<EventId, (String, String)> = BTreeMap::new();
        let mut producers: BTreeMap<EventId, Vec<EventId>> = BTreeMap::new();
        let mut extents: BTreeMap<EventId, (usize, usize, u64)> = BTreeMap::new();
        let mut octaves: BTreeMap<EventId, u32> = BTreeMap::new();
        for receipt in bound.fronts() {
            for (event, operation) in &receipt.members {
                let law = founded
                    .complex
                    .shape
                    .occurrences
                    .get(event)
                    .and_then(|o| founded.complex.shape.laws.get(&o.law))
                    .map(|l| l.name.clone())
                    .unwrap_or_else(|| "unknown".to_owned());
                names.insert(*event, ((*operation).to_owned(), law));
                let mut from: Vec<EventId> = Vec::new();
                if let Some(indices) = bound.producers_of(*event) {
                    for index in indices {
                        if let Some(producer) = bound.occurrence_at(*index) {
                            from.push(producer);
                        }
                    }
                }
                producers.insert(*event, from);
                if let Some(section) = bound.section(*event) {
                    extents.insert(
                        *event,
                        (section.rows(), section.width(), section.resident_octets()),
                    );
                }
                if let Some(bound_octave) =
                    bound.octave_field.get(&OccurrencePort::output(*event, 0))
                {
                    octaves.insert(*event, *bound_octave);
                }
            }
        }
        let mut arriving: BTreeMap<EventId, Vec<(String, OccurrencePort, OccurrencePort)>> =
            BTreeMap::new();
        for interaction in founded.complex.shape.interactions.values() {
            for bond in &interaction.bonds {
                arriving.entry(bond.target.event).or_default().push((
                    interaction.name.clone(),
                    bond.source,
                    bond.target,
                ));
            }
        }

        profiles.push(LayerProfile {
            layer,
            species,
            role,
            entry,
            fronts: bound.fronts().to_vec(),
            readings: returned.fronts.clone(),
            names,
            producers,
            arriving,
            extents,
            octaves,
            traffic: bound.traffic.clone(),
            deed: bound.deed_prediction.clone(),
            apparatus: bound.apparatus_prediction.clone(),
            admission: bound.admission.clone(),
            material: admission.clone(),
            graph_nodes,
            graph_edges,
            graph_kernel_nodes,
            graph_memset_nodes,
            graph_memcpy_nodes,
            graph_other_nodes,
            intended_nodes: intended.0,
            intended_edges: intended.1,
            schedule: bound.schedule(),
            stood,
            measured_octaves: returned.measured_octaves.len(),
            a_priori_held,
            mount_wall_s,
            bind_wall_s,
            launch_wall_s,
        });

        let (out, ob) = bound
            .release_section(founded.returns[tower::LAYER_RETURN])
            .ok_or("layer return")?;
        carried = Some((Rc::new(out), ob));
        last_occurrence = Some(occurrence);
        drop(bound);
        drop(material);
    }
    let occurrence = last_occurrence.ok_or("no source occurrence")?;
    Ok((profiles, occurrence))
}

// ---------------------------------------------------------------------------------------------
// the device, answering about itself
// ---------------------------------------------------------------------------------------------

/// Every capacity below was read from the device through `cuDeviceGetAttribute`, by the numeric
/// `CUdevice_attribute` the driver API declares. Nothing here is a remembered specification.
struct DeviceCapacities {
    values: BTreeMap<&'static str, Option<i64>>,
}

const ATTRIBUTES: [(&str, i32); 17] = [
    ("max_threads_per_block", 1),
    ("max_shared_octets_per_block", 8),
    ("warp_size", 10),
    ("max_registers_per_block", 12),
    ("clock_khz", 13),
    ("multiprocessors", 16),
    ("concurrent_kernels", 31),
    ("memory_clock_khz", 36),
    ("global_memory_bus_width_bits", 37),
    ("l2_cache_octets", 38),
    ("max_threads_per_multiprocessor", 39),
    ("async_engine_count", 40),
    ("compute_capability_major", 75),
    ("compute_capability_minor", 76),
    ("max_shared_octets_per_multiprocessor", 81),
    ("max_registers_per_multiprocessor", 82),
    ("max_blocks_per_multiprocessor", 106),
];

fn read_device_capacities() -> DeviceCapacities {
    let mut values: BTreeMap<&'static str, Option<i64>> = BTreeMap::new();
    match mount::Device::get(0) {
        Ok(device) => {
            for (name, raw) in ATTRIBUTES {
                let value = device
                    .attribute(mount::DeviceAttribute::from_raw(raw))
                    .ok()
                    .map(i64::from);
                values.insert(name, value);
            }
        }
        Err(_) => {
            for (name, _) in ATTRIBUTES {
                values.insert(name, None);
            }
        }
    }
    DeviceCapacities { values }
}

impl DeviceCapacities {
    fn get(&self, name: &str) -> Option<i64> {
        self.values.get(name).copied().flatten()
    }
    fn text(&self, name: &str) -> String {
        self.get(name)
            .map(|v| v.to_string())
            .unwrap_or_else(|| profile::UNKNOWN.to_owned())
    }
}

/// An exterior command, quoted with its exit status. Its output is testimony from outside the
/// deed and is labelled so.
fn exterior(command: &str, arguments: &[&str]) -> String {
    match std::process::Command::new(command).args(arguments).output() {
        Ok(output) if output.status.success() => String::from_utf8_lossy(&output.stdout)
            .trim()
            .replace('\n', " | "),
        Ok(output) => format!("{} (exit {})", profile::UNKNOWN, output.status),
        Err(error) => format!("{} ({error})", profile::UNKNOWN),
    }
}

// ---------------------------------------------------------------------------------------------
// MODE 1 — the four forms
// ---------------------------------------------------------------------------------------------

fn write_form(out: &Path, name: &str, body: &str) -> Result<(), String> {
    let path = out.join(name);
    std::fs::write(&path, body).map_err(|e| format!("{}: {e}", path.display()))?;
    println!("  wrote {} ({} octets)", path.display(), body.len());
    Ok(())
}

fn coordinate_line(coordinate: &CoordinateAdmission) -> String {
    match &coordinate.ceiling {
        Ceiling::Bounded {
            ceiling,
            declared_by,
        } => format!(
            "      {:<34} required {:<24} ceiling {:<24} declared_by {declared_by:<28} admitted {}",
            coordinate.name, coordinate.required, ceiling, coordinate.admitted
        ),
        Ceiling::Unbounded {
            because,
            constrained_by,
        } => format!(
            "      {:<34} required {:<24} ceiling UNBOUNDED because {because}; constrained_by {constrained_by:?}",
            coordinate.name, coordinate.required
        ),
    }
}

fn source_and_mode_form(
    commit: &str,
    args: &Args,
    occurrence: &SourceOccurrence,
    mode: &ModeIdentity,
    surface: &ResidentSurface<'_>,
    capacities: &DeviceCapacities,
    pcie: (String, String),
    clockings: &Clockings,
) -> String {
    let mut f = String::new();
    let _ = writeln!(f, "SOURCE AND MODE — Deed H0, the unchanged scalar path");
    let _ = writeln!(
        f,
        "the exact code/source/configuration/input closure this deed's receipts were taken under."
    );
    let _ = writeln!(
        f,
        "every value below was returned by a struct the passage handed back or by the device answering"
    );
    let _ = writeln!(
        f,
        "cuDeviceGetAttribute. The PCIe link rows and the block marked EXTERIOR TESTIMONY are quoted from"
    );
    let _ = writeln!(
        f,
        "tools outside the deed and are labelled so; they testify for nothing semantic.\n"
    );

    let _ = writeln!(f, "  [1] THE CLOSURE");
    let _ = writeln!(f, "    closure.commit = {commit}");
    let _ = writeln!(
        f,
        "    closure.driver = the_scalar_path_returns_its_pressure_and_utility"
    );
    let _ = writeln!(f, "    closure.mode = --receipts");
    let _ = writeln!(f, "    closure.text = {CLOSURE_TEXT}");
    let _ = writeln!(
        f,
        "    closure.tokens = {}",
        args.tokens
            .iter()
            .map(|t| t.to_string())
            .collect::<Vec<_>>()
            .join(",")
    );
    let _ = writeln!(f, "    closure.positions = {}", args.tokens.len());
    let _ = writeln!(f, "    closure.chart = {:?}", args.chart);
    let _ = writeln!(f, "    closure.grain = {}", args.grain);
    let _ = writeln!(f, "    closure.terms = {}", args.terms);
    let _ = writeln!(
        f,
        "    closure.layers_conducted = {}",
        LAYERS_CONDUCTED
            .iter()
            .map(|l| l.to_string())
            .collect::<Vec<_>>()
            .join(",")
    );
    let _ = writeln!(
        f,
        "    closure.representative_layer = {REPRESENTATIVE_LAYER}"
    );
    let _ = writeln!(
        f,
        "    closure.representative_layer_because = sliding species, entry on a carried standing, owns its own K and V — the shape 34 of the 42 layers have"
    );
    let _ = writeln!(f, "    closure.source_root = {}\n", args.root);

    let _ = writeln!(f, "  [2] THE SOURCE, AUTHENTICATED");
    let _ = writeln!(
        f,
        "    source.container.locator = {}",
        occurrence.container.locator
    );
    let _ = writeln!(
        f,
        "    source.container.octets = {}",
        occurrence.container.octets
    );
    let _ = writeln!(
        f,
        "    source.container.header_octets = {}",
        occurrence.container.header_octets
    );
    let _ = writeln!(
        f,
        "    source.container.header_sha256 = {}",
        occurrence.container.header_sha256
    );
    let _ = writeln!(
        f,
        "    source.container.content_sha256 = {}",
        occurrence
            .container
            .content_sha256
            .clone()
            .unwrap_or_else(|| format!("{} (not taken this run)", profile::UNKNOWN))
    );
    match &occurrence.container.identity {
        Some(identity) => {
            let _ = writeln!(
                f,
                "    source.container.identity.device = {}",
                identity.device
            );
            let _ = writeln!(
                f,
                "    source.container.identity.inode = {}",
                identity.inode
            );
            let _ = writeln!(
                f,
                "    source.container.identity.octets = {}",
                identity.octets
            );
            let _ = writeln!(
                f,
                "    source.container.identity.modified_secs = {}",
                identity.modified_secs
            );
            let _ = writeln!(
                f,
                "    source.container.identity.modified_nanos = {}",
                identity.modified_nanos
            );
            let _ = writeln!(
                f,
                "    source.container.identity.changed_secs = {}",
                identity.changed_secs
            );
            let _ = writeln!(
                f,
                "    source.container.identity.changed_nanos = {}",
                identity.changed_nanos
            );
        }
        None => {
            let _ = writeln!(
                f,
                "    source.container.identity = {} (not taken)",
                profile::UNKNOWN
            );
        }
    }
    let _ = writeln!(
        f,
        "    source.container.regions = {}",
        occurrence.container.regions.len()
    );
    let _ = writeln!(
        f,
        "    source.implementation.locator = {}",
        occurrence.implementation.locator
    );
    let _ = writeln!(
        f,
        "    source.implementation.sha256 = {}",
        occurrence.implementation.sha256
    );
    let _ = writeln!(
        f,
        "    source.implementation.octets = {}",
        occurrence.implementation.octets
    );
    let _ = writeln!(
        f,
        "    source.implementation.version = {}",
        occurrence
            .implementation
            .version
            .clone()
            .unwrap_or_else(|| profile::UNKNOWN.to_owned())
    );
    let _ = writeln!(
        f,
        "    source.implementation.declared_sha256 = {}",
        resident_layer::IMPLEMENTATION_SHA256
    );
    let _ = writeln!(
        f,
        "    source.configuration.locator = {}",
        occurrence.configuration.locator
    );
    let _ = writeln!(
        f,
        "    source.configuration.sha256 = {}",
        occurrence.configuration.sha256
    );
    let _ = writeln!(
        f,
        "    source.configuration.octets = {}",
        occurrence.configuration.octets
    );
    for asset in &occurrence.assets {
        let _ = writeln!(
            f,
            "    source.asset.{} = {} sha256 {} used {}",
            asset.role.replace(' ', "_"),
            asset.locator,
            asset
                .sha256
                .clone()
                .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
            asset.used
        );
    }
    let _ = writeln!(f);

    let _ = writeln!(
        f,
        "  [3] THE MODE — the identity every launch is checked against"
    );
    let _ = writeln!(f, "    mode.source_law = {}", mode.source_law);
    let _ = writeln!(f, "    mode.abi = {}", mode.abi);
    let _ = writeln!(f, "    mode.kernel = {}", mode.kernel);
    let _ = writeln!(
        f,
        "    mode.kernel_content = {}",
        mode.kernel_content
            .clone()
            .unwrap_or_else(|| profile::UNKNOWN.to_owned())
    );
    let _ = writeln!(f, "    mode.arithmetic = {}", mode.arithmetic);
    let _ = writeln!(
        f,
        "    mode.device = {}",
        mode.device
            .clone()
            .unwrap_or_else(|| profile::UNKNOWN.to_owned())
    );
    let _ = writeln!(f, "    mode.apparatus = {}\n", mode.apparatus);

    let _ = writeln!(
        f,
        "  [4] THE DEVICE, ANSWERING ABOUT ITSELF (cuDeviceGetAttribute)"
    );
    let declaration = surface.declaration();
    let _ = writeln!(f, "    device.name = {}", surface.device_name());
    let _ = writeln!(
        f,
        "    device.capability_major = {}",
        declaration.capability_major
    );
    let _ = writeln!(
        f,
        "    device.capability_minor = {}",
        declaration.capability_minor
    );
    let _ = writeln!(
        f,
        "    device.multiprocessors = {}",
        declaration.multiprocessors
    );
    let _ = writeln!(f, "    device.warp_size = {}", declaration.warp_size);
    let _ = writeln!(
        f,
        "    device.max_threads_per_block = {}",
        declaration.max_threads_per_block
    );
    let _ = writeln!(
        f,
        "    device.max_threads_per_multiprocessor = {}",
        declaration.max_threads_per_multiprocessor
    );
    let _ = writeln!(
        f,
        "    device.resident_lanes = {}",
        declaration.resident_lanes()
    );
    let _ = writeln!(
        f,
        "    device.resident_groups = {}",
        declaration.resident_groups()
    );
    let _ = writeln!(f, "    device.max_grid_x = {}", declaration.max_grid_x);
    let _ = writeln!(
        f,
        "    device.async_engines = {}",
        declaration.async_engines
    );
    let _ = writeln!(
        f,
        "    device.concurrent_kernels = {}",
        declaration.concurrent_kernels
    );
    for (name, _) in ATTRIBUTES {
        let _ = writeln!(f, "    device.attribute.{name} = {}", capacities.text(name));
    }
    let dram = match (
        capacities.get("memory_clock_khz"),
        capacities.get("global_memory_bus_width_bits"),
    ) {
        (Some(khz), Some(bits)) => format!(
            "{} (derived: 2 × {khz} kHz × {bits} bits ÷ 8, the driver's own two attributes; DDR double rate)",
            2u64 * (khz as u64) * 1000 * (bits as u64) / 8
        ),
        _ => format!(
            "{} (the driver did not state memory clock or bus width)",
            profile::UNKNOWN
        ),
    };
    let _ = writeln!(f, "    device.dram_nominal_octets_per_second = {dram}");
    let _ = writeln!(
        f,
        "    device.allocation_grain = {}",
        surface.allocation_grain()
    );
    let _ = writeln!(
        f,
        "    device.memory_at_mount_free_octets = {}",
        surface.memory_at_mount().free_bytes
    );
    let _ = writeln!(
        f,
        "    device.memory_at_mount_total_octets = {}",
        surface.memory_at_mount().total_bytes
    );
    let _ = writeln!(f, "    device.ptx_sha256 = {}", surface.ptx_sha256());
    let _ = writeln!(
        f,
        "    pcie.link_gen_max = {} (EXTERIOR: nvidia-smi --query-gpu=pcie.link.gen.max)",
        pcie.0
    );
    let _ = writeln!(
        f,
        "    pcie.link_width_max = {} (EXTERIOR: nvidia-smi --query-gpu=pcie.link.width.max)",
        pcie.1
    );
    let pcie_nominal = match (pcie.0.trim().parse::<u32>(), pcie.1.trim().parse::<u64>()) {
        (Ok(4), Ok(width)) => format!(
            "{} (derived: 16 GT/s × {width} lanes × 128/130 encoding ÷ 8)",
            (16_000_000_000u128 * width as u128 * 128 / 130 / 8) as u64
        ),
        _ => format!(
            "{} (the link generation or width was not stated)",
            profile::UNKNOWN
        ),
    };
    let _ = writeln!(f, "    pcie.nominal_octets_per_second = {pcie_nominal}\n");

    let _ = writeln!(
        f,
        "  [5] EXTERIOR TESTIMONY — quoted from tools outside the deed; they testify for nothing semantic"
    );
    let _ = writeln!(
        f,
        "    exterior.nvidia_smi_driver_version = {}",
        exterior(
            "nvidia-smi",
            &["--query-gpu=driver_version", "--format=csv,noheader"]
        )
    );
    let _ = writeln!(
        f,
        "    exterior.nvidia_smi_name = {}",
        exterior("nvidia-smi", &["--query-gpu=name", "--format=csv,noheader"])
    );
    let _ = writeln!(
        f,
        "    exterior.nvcc_version = {}",
        exterior("nvcc", &["--version"])
    );
    let _ = writeln!(f, "    exterior.uname = {}\n", exterior("uname", &["-sr"]));

    let _ = writeln!(
        f,
        "  [6] EVERY EXPENSIVE STEP, WITH ITS ELAPSED TIME AND STATUS"
    );
    let _ = writeln!(
        f,
        "    the frame: this process on this machine, the card's display state not declared; an elapsed"
    );
    let _ = writeln!(
        f,
        "    time is an apparatus measurement and selects nothing."
    );
    for (what, elapsed, status) in &clockings.0 {
        let _ = writeln!(f, "      {elapsed:>9.3} s  {status:<24} {what}");
    }
    f
}

fn causal_fronts_form(profiles: &[LayerProfile]) -> String {
    let mut f = String::new();
    let _ = writeln!(
        f,
        "CAUSAL FRONTS — the FrontReceipt population of the conducted layers, in depth order"
    );
    let _ = writeln!(
        f,
        "every front is the receipt the passage took BEFORE any launch: its members, their footprints, the"
    );
    let _ = writeln!(
        f,
        "certificate derived from those footprints, the named couplings, and the cover's own reading. Nothing"
    );
    let _ = writeln!(
        f,
        "here is measured overlap: a certificate is PERMISSION for co-presence, never evidence of it.\n"
    );
    for p in profiles {
        let role = if p.layer == REPRESENTATIVE_LAYER {
            "THE REPRESENTATIVE LAYER"
        } else {
            "PREDECESSOR — conducted only to produce the representative layer's entry"
        };
        let _ = writeln!(
            f,
            "================================================================================"
        );
        let _ = writeln!(f, "LAYER {} — {role}", p.layer);
        let _ = writeln!(
            f,
            "================================================================================"
        );
        let _ = writeln!(f, "    layer{}.species = {:?}", p.layer, p.species);
        let _ = writeln!(f, "    layer{}.kv_role = {:?}", p.layer, p.role);
        let _ = writeln!(f, "    layer{}.entry = {:?}", p.layer, p.entry);
        let _ = writeln!(f, "    layer{}.fronts = {}", p.layer, p.fronts.len());
        let _ = writeln!(f, "    layer{}.members = {}", p.layer, p.members());
        let _ = writeln!(
            f,
            "    layer{}.fronts_with_two_or_more_members = {}",
            p.layer,
            p.plural_fronts()
        );
        let _ = writeln!(f, "    layer{}.schedule = {:?}", p.layer, p.schedule);
        let _ = writeln!(f, "    layer{}.graph.nodes = {}", p.layer, p.graph_nodes);
        let _ = writeln!(f, "    layer{}.graph.edges = {}", p.layer, p.graph_edges);
        let _ = writeln!(
            f,
            "    layer{}.graph.kernel_nodes = {}",
            p.layer, p.graph_kernel_nodes
        );
        let _ = writeln!(
            f,
            "    layer{}.graph.memset_nodes = {}",
            p.layer, p.graph_memset_nodes
        );
        let _ = writeln!(
            f,
            "    layer{}.graph.memcpy_nodes = {}",
            p.layer, p.graph_memcpy_nodes
        );
        let _ = writeln!(
            f,
            "    layer{}.graph.other_nodes = {}",
            p.layer, p.graph_other_nodes
        );
        let _ = writeln!(
            f,
            "    layer{}.graph.intended_nodes = {}",
            p.layer, p.intended_nodes
        );
        let _ = writeln!(
            f,
            "    layer{}.graph.intended_edges = {}",
            p.layer, p.intended_edges
        );
        let _ = writeln!(
            f,
            "    layer{}.captured_launches = {}",
            p.layer, p.apparatus.captured_launches
        );
        let _ = writeln!(
            f,
            "    layer{}.deed_launches = {}",
            p.layer, p.apparatus.deed_launches
        );
        let _ = writeln!(
            f,
            "    layer{}.synchronizations = {}",
            p.layer, p.apparatus.synchronizations
        );
        let _ = writeln!(f, "    layer{}.stood = {}", p.layer, p.stood);
        let _ = writeln!(
            f,
            "    layer{}.a_priori_octave_bound_held = {}",
            p.layer, p.a_priori_held
        );
        let _ = writeln!(
            f,
            "    layer{}.measured_octave_ports = {}",
            p.layer, p.measured_octaves
        );
        let certified = p
            .fronts
            .iter()
            .filter(|fr| fr.certificate.is_interchangeable())
            .count();
        let _ = writeln!(
            f,
            "    layer{}.fronts_certified_interchangeable = {certified}",
            p.layer
        );
        let _ = writeln!(
            f,
            "    layer{}.fronts_certified_ordered = {}",
            p.layer,
            p.fronts.len() - certified
        );
        let _ = writeln!(f);
        for receipt in &p.fronts {
            let _ = writeln!(
                f,
                "  ---- FRONT depth {} — {} member(s)",
                receipt.depth,
                receipt.members.len()
            );
            let verdict = if receipt.certificate.is_interchangeable() {
                "Interchangeable".to_owned()
            } else {
                format!("Ordered because {:?}", receipt.certificate.because())
            };
            let _ = writeln!(
                f,
                "       certificate: {verdict} · schema {} · orders enacted {} · refusals {} · endpoints {} conduct {} obstruction {} lineage {} resources {} capacities {} remainder {} · coherence {:?} · endpoint-only verdict would have been {}",
                receipt.certificate.schema,
                receipt.certificate.orders.len(),
                receipt.certificate.refusals.len(),
                receipt.certificate.endpoints_agree,
                receipt.certificate.conduct_agrees,
                receipt.certificate.obstruction_agrees,
                receipt.certificate.lineage_agrees,
                receipt.certificate.resources_agree,
                receipt.certificate.capacities_agree,
                receipt.certificate.remainder_agrees,
                receipt.certificate.coherence,
                receipt.certificate.endpoint_only_verdict()
            );
            let _ = writeln!(
                f,
                "       cover: occupied charts {:?} · device cells {} · cpu cells {} · members {} · occupied lanes {} · idle lanes {}",
                receipt.cover.occupied,
                receipt.cover.device_cells,
                receipt.cover.cpu_cells,
                receipt.cover.members,
                receipt.cover.occupied_lanes,
                receipt.cover.idle_lanes
            );
            let _ = writeln!(
                f,
                "       front work: additions {} · multiplications {} · divisions {} · entries {} · peak-bits {} · resident {} · span {}",
                receipt.predicted.additions,
                receipt.predicted.multiplications,
                receipt.predicted.divisions,
                receipt.predicted.entries_written,
                receipt.predicted.peak_bits,
                receipt.predicted.resident_entries,
                receipt.predicted.dependency_span
            );
            for (index, (event, operation)) in receipt.members.iter().enumerate() {
                let law = p
                    .names
                    .get(event)
                    .map(|(_, l)| l.clone())
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned());
                let extent = p
                    .extents
                    .get(event)
                    .map(|(rows, width, octets)| {
                        format!("{rows} rows × {width} wide, {octets} octets resident")
                    })
                    .unwrap_or_else(|| {
                        format!("{} (no section owned by this occurrence)", profile::UNKNOWN)
                    });
                let octave = p
                    .octaves
                    .get(event)
                    .map(|o| o.to_string())
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned());
                let _ = writeln!(f, "       · e{} operation {operation} · law {law}", event.0);
                let _ = writeln!(
                    f,
                    "           output extent: {extent} · admitted octave bound {octave}"
                );
                let producers = p.producers.get(event).cloned().unwrap_or_default();
                if producers.is_empty() {
                    let _ = writeln!(
                        f,
                        "           predecessors: none — this occurrence enters on material"
                    );
                } else {
                    let named: Vec<String> = producers
                        .iter()
                        .map(|e| {
                            format!(
                                "e{}({})",
                                e.0,
                                p.names
                                    .get(e)
                                    .map(|(op, _)| (*op).to_string())
                                    .unwrap_or_else(|| profile::UNKNOWN.to_owned())
                            )
                        })
                        .collect();
                    let _ = writeln!(f, "           predecessors: {}", named.join(" "));
                }
                let ports = p.arriving.get(event).cloned().unwrap_or_default();
                if ports.is_empty() {
                    let _ = writeln!(f, "           arriving ports: none named");
                } else {
                    let named: Vec<String> = ports
                        .iter()
                        .map(|(name, from, to)| {
                            format!("{name}[{} → {}]", port_name(from), port_name(to))
                        })
                        .collect();
                    let _ = writeln!(f, "           arriving ports: {}", named.join("  "));
                }
                if let Some(footprint) = receipt.footprints.get(index) {
                    let read_octets: u64 = footprint
                        .reads
                        .iter()
                        .map(|(a, b)| b.saturating_sub(*a))
                        .sum();
                    let write_octets: u64 = footprint
                        .writes
                        .iter()
                        .map(|(a, b)| b.saturating_sub(*a))
                        .sum();
                    let _ = writeln!(
                        f,
                        "           footprint: {} read range(s) totalling {read_octets} octets · {} write range(s) totalling {write_octets} octets",
                        footprint.reads.len(),
                        footprint.writes.len()
                    );
                }
                if let Some((reads, write)) = receipt.slot_footprints.get(index) {
                    let _ = writeln!(
                        f,
                        "           census slots: reads {reads:?} · writes {write:?}"
                    );
                }
            }
            if let Some(reading) = p.readings.iter().find(|r| r.depth == receipt.depth) {
                let _ = writeln!(
                    f,
                    "       MEASURED — what the card's census returned for this front after the launch:"
                );
                for member in &reading.readings {
                    let _ = writeln!(
                        f,
                        "         e{:<5} {:<20} bound {:>4} needed {:>4} · measured max octave {:>4} · written {} · refused {} · bound violated {} · inverted {} · reach {} · max width {} · width sum {} · nonzero widths {} · lineage inspected {} · upstream refusals {}",
                        member.occurrence.0,
                        member.operation,
                        member.bound,
                        member.needed,
                        member.measured.max_octave,
                        member.measured.written,
                        member.measured.refused,
                        member.measured.bound_violated,
                        member.measured.inverted,
                        member.measured.reach,
                        member.measured.max_width,
                        member.measured.width_sum,
                        member.measured.nonzero_widths,
                        member.measured.lineage_inspected,
                        member.measured.upstream_count
                    );
                }
                for coupling in &reading.couplings {
                    let _ = writeln!(
                        f,
                        "         coupling completed: {} · kernel {} · written {} · measured octave {} · measured width {} · refused {} · reach {}",
                        coupling.plan.coupling,
                        coupling.plan.kernel,
                        coupling.written,
                        coupling.measured_octave,
                        coupling.measured_width,
                        coupling.refused,
                        coupling.reach
                    );
                }
            }
            if receipt.couplings.is_empty() {
                let _ = writeln!(f, "       couplings (as bound, before the launch): none");
            } else {
                for coupling in &receipt.couplings {
                    let _ = writeln!(
                        f,
                        "       coupling (as bound) {} · kernel {} · extent {} · block {} · at e{} · output {} · inputs {:?} · written {} · measured octave {} · measured width {} · refused {} · reach {}",
                        coupling.plan.coupling,
                        coupling.plan.kernel,
                        coupling.plan.extent,
                        coupling.plan.block,
                        coupling.occurrence.0,
                        port_name(&coupling.output),
                        coupling.inputs.iter().map(port_name).collect::<Vec<_>>(),
                        coupling.written,
                        coupling.measured_octave,
                        coupling.measured_width,
                        coupling.refused,
                        coupling.reach
                    );
                }
            }
            let _ = writeln!(f);
        }
    }
    let _ = writeln!(f, "GRAPH PERMISSION, STATED AS PERMISSION");
    for p in profiles {
        let _ = writeln!(
            f,
            "    layer{}: schedule {:?}, {} of {} fronts carry two or more members, so the diagram PERMITS {} co-present member(s) beyond the serial order. Whether any of them overlapped physically is not in this file; it is measured in surface-utility.form.",
            p.layer,
            p.schedule,
            p.plural_fronts(),
            p.fronts.len(),
            p.fronts
                .iter()
                .map(|fr| fr.members.len().saturating_sub(1))
                .sum::<usize>()
        );
    }
    f
}

fn exact_work_form(profiles: &[LayerProfile]) -> String {
    let mut f = String::new();
    let _ = writeln!(
        f,
        "EXACT WORK — the semantic half of the receipt, in the coordinates ExactWork returns"
    );
    let _ = writeln!(
        f,
        "these are counted operations on exact rationals, not times, not throughputs, and not a scalar. The"
    );
    let _ = writeln!(
        f,
        "serial law is ExactWork::then: counts add, peaks and spans take the maximum, resident populations"
    );
    let _ = writeln!(
        f,
        "add; two co-present deeds compose by front_passage::co_present. Nothing here is divided by anything.\n"
    );
    for p in profiles {
        let role = if p.layer == REPRESENTATIVE_LAYER {
            "REPRESENTATIVE"
        } else {
            "PREDECESSOR"
        };
        let _ = writeln!(
            f,
            "================================================================================"
        );
        let _ = writeln!(f, "LAYER {} ({role})", p.layer);
        let _ = writeln!(
            f,
            "================================================================================\n"
        );
        let _ = writeln!(
            f,
            "  [1] PER FRONT — the ExactWork the front's members were admitted under"
        );
        let _ = writeln!(
            f,
            "      (per-OCCURRENCE work is carried on the private LawShape of front_passage::Plan and is not"
        );
        let _ = writeln!(
            f,
            "       reachable through any public accessor; per-front and per-coupling are what the passage exposes)"
        );
        for receipt in &p.fronts {
            let members: Vec<String> = receipt
                .members
                .iter()
                .map(|(e, op)| format!("e{}:{op}", e.0))
                .collect();
            let _ = writeln!(
                f,
                "      depth {:>3} · {:<58} + {} × {} ÷ {} · entries {} · cumulative-bits {} · peak-bits {} · resident {} · span {}",
                receipt.depth,
                members.join(" "),
                receipt.predicted.additions,
                receipt.predicted.multiplications,
                receipt.predicted.divisions,
                receipt.predicted.entries_written,
                receipt.predicted.cumulative_bits,
                receipt.predicted.peak_bits,
                receipt.predicted.resident_entries,
                receipt.predicted.dependency_span
            );
            for coupling in &receipt.couplings {
                let _ = writeln!(
                    f,
                    "               coupling {:<28} kernel {:<26} extent {:>8} block {:>5} · + {} × {} ÷ {} · span {}",
                    coupling.plan.coupling,
                    coupling.plan.kernel,
                    coupling.plan.extent,
                    coupling.plan.block,
                    coupling.plan.predicted.additions,
                    coupling.plan.predicted.multiplications,
                    coupling.plan.predicted.divisions,
                    coupling.plan.predicted.dependency_span
                );
            }
        }
        let _ = writeln!(f);
        let _ = writeln!(f, "  [2] THE DEED TOTAL — deed_prediction.coordinates()");
        for (name, value) in p.deed.coordinates() {
            let _ = writeln!(
                f,
                "    layer{}.deed.{} = {value}",
                p.layer,
                name.replace('-', "_")
            );
        }
        let _ = writeln!(f);
        let _ = writeln!(
            f,
            "  [3] THE APPARATUS PREDICTION — what the realization costs, in octets and counts"
        );
        let a = &p.apparatus;
        for (name, value) in [
            ("source_map_octets", a.source_map_octets),
            ("carried_standing_octets", a.carried_standing_octets),
            ("staged_octets", a.staged_octets),
            ("section_octets", a.section_octets),
            ("census_octets", a.census_octets),
            ("lineage_octets", a.lineage_octets),
            ("deed_octets", a.deed_octets),
            ("charged_octets", a.charged_octets),
            ("allocation_grain", a.allocation_grain),
            ("allocations", a.allocations),
            ("scratch_octets", a.scratch_octets),
            ("grid_extent", a.grid_extent),
            ("carrier_peak_octaves", a.carrier_peak_octaves),
            (
                "a_priori_peak_octaves_uncapped",
                a.a_priori_peak_octaves_uncapped,
            ),
            (
                "occurrences_admitted_at_the_word",
                a.occurrences_admitted_at_the_word,
            ),
            ("captured_launches", a.captured_launches),
            ("reductions", a.reductions),
            ("deed_launches", a.deed_launches),
            ("synchronizations", a.synchronizations),
            ("streams", a.streams),
            ("events", a.events),
            ("graphs", a.graphs),
            ("graph_execs", a.graph_execs),
            ("ingress_octets", a.ingress_octets),
            ("egress_receipt_octets", a.egress_receipt_octets),
            ("egress_section_octets", a.egress_section_octets),
            ("graph_nodes", a.graph_nodes),
            ("graph_edges", a.graph_edges),
            ("dependency_span", a.dependency_span),
            ("remainder_grain", a.remainder_grain),
        ] {
            let _ = writeln!(f, "    layer{}.apparatus.{name} = {value}", p.layer);
        }
        let _ = writeln!(
            f,
            "    layer{}.apparatus.allocation_octets = {:?}",
            p.layer, a.allocation_octets
        );
        let _ = writeln!(
            f,
            "    the three elapsed times below are apparatus measurements in this process's frame; they"
        );
        let _ = writeln!(f, "    price nothing semantic and select nothing:");
        let _ = writeln!(
            f,
            "    layer{}.wall.mount_seconds = {:.6}",
            p.layer, p.mount_wall_s
        );
        let _ = writeln!(
            f,
            "    layer{}.wall.bind_seconds = {:.6}",
            p.layer, p.bind_wall_s
        );
        let _ = writeln!(
            f,
            "    layer{}.wall.launch_and_synchronize_seconds = {:.6}",
            p.layer, p.launch_wall_s
        );
        let _ = writeln!(f);
        let _ = writeln!(
            f,
            "  [4] THE ADMISSION — every coordinate, its requirement, its ceiling and who declared it"
        );
        let _ = writeln!(
            f,
            "    layer{}.admission.is_admitted = {}",
            p.layer,
            p.admission.is_admitted()
        );
        let _ = writeln!(
            f,
            "    layer{}.admission.free_octets_at_admission = {}",
            p.layer, p.admission.free_octets_at_admission
        );
        let _ = writeln!(
            f,
            "    layer{}.admission.semantic_coordinates = {}",
            p.layer,
            p.admission.semantic.len()
        );
        let _ = writeln!(
            f,
            "    layer{}.admission.apparatus_coordinates = {}",
            p.layer,
            p.admission.apparatus.len()
        );
        let _ = writeln!(
            f,
            "    layer{}.admission.bounded = {}",
            p.layer,
            p.admission.bounded().count()
        );
        let _ = writeln!(
            f,
            "    layer{}.admission.unbounded = {}",
            p.layer,
            p.admission.unbounded().count()
        );
        let _ = writeln!(f, "    semantic:");
        for coordinate in &p.admission.semantic {
            let _ = writeln!(f, "{}", coordinate_line(coordinate));
        }
        let _ = writeln!(f, "    apparatus:");
        for coordinate in &p.admission.apparatus {
            let _ = writeln!(f, "{}", coordinate_line(coordinate));
        }
        let _ = writeln!(f, "    cited material admission:");
        let _ = writeln!(
            f,
            "      layer{}.material.is_admitted = {}",
            p.layer,
            p.material.is_admitted()
        );
        let _ = writeln!(
            f,
            "      layer{}.material.resident_octets = {}",
            p.layer,
            p.material.resident_octets()
        );
        let _ = writeln!(
            f,
            "      layer{}.material.ingress_octets = {}",
            p.layer, p.material.prediction.ingress_octets
        );
        let _ = writeln!(
            f,
            "      layer{}.material.charged_octets = {}",
            p.layer, p.material.prediction.charged_octets
        );
        let _ = writeln!(
            f,
            "      layer{}.material.allocations = {}",
            p.layer, p.material.prediction.allocations
        );
        let _ = writeln!(
            f,
            "      layer{}.material.transient_peak_octets = {}",
            p.layer, p.material.prediction.transient_peak_octets
        );
        let _ = writeln!(
            f,
            "      layer{}.material.maps = {}",
            p.layer,
            p.material.prediction.maps.len()
        );
        let _ = writeln!(f);
    }
    if profiles.len() >= 2 {
        let _ = writeln!(
            f,
            "================================================================================"
        );
        let _ = writeln!(f, "THE REPRESENTATIVE LAYER AGAINST ITS PREDECESSOR");
        let _ = writeln!(
            f,
            "================================================================================"
        );
        let _ = writeln!(
            f,
            "  the two layers differ in exactly one declared thing: layer 0 enters on ROWS decoded from the"
        );
        let _ = writeln!(
            f,
            "  entering material, layer 1 enters on the CARRIED standing layer 0 released. Every other"
        );
        let _ = writeln!(
            f,
            "  declaration is identical, so the difference below is the entry's own price."
        );
        let zero = &profiles[0];
        let one = &profiles[1];
        for ((name, a), (_, b)) in zero
            .deed
            .coordinates()
            .iter()
            .zip(one.deed.coordinates().iter())
        {
            let _ = writeln!(
                f,
                "    {:<28} layer0 {:<26} layer1 {:<26} equal {}",
                name,
                a,
                b,
                a == b
            );
        }
        let _ = writeln!(
            f,
            "    serial composition (ExactWork::then, layer0 then layer1):"
        );
        for (name, value) in zero.deed.then(&one.deed).coordinates() {
            let _ = writeln!(
                f,
                "      tower_two_layers.{} = {value}",
                name.replace('-', "_")
            );
        }
    }
    f
}

fn pressure_form(
    profiles: &[LayerProfile],
    capacities: &DeviceCapacities,
    surface: &ResidentSurface<'_>,
) -> String {
    let mut f = String::new();
    let _ = writeln!(
        f,
        "PRESSURE — current against capacity, per site, per resource species"
    );
    let _ = writeln!(
        f,
        "R = ceil(N / C) per species, per site. The species are NEVER summed and no scalar pressure exists"
    );
    let _ = writeln!(
        f,
        "here: a row whose demand the deed does not measure carries `unknown`, and an unknown row is not a"
    );
    let _ = writeln!(
        f,
        "zero row. `--join` fills the demand columns the exterior telemetry supplies, into pressure-joined.form.\n"
    );
    for p in profiles {
        let role = if p.layer == REPRESENTATIVE_LAYER {
            "REPRESENTATIVE"
        } else {
            "PREDECESSOR"
        };
        let _ = writeln!(
            f,
            "================================================================================"
        );
        let _ = writeln!(
            f,
            "LAYER {} ({role}) — the resident-lane species, site by site",
            p.layer
        );
        let _ = writeln!(
            f,
            "================================================================================"
        );
        let _ = writeln!(
            f,
            "    layer{}.traffic.resident_lanes = {}",
            p.layer, p.traffic.resident_lanes
        );
        let _ = writeln!(
            f,
            "    layer{}.traffic.earliest_arrival = {}",
            p.layer, p.traffic.earliest_arrival
        );
        let _ = writeln!(
            f,
            "    layer{}.traffic.earliest_routes = {}",
            p.layer, p.traffic.earliest_routes
        );
        let _ = writeln!(
            f,
            "    layer{}.traffic.deferred_arrivals = {}",
            p.layer, p.traffic.deferred_arrivals
        );
        let _ = writeln!(
            f,
            "    layer{}.traffic.deferred_population = {}",
            p.layer, p.traffic.deferred_population
        );
        let _ = writeln!(
            f,
            "    layer{}.traffic.reconvergent_sites = {}",
            p.layer, p.traffic.reconvergent_sites
        );
        let _ = writeln!(
            f,
            "    layer{}.traffic.junctions = {}",
            p.layer,
            p.traffic.junctions.len()
        );
        let _ = writeln!(
            f,
            "    layer{}.traffic.characteristic_delay = 1 (every bond of the diagram; front_passage::traffic_reading founds each passage with characteristic_delay 1)",
            p.layer
        );
        match &p.traffic.composite {
            Some((t, r, power)) => {
                let _ = writeln!(
                    f,
                    "    layer{}.traffic.composite_transmission = {t}",
                    p.layer
                );
                let _ = writeln!(f, "    layer{}.traffic.composite_reflection = {r}", p.layer);
                let _ = writeln!(
                    f,
                    "    layer{}.traffic.composite_power_transmission = {power}",
                    p.layer
                );
            }
            None => {
                let _ = writeln!(
                    f,
                    "    layer{}.traffic.composite = {} (a junction did not cross)",
                    p.layer,
                    profile::UNKNOWN
                );
            }
        }
        let _ = writeln!(f);
        let _ = writeln!(
            f,
            "  SITE TABLE — one row per front. species = resident lanes on the device chart."
        );
        let _ = writeln!(
            f,
            "    {:>5}  {:>12}  {:>12}  {:>12}  {:>7}  {:>19}",
            "depth", "N occupied", "idle lanes", "C resident", "R rounds", "characteristic delay"
        );
        for (depth, occupied, idle, rounds) in &p.traffic.fronts {
            let _ = writeln!(
                f,
                "    {depth:>5}  {occupied:>12}  {idle:>12}  {:>12}  {rounds:>7}  {:>19}",
                p.traffic.resident_lanes, 1
            );
        }
        let _ = writeln!(f);
        let _ = writeln!(
            f,
            "  JUNCTIONS — each front-to-front crossing as an admittance meeting (traversible_chain)"
        );
        for junction in &p.traffic.junctions {
            let _ = writeln!(
                f,
                "    {:>4} → {:<4} incident {:>10} transmitted {:>10} · transmission {} · reflection {} · power {}",
                junction.from_depth,
                junction.to_depth,
                junction.incident_lanes,
                junction.transmitted_lanes,
                junction.transmission,
                junction.reflection,
                junction.power_transmission
            );
        }
        let _ = writeln!(f);
    }

    let _ = writeln!(
        f,
        "================================================================================"
    );
    let _ = writeln!(
        f,
        "THE OTHER RESOURCE SPECIES — capacity from the device, demand from telemetry"
    );
    let _ = writeln!(
        f,
        "================================================================================"
    );
    let _ = writeln!(
        f,
        "  Every capacity C below was read from the device through cuDeviceGetAttribute or from the link"
    );
    let _ = writeln!(
        f,
        "  the driver reported. Every demand N is `unknown` in this file by construction: the passage does"
    );
    let _ = writeln!(
        f,
        "  not measure register pressure, shared-memory residency, DRAM traffic or bus occupancy, and this"
    );
    let _ = writeln!(
        f,
        "  deed will not infer them. `--join` fills the rows the exterior apparatus measured.\n"
    );
    let sms = capacities.get("multiprocessors").unwrap_or(0);
    let per = |value: Option<i64>| {
        value
            .map(|v| v.to_string())
            .unwrap_or_else(|| profile::UNKNOWN.to_owned())
    };
    let whole = |value: Option<i64>| match (value, sms) {
        (Some(v), s) if s > 0 => (v * s).to_string(),
        _ => profile::UNKNOWN.to_owned(),
    };
    let _ = writeln!(
        f,
        "    {:<34} {:>18} {:>18} {:>12} {:>10}",
        "species", "C per unit", "C whole card", "N demand", "R rounds"
    );
    let rows: Vec<(&str, String, String)> = vec![
        (
            "32-bit registers per SM",
            per(capacities.get("max_registers_per_multiprocessor")),
            whole(capacities.get("max_registers_per_multiprocessor")),
        ),
        (
            "shared-memory octets per SM",
            per(capacities.get("max_shared_octets_per_multiprocessor")),
            whole(capacities.get("max_shared_octets_per_multiprocessor")),
        ),
        (
            "shared-memory octets per block",
            per(capacities.get("max_shared_octets_per_block")),
            profile::UNKNOWN.to_owned(),
        ),
        (
            "32-bit registers per block",
            per(capacities.get("max_registers_per_block")),
            profile::UNKNOWN.to_owned(),
        ),
        (
            "resident threads per SM",
            per(capacities.get("max_threads_per_multiprocessor")),
            whole(capacities.get("max_threads_per_multiprocessor")),
        ),
        (
            "resident warps per SM",
            match (
                capacities.get("max_threads_per_multiprocessor"),
                capacities.get("warp_size"),
            ) {
                (Some(t), Some(w)) if w > 0 => (t / w).to_string(),
                _ => profile::UNKNOWN.to_owned(),
            },
            match (
                capacities.get("max_threads_per_multiprocessor"),
                capacities.get("warp_size"),
                sms,
            ) {
                (Some(t), Some(w), s) if w > 0 && s > 0 => (t / w * s).to_string(),
                _ => profile::UNKNOWN.to_owned(),
            },
        ),
        (
            "resident blocks per SM",
            per(capacities.get("max_blocks_per_multiprocessor")),
            whole(capacities.get("max_blocks_per_multiprocessor")),
        ),
        (
            "multiprocessors",
            per(capacities.get("multiprocessors")),
            per(capacities.get("multiprocessors")),
        ),
        (
            "L2 cache octets",
            per(capacities.get("l2_cache_octets")),
            per(capacities.get("l2_cache_octets")),
        ),
        (
            "DRAM octets (device memory)",
            surface.memory_at_mount().total_bytes.to_string(),
            surface.memory_at_mount().total_bytes.to_string(),
        ),
        (
            "DRAM octets per second (nominal)",
            match (
                capacities.get("memory_clock_khz"),
                capacities.get("global_memory_bus_width_bits"),
            ) {
                (Some(khz), Some(bits)) => (2u64 * khz as u64 * 1000 * bits as u64 / 8).to_string(),
                _ => profile::UNKNOWN.to_owned(),
            },
            profile::UNKNOWN.to_owned(),
        ),
        (
            "copy engines (async engine count)",
            per(capacities.get("async_engine_count")),
            per(capacities.get("async_engine_count")),
        ),
        (
            "PCIe octets per second (nominal)",
            "see source-and-mode.form pcie.nominal_octets_per_second".to_owned(),
            profile::UNKNOWN.to_owned(),
        ),
        (
            "CPU I/O octets",
            profile::UNKNOWN.to_owned(),
            profile::UNKNOWN.to_owned(),
        ),
        (
            "streams",
            "1 per bound passage (front_passage allocates one)".to_owned(),
            profile::UNKNOWN.to_owned(),
        ),
        (
            "events",
            profile::UNKNOWN.to_owned(),
            profile::UNKNOWN.to_owned(),
        ),
        (
            "graph nodes",
            profile::UNKNOWN.to_owned(),
            profile::UNKNOWN.to_owned(),
        ),
    ];
    for (species, c_unit, c_card) in &rows {
        let (n, r) = (profile::UNKNOWN, profile::UNKNOWN);
        let _ = writeln!(
            f,
            "    {species:<34} {c_unit:>18} {c_card:>18} {n:>12} {r:>10}"
        );
    }
    let _ = writeln!(f);
    for p in profiles {
        let _ = writeln!(
            f,
            "    layer{}.apparatus_demand.streams = {}",
            p.layer, p.apparatus.streams
        );
        let _ = writeln!(
            f,
            "    layer{}.apparatus_demand.events = {}",
            p.layer, p.apparatus.events
        );
        let _ = writeln!(
            f,
            "    layer{}.apparatus_demand.graph_nodes = {}",
            p.layer, p.apparatus.graph_nodes
        );
        let _ = writeln!(
            f,
            "    layer{}.apparatus_demand.graph_edges = {}",
            p.layer, p.apparatus.graph_edges
        );
        let _ = writeln!(
            f,
            "    layer{}.apparatus_demand.allocations = {}",
            p.layer, p.apparatus.allocations
        );
        let _ = writeln!(
            f,
            "    layer{}.apparatus_demand.grid_extent = {}",
            p.layer, p.apparatus.grid_extent
        );
        let _ = writeln!(
            f,
            "    layer{}.apparatus_demand.ingress_octets = {}",
            p.layer, p.apparatus.ingress_octets
        );
        let _ = writeln!(
            f,
            "    layer{}.apparatus_demand.charged_octets = {}",
            p.layer, p.apparatus.charged_octets
        );
    }
    let _ = writeln!(
        f,
        "\n  NEVER SUMMED. There is no total pressure row and none may be derived from these: the species"
    );
    let _ = writeln!(
        f,
        "  are distinct coordinates of one local reaction, and a single number over them would be a receiver"
    );
    let _ = writeln!(f, "  face presented as the object.");
    f
}

// ---------------------------------------------------------------------------------------------
// MODE 2 — the join
// ---------------------------------------------------------------------------------------------

fn join(dir: &Path) -> Result<(), String> {
    println!("JOIN — reading the exterior telemetry beside the deed's own receipts");
    let forms = profile::FormFacts::read_all(
        dir,
        &[
            "source-and-mode.form",
            "causal-fronts.form",
            "exact-work.form",
            "pressure.form",
        ],
    );
    println!(
        "  forms read: {:?}; forms absent: {:?}",
        forms.read, forms.missing
    );
    let kernels = profile::Table::read(dir, "kernel-timeline.tsv");
    let transfers = profile::Table::read(dir, "transfer-timeline.tsv");
    let api = profile::Table::read(dir, "cpu-api-timeline.tsv");
    let process = profile::Table::read(dir, "cpu-process.tsv");
    let resources = profile::Table::read(dir, "kernel-resources.tsv");
    let scheduler = profile::Table::read(dir, "scheduler-states.tsv");
    let calibration = std::fs::read_to_string(dir.join("calibration.form")).ok();
    for (name, present) in [
        ("kernel-timeline.tsv", kernels.is_some()),
        ("transfer-timeline.tsv", transfers.is_some()),
        ("cpu-api-timeline.tsv", api.is_some()),
        ("cpu-process.tsv", process.is_some()),
        ("kernel-resources.tsv", resources.is_some()),
        ("scheduler-states.tsv", scheduler.is_some()),
        ("calibration.form", calibration.is_some()),
    ] {
        println!(
            "  {name}: {}",
            if present {
                "present"
            } else {
                "ABSENT — every face it carries stays unknown"
            }
        );
    }

    let timeline = kernels.as_ref().map(profile::read_timeline);
    let scheduler_faces = scheduler
        .as_ref()
        .map(profile::read_scheduler)
        .unwrap_or_default();
    let api_faces = api.as_ref().map(profile::read_api).unwrap_or_default();
    let transfer_faces = transfers
        .as_ref()
        .map(profile::read_transfers)
        .unwrap_or_default();

    let resident_lanes = forms.u64("device.resident_lanes");
    let sms = forms.u64("device.multiprocessors");
    let threads_per_sm = forms.u64("device.max_threads_per_multiprocessor");
    let pcie_nominal = forms
        .get("pcie.nominal_octets_per_second")
        .split_whitespace()
        .next()
        .and_then(|v| v.parse::<u64>().ok());

    // ---------------------------------------------------------------- surface-utility.form
    let mut u = String::new();
    let _ = writeln!(
        u,
        "SURFACE UTILITY — product-ordered, in four blocks that are never combined into one number"
    );
    let _ = writeln!(
        u,
        "semantic work, cover/current, apparatus traffic and physical telemetry are four coordinates of one"
    );
    let _ = writeln!(
        u,
        "reading. No ratio between blocks is taken, no speedup is computed, and no scalar utilization exists"
    );
    let _ = writeln!(
        u,
        "in this file. A block whose apparatus did not report stays `unknown`.\n"
    );
    let _ = writeln!(u, "  deed/source/mode lineage");
    for key in [
        "closure.commit",
        "closure.tokens",
        "closure.chart",
        "closure.grain",
        "closure.terms",
        "closure.representative_layer",
        "source.container.header_sha256",
        "source.container.content_sha256",
        "source.implementation.sha256",
        "mode.kernel",
        "mode.kernel_content",
        "mode.device",
        "device.name",
    ] {
        let _ = writeln!(u, "    {key} = {}", forms.get(key));
    }
    let _ = writeln!(u);

    let _ = writeln!(
        u,
        "  ---------------------------------------------------------------------------"
    );
    let _ = writeln!(
        u,
        "  (i) SEMANTIC WORK — exact, counted, from exact-work.form. Not divided by any time."
    );
    let _ = writeln!(
        u,
        "  ---------------------------------------------------------------------------"
    );
    for layer in LAYERS_CONDUCTED {
        for coordinate in [
            "additions",
            "multiplications",
            "divisions",
            "entries_written",
            "cumulative_bits",
            "peak_bits",
            "resident_entries",
            "dependency_span",
            "width_weighted_operations",
        ] {
            let key = format!("layer{layer}.deed.{coordinate}");
            let _ = writeln!(u, "    {key} = {}", forms.get(&key));
        }
    }
    let _ = writeln!(u);

    let _ = writeln!(
        u,
        "  ---------------------------------------------------------------------------"
    );
    let _ = writeln!(
        u,
        "  (ii) COVER AND CURRENT — the front population, the lanes, the rounds, the deferred arrivals"
    );
    let _ = writeln!(
        u,
        "  ---------------------------------------------------------------------------"
    );
    for layer in LAYERS_CONDUCTED {
        for key in [
            format!("layer{layer}.fronts"),
            format!("layer{layer}.members"),
            format!("layer{layer}.fronts_with_two_or_more_members"),
            format!("layer{layer}.schedule"),
            format!("layer{layer}.traffic.resident_lanes"),
            format!("layer{layer}.traffic.earliest_arrival"),
            format!("layer{layer}.traffic.earliest_routes"),
            format!("layer{layer}.traffic.deferred_arrivals"),
            format!("layer{layer}.traffic.deferred_population"),
            format!("layer{layer}.traffic.reconvergent_sites"),
        ] {
            let _ = writeln!(u, "    {key} = {}", forms.get(&key));
        }
    }
    let _ = writeln!(u);

    let _ = writeln!(
        u,
        "  ---------------------------------------------------------------------------"
    );
    let _ = writeln!(
        u,
        "  (iii) APPARATUS TRAFFIC — what the exterior profiler recorded"
    );
    let _ = writeln!(
        u,
        "  ---------------------------------------------------------------------------"
    );
    match &timeline {
        None => {
            let _ = writeln!(
                u,
                "    kernel-timeline.tsv absent — every apparatus-traffic face is unknown."
            );
        }
        Some(timeline) => {
            let _ = writeln!(
                u,
                "    total kernel launches recorded = {}",
                timeline.total_launches
            );
            let _ = writeln!(
                u,
                "    distinct kernel classes = {}",
                timeline.classes.len()
            );
            let _ = writeln!(u, "    graph launches seen = {}", timeline.graphs.len());
            let _ = writeln!(u, "\n    per kernel class:");
            let _ = writeln!(
                u,
                "    {:<26} {:>8} {:>14} {:>13} {:>13} {:>22} {:>10} {:>8} {:>9} {:>12}",
                "kernel",
                "launches",
                "summed ns",
                "median ns",
                "min ns",
                "grid × block",
                "regs/thr",
                "shared",
                "threads",
                "waves/card"
            );
            for class in &timeline.classes {
                let geometry = class
                    .geometries
                    .first()
                    .map(|(g, _, _, _, _)| {
                        format!("({},{},{})×({},{},{})", g.0, g.1, g.2, g.3, g.4, g.5)
                    })
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned());
                let _ = writeln!(
                    u,
                    "    {:<26} {:>8} {:>14} {:>13} {:>13} {:>22} {:>10} {:>8} {:>9} {:>12}",
                    class.name,
                    class.launches,
                    class
                        .summed_ns
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                    class
                        .median_ns
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                    class
                        .min_ns
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                    geometry,
                    class
                        .registers_per_thread
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                    class
                        .static_shared_octets
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                    class
                        .threads_per_launch
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                    class
                        .waves_per_sm(resident_lanes)
                        .map(|w| format!("{w:.4}"))
                        .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                );
                for (g, count, med, low, high) in &class.geometries {
                    let _ = writeln!(
                        u,
                        "        geometry ({},{},{})×({},{},{}) · {count} launch(es) · median {} ns · min {} ns · max {} ns · threads {}",
                        g.0,
                        g.1,
                        g.2,
                        g.3,
                        g.4,
                        g.5,
                        med.map(|v| v.to_string())
                            .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                        low.map(|v| v.to_string())
                            .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                        high.map(|v| v.to_string())
                            .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                        g.0 * g.1.max(1) * g.2.max(1) * g.3 * g.4.max(1) * g.5.max(1)
                    );
                }
            }
            let _ = writeln!(u, "\n    per graph launch:");
            let _ = writeln!(
                u,
                "    {:>6} {:>8} {:>14} {:>15} {:>15} {:>18} {:>18} {:>14}",
                "graph",
                "kernels",
                "GPU wall ns",
                "summed kern ns",
                "union kern ns",
                "max concurrent",
                "overlap fraction",
                "census ns"
            );
            for graph in &timeline.graphs {
                let _ = writeln!(
                    u,
                    "    {:>6} {:>8} {:>14} {:>15} {:>15} {:>18} {:>18} {:>14}",
                    graph.index,
                    graph.kernels,
                    graph
                        .wall_ns
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                    graph
                        .summed_kernel_ns
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                    graph
                        .union_kernel_ns
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                    graph
                        .max_concurrent
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                    graph
                        .overlap_fraction
                        .map(|v| format!("{v:.6}"))
                        .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                    graph
                        .census_ns
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                );
            }
            let gaps = profile::inter_graph_gaps(timeline);
            let _ = writeln!(
                u,
                "\n    inter-graph CPU gaps (last kernel end of one graph → first kernel start of the next):"
            );
            for (from, to, gap, previous_wall) in &gaps {
                let _ = writeln!(
                    u,
                    "      graph {from} → {to}: gap {} ns · previous graph GPU wall {} ns",
                    gap.map(|v| v.to_string())
                        .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                    previous_wall
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| profile::UNKNOWN.to_owned())
                );
            }
            let unnamed = profile::unnamed_classes(timeline);
            if !unnamed.is_empty() {
                let _ = writeln!(
                    u,
                    "\n    kernel names present in the timeline that the rubric does not name as load-bearing: {unnamed:?}"
                );
            }
        }
    }
    let _ = writeln!(u, "\n    transfers:");
    if transfer_faces.is_empty() {
        let _ = writeln!(
            u,
            "      transfer-timeline.tsv absent or empty — transfer octets and rate unknown."
        );
    } else {
        for face in &transfer_faces {
            let _ = writeln!(
                u,
                "      {:<14} {:>6} transfer(s) · {} octets · {} ns · {} octets/s",
                face.kind,
                face.count,
                face.octets
                    .map(|v| v.to_string())
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                face.summed_ns
                    .map(|v| v.to_string())
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                face.octets_per_second
                    .map(|v| format!("{v:.0}"))
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned())
            );
        }
    }
    let _ = writeln!(u, "\n    CPU driver-API time by api (summed, descending):");
    if api_faces.is_empty() {
        let _ = writeln!(
            u,
            "      cpu-api-timeline.tsv absent or empty — CPU API time unknown."
        );
    } else {
        for face in api_faces.iter().take(30) {
            let _ = writeln!(
                u,
                "      {:<34} {:>7} call(s) · summed {} ns · median {} ns · index {}..{}",
                face.api,
                face.calls,
                face.summed_ns
                    .map(|v| v.to_string())
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                face.median_ns
                    .map(|v| v.to_string())
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                face.first_index
                    .map(|v| v.to_string())
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                face.last_index
                    .map(|v| v.to_string())
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned())
            );
        }
    }
    let build = api_faces
        .iter()
        .filter(|f| {
            f.api.contains("GraphInstantiate")
                || f.api.contains("StreamEndCapture")
                || f.api.contains("StreamBeginCapture")
        })
        .map(|f| {
            format!(
                "{} summed {} ns",
                f.api,
                f.summed_ns
                    .map(|v| v.to_string())
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned())
            )
        })
        .collect::<Vec<_>>();
    let _ = writeln!(
        u,
        "\n    graph build/instantiate: {}",
        if build.is_empty() {
            profile::UNKNOWN.to_owned()
        } else {
            build.join(" · ")
        }
    );
    let _ = writeln!(u);

    let _ = writeln!(
        u,
        "  ---------------------------------------------------------------------------"
    );
    let _ = writeln!(
        u,
        "  (iv) PHYSICAL TELEMETRY — ncu faces where the counters were reachable"
    );
    let _ = writeln!(
        u,
        "  ---------------------------------------------------------------------------"
    );
    if scheduler_faces.is_empty() {
        let _ = writeln!(
            u,
            "    scheduler-states.tsv absent or carried no measured row."
        );
        let _ = writeln!(
            u,
            "    active/eligible/issued warps, stall classes, L1/L2/DRAM throughput and achieved occupancy = unknown."
        );
        let _ = writeln!(
            u,
            "    They are unknown, not zero, and nothing in this file infers them from the timeline."
        );
    } else {
        for (name, face) in &scheduler_faces {
            let _ = writeln!(
                u,
                "    {name:<26} rows {} · active {} · eligible {} · issued {} · no-eligible% {} · stall1 {} ({}%) · L1 {} · L2 {} · DRAM% {} · SM% {} · occupancy% {}",
                face.rows,
                face.active_warps_per_cycle
                    .map(|v| format!("{v:.3}"))
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                face.eligible_warps_per_cycle
                    .map(|v| format!("{v:.3}"))
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                face.issued_warps_per_cycle
                    .map(|v| format!("{v:.3}"))
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                face.no_eligible_pct
                    .map(|v| format!("{v:.2}"))
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                face.stall_top1
                    .clone()
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                face.stall_top1_pct
                    .map(|v| format!("{v:.2}"))
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                face.l1_hit_pct
                    .map(|v| format!("{v:.2}"))
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                face.l2_hit_pct
                    .map(|v| format!("{v:.2}"))
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                face.dram_throughput_pct
                    .map(|v| format!("{v:.2}"))
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                face.sm_throughput_pct
                    .map(|v| format!("{v:.2}"))
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                face.achieved_occupancy_pct
                    .map(|v| format!("{v:.2}"))
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
            );
        }
    }
    if let Some(resources) = &resources {
        let _ = writeln!(
            u,
            "\n    kernel-resources.tsv, as A measured it ({} row(s)):",
            resources.rows.len()
        );
        for row in &resources.rows {
            let _ = writeln!(
                u,
                "      {:<26} launches {:<6} threads/launch {:<10} warps/block {:<6} theoretical occ% {:<8} achieved occ% {:<8} blocks/SM {:<6} waves/SM {:<8} source {}",
                resources.cell(row, "kernel"),
                resources.cell(row, "launches"),
                resources.cell(row, "threads_per_launch"),
                resources.cell(row, "warps_per_block"),
                resources.cell(row, "theoretical_occupancy_pct"),
                resources.cell(row, "achieved_occupancy_pct"),
                resources.cell(row, "resident_blocks_per_sm"),
                resources.cell(row, "waves_per_sm"),
                resources.cell(row, "source"),
            );
        }
    } else {
        let _ = writeln!(
            u,
            "\n    kernel-resources.tsv absent — per-kernel occupancy and residency unknown."
        );
    }
    let _ = writeln!(
        u,
        "\n    nvidia-smi coarse sample: COARSE — a whole-card poll at whole-second granularity is not"
    );
    let _ = writeln!(
        u,
        "    scheduler or resource telemetry and never substitutes for one. If A recorded one it is in"
    );
    let _ = writeln!(u, "    calibration.form; this file does not promote it.");
    let _ = writeln!(u);

    // the permission-versus-overlap sentence, stated explicitly
    let _ = writeln!(
        u,
        "  ---------------------------------------------------------------------------"
    );
    let _ = writeln!(u, "  GRAPH PERMISSION VERSUS MEASURED OVERLAP");
    let _ = writeln!(
        u,
        "  ---------------------------------------------------------------------------"
    );
    for layer in LAYERS_CONDUCTED {
        let schedule = forms.get(&format!("layer{layer}.schedule"));
        let plural = forms.get(&format!("layer{layer}.fronts_with_two_or_more_members"));
        let fronts = forms.get(&format!("layer{layer}.fronts"));
        let (concurrent, fraction) = match &timeline {
            Some(timeline) if !timeline.graphs.is_empty() => {
                let graph = timeline
                    .graphs
                    .iter()
                    .find(|g| g.index == layer as u64)
                    .or_else(|| timeline.graphs.first());
                match graph {
                    Some(g) => (
                        g.max_concurrent
                            .map(|v| v.to_string())
                            .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                        g.overlap_fraction
                            .map(|v| format!("{v:.6}"))
                            .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                    ),
                    None => (profile::UNKNOWN.to_owned(), profile::UNKNOWN.to_owned()),
                }
            }
            _ => (profile::UNKNOWN.to_owned(), profile::UNKNOWN.to_owned()),
        };
        let _ = writeln!(
            u,
            "    layer {layer}: graph permission (schedule {schedule}, {plural} of {fronts} fronts with two or more members) versus measured overlap (max concurrent kernels {concurrent}, overlap fraction {fraction})."
        );
    }
    let _ = writeln!(
        u,
        "    Permission is a property of the diagram the passage certified. Overlap is a property of what"
    );
    let _ = writeln!(
        u,
        "    the card did. They are different objects and this file never reads one as the other."
    );
    write_form(dir, "surface-utility.form", &u)?;

    // ---------------------------------------------------------------- profile.form
    let mut rows: Vec<profile::Classification> = Vec::new();
    if let Some(timeline) = &timeline {
        let total: usize = timeline.classes.iter().map(|c| c.launches).sum();
        let equal_share = if timeline.classes.is_empty() {
            None
        } else {
            Some(1.0 / timeline.classes.len() as f64)
        };
        for class in &timeline.classes {
            let share = if total == 0 {
                None
            } else {
                Some(class.launches as f64 / total as f64)
            };
            rows.push(profile::classify_kernel(
                class,
                resident_lanes,
                share,
                equal_share,
                scheduler_faces.get(&class.name),
            ));
        }
    }
    // the boundaries
    let mut boundary_rows: Vec<profile::Classification> = Vec::new();
    match &timeline {
        None => {
            for object in [
                "boundary: source read + mount",
                "boundary: bind/instantiate",
                "boundary: launch → sync",
                "boundary: release",
                "boundary: inter-layer CPU gap",
                "boundary: H2D transfers",
            ] {
                boundary_rows.push(profile::classify_boundary(
                    object,
                    None,
                    None,
                    None,
                    vec![(
                        "telemetry".to_owned(),
                        "kernel-timeline.tsv absent".to_owned(),
                    )],
                    profile::UNKNOWN.to_owned(),
                ));
            }
        }
        Some(timeline) => {
            let gaps = profile::inter_graph_gaps(timeline);
            let foreman: Option<bool> = if gaps.is_empty() {
                None
            } else {
                let decided: Vec<bool> = gaps
                    .iter()
                    .filter_map(|(_, _, gap, wall)| match (gap, wall) {
                        (Some(g), Some(w)) => Some(*g >= *w),
                        _ => None,
                    })
                    .collect();
                if decided.is_empty() {
                    None
                } else {
                    Some(decided.iter().filter(|d| **d).count() * 2 >= decided.len())
                }
            };
            let gap_detail = gaps
                .iter()
                .map(|(a, b, gap, wall)| {
                    format!(
                        "{a}→{b}: gap {} vs previous GPU wall {}",
                        gap.map(|v| v.to_string())
                            .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                        wall.map(|v| v.to_string())
                            .unwrap_or_else(|| profile::UNKNOWN.to_owned())
                    )
                })
                .collect::<Vec<_>>()
                .join(" · ");
            boundary_rows.push(profile::classify_boundary(
                "boundary: inter-layer CPU gap (sync return → next graph launch)",
                foreman,
                None,
                None,
                vec![
                    ("gaps_measured".to_owned(), gaps.len().to_string()),
                    (
                        "rule".to_owned(),
                        "gap >= the previous graph's GPU wall, on the majority of measured gaps"
                            .to_owned(),
                    ),
                    (
                        "gaps".to_owned(),
                        if gap_detail.is_empty() {
                            profile::UNKNOWN.to_owned()
                        } else {
                            gap_detail
                        },
                    ),
                ],
                "kernel-timeline.tsv, all graph_launch_index groups".to_owned(),
            ));

            // census overhead per graph
            let mut census_flags: Vec<bool> = Vec::new();
            let mut census_detail: Vec<String> = Vec::new();
            for graph in &timeline.graphs {
                if let (Some(census), Some(wall)) = (graph.census_ns, graph.wall_ns) {
                    if wall > 0 {
                        let share = census as f64 / wall as f64;
                        census_flags.push(share >= 0.30);
                        census_detail.push(format!(
                            "graph {}: census {census} ns / wall {wall} ns = {share:.4}",
                            graph.index
                        ));
                    }
                }
            }
            let census_bound = if census_flags.is_empty() {
                None
            } else {
                Some(census_flags.iter().filter(|c| **c).count() * 2 >= census_flags.len())
            };
            boundary_rows.push(profile::classify_boundary(
                "per graph: census kernels' share of the graph's GPU wall",
                None,
                None,
                census_bound,
                vec![
                    (
                        "rule".to_owned(),
                        "census summed duration / graph GPU wall >= 0.30".to_owned(),
                    ),
                    (
                        "measured".to_owned(),
                        if census_detail.is_empty() {
                            profile::UNKNOWN.to_owned()
                        } else {
                            census_detail.join(" · ")
                        },
                    ),
                ],
                "kernel-timeline.tsv, kernel names beginning section_census".to_owned(),
            ));

            // transfers
            let h2d = transfer_faces.iter().find(|f| f.kind.contains("htod"));
            let slow = match (h2d.and_then(|f| f.octets_per_second), pcie_nominal) {
                (Some(rate), Some(nominal)) if nominal > 0 => Some(rate <= 0.25 * nominal as f64),
                _ => None,
            };
            let overlap = match (&kernels, &transfers) {
                (Some(k), Some(tr)) => profile::transfer_overlap(k, tr, "htod"),
                _ => None,
            };
            let overlap_fraction =
                overlap.and_then(|(o, total)| (total > 0).then(|| o as f64 / total as f64));
            // the rubric's second clause: transfers serialize with compute. Serialized means the
            // transfer time concurrent with ANY kernel is under one percent of it.
            let serialized = overlap_fraction.map(|f| f < 0.01);
            let transfer_bound = match (slow, serialized) {
                (Some(a), Some(b)) => Some(a || b),
                (Some(a), None) => Some(a),
                (None, Some(b)) => Some(b),
                _ => None,
            };
            boundary_rows.push(profile::classify_boundary(
                "boundary: H2D transfers",
                None,
                transfer_bound,
                None,
                vec![
                    ("h2d_octets".to_owned(), h2d.and_then(|f| f.octets).map(|v| v.to_string()).unwrap_or_else(|| profile::UNKNOWN.to_owned())),
                    ("h2d_octets_per_second".to_owned(), h2d.and_then(|f| f.octets_per_second).map(|v| format!("{v:.0}")).unwrap_or_else(|| profile::UNKNOWN.to_owned())),
                    ("pcie_nominal_octets_per_second".to_owned(), pcie_nominal.map(|v| v.to_string()).unwrap_or_else(|| profile::UNKNOWN.to_owned())),
                    ("rule_a".to_owned(), "measured H2D rate <= 25% of the PCIe gen4 x16 nominal".to_owned()),
                    ("rule_a_holds".to_owned(), slow.map(|v| v.to_string()).unwrap_or_else(|| profile::UNKNOWN.to_owned())),
                    (
                        "h2d_time_concurrent_with_any_kernel".to_owned(),
                        overlap.map(|(o, total)| format!("{o} ns of {total} ns")).unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                    ),
                    ("h2d_overlap_fraction".to_owned(), overlap_fraction.map(|v| format!("{v:.6}")).unwrap_or_else(|| profile::UNKNOWN.to_owned())),
                    ("rule_b".to_owned(), "transfers serialize with compute: under 1% of H2D time is concurrent with any kernel".to_owned()),
                    ("rule_b_holds".to_owned(), serialized.map(|v| v.to_string()).unwrap_or_else(|| profile::UNKNOWN.to_owned())),
                ],
                "transfer-timeline.tsv kind memcpy_htod, intersected with every kernel interval of kernel-timeline.tsv".to_owned(),
            ));

            // the four span boundaries. Each is a component of the same inter-graph gap, so the
            // CPU-FOREMAN test is the rubric's own rule applied per graph launch: the boundary's
            // summed api time divided by the number of graph launches, against the MEDIAN graph
            // GPU wall. launch→sync is excluded from that test by construction and the reason is
            // printed: a blocking synchronize contains the card's own execution, so its duration is
            // not CPU work and reading it as such would manufacture the verdict.
            let graph_count = timeline.graphs.len().max(1) as u64;
            let mut walls: Vec<u64> = timeline.graphs.iter().filter_map(|g| g.wall_ns).collect();
            walls.sort_unstable();
            let median_wall = walls.get(walls.len() / 2).copied();
            for (object, apis, foreman_applicable) in [
                (
                    "boundary: source read + mount (cuMemAlloc / cuMemcpyHtoD cluster)",
                    vec!["cuMemAlloc", "cuMemcpyHtoD"],
                    true,
                ),
                (
                    "boundary: bind/instantiate (cuStreamBeginCapture .. cuGraphInstantiate)",
                    vec![
                        "cuStreamBeginCapture",
                        "cuStreamEndCapture",
                        "cuGraphInstantiate",
                    ],
                    true,
                ),
                (
                    "boundary: launch → sync (cuGraphLaunch .. cuStreamSynchronize)",
                    vec!["cuGraphLaunch", "cuStreamSynchronize"],
                    false,
                ),
                (
                    "boundary: release (cuMemFree cluster)",
                    vec!["cuMemFree"],
                    true,
                ),
            ] {
                let mut deciding: Vec<(String, String)> = Vec::new();
                let mut any = false;
                let mut summed = 0u64;
                let mut complete = true;
                for api in &apis {
                    match api_faces.iter().find(|f| f.api.contains(api)) {
                        Some(face) => {
                            any = true;
                            match face.summed_ns {
                                Some(ns) => summed += ns,
                                None => complete = false,
                            }
                            deciding.push((
                                (*api).to_owned(),
                                format!(
                                    "{} call(s), summed {} ns, median {} ns",
                                    face.calls,
                                    face.summed_ns
                                        .map(|v| v.to_string())
                                        .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                                    face.median_ns
                                        .map(|v| v.to_string())
                                        .unwrap_or_else(|| profile::UNKNOWN.to_owned())
                                ),
                            ));
                        }
                        None => {
                            complete = false;
                            deciding.push(((*api).to_owned(), profile::UNKNOWN.to_owned()));
                        }
                    }
                }
                let per_graph = (complete && any).then(|| summed / graph_count);
                deciding.push((
                    "summed_per_graph_launch_ns".to_owned(),
                    per_graph
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                ));
                deciding.push((
                    "median_graph_gpu_wall_ns".to_owned(),
                    median_wall
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                ));
                let foreman = if foreman_applicable {
                    match (per_graph, median_wall) {
                        (Some(cpu), Some(wall)) => Some(cpu >= wall),
                        _ => None,
                    }
                } else {
                    deciding.push((
                        "cpu_foreman_test".to_owned(),
                        "not applicable — a blocking synchronize contains the card's own execution, so this span is not CPU work".to_owned(),
                    ));
                    None
                };
                if foreman_applicable {
                    deciding.push((
                        "cpu_foreman_test".to_owned(),
                        "the boundary's summed api time per graph launch >= the median graph GPU wall".to_owned(),
                    ));
                }
                let mut row = profile::classify_boundary(
                    object,
                    foreman,
                    None,
                    None,
                    deciding,
                    if any {
                        "cpu-api-timeline.tsv, rows whose api matches the names above".to_owned()
                    } else {
                        profile::UNKNOWN.to_owned()
                    },
                );
                if !foreman_applicable && any {
                    // its durations were measured; no class of the rubric can apply to it
                    row.class = "NOT-APPLICABLE (every rubric class is about CPU work, a transfer or a kernel; this span contains the card's own execution)".to_owned();
                    row.confidence =
                        "measured (durations present; the rubric defines no class for this span)"
                            .to_owned();
                    row.verdict = format!("{object} → {}", row.class);
                }
                boundary_rows.push(row);
            }
        }
    }

    let mut p = String::new();
    let _ = writeln!(
        p,
        "PROFILE — one attributable classification per load-bearing kernel class and per boundary"
    );
    let _ = writeln!(
        p,
        "The rubric was declared BEFORE the measurement and is applied here as code, not as prose. For each"
    );
    let _ = writeln!(
        p,
        "object the FIRST class that applies in the rubric's order decides; every other class that also"
    );
    let _ = writeln!(
        p,
        "applied is listed as secondary. A class whose deciding metric is an ncu-only face is neither"
    );
    let _ = writeln!(
        p,
        "asserted nor denied when ncu could not run: it stays unknown and the metric is named.\n"
    );
    let _ = writeln!(p, "  rubric order: {}", profile::RUBRIC_ORDER.join(" > "));
    let _ = writeln!(
        p,
        "  operationalizations this join declares, so the rubric is reproducible:"
    );
    let _ = writeln!(
        p,
        "    LAUNCH-LATENCY-BOUND · 'the kernel count per graph dominates' = the class's share of all kernel"
    );
    let _ = writeln!(
        p,
        "      launches is at or above the equal share 1/(number of distinct classes)."
    );
    let _ = writeln!(
        p,
        "    UNDER-PARALLEL · waves per card = threads in a launch ÷ (SMs × max threads per SM), the card's"
    );
    let _ = writeln!(
        p,
        "      own two attributes. A class launched at several geometries has no single answer, so the"
    );
    let _ = writeln!(
        p,
        "      POPULATION decides: the class carries the term when a MAJORITY of its launches are below one"
    );
    let _ = writeln!(
        p,
        "      wave. Both the population and the widest launch's figure are printed, never one alone."
    );
    let _ = writeln!(
        p,
        "    INNER-SERIAL · the inner dimension K is in NO telemetry column. What is measurable is launches"
    );
    let _ = writeln!(
        p,
        "      at the IDENTICAL grid and block — hence the identical output count — whose durations differ by"
    );
    let _ = writeln!(
        p,
        "      ≥ 2×; that is the deciding metric, and it is evidence CONSISTENT WITH K-scaling, not a"
    );
    let _ = writeln!(p, "      measurement of it.");
    let _ = writeln!(
        p,
        "    CPU-FOREMAN-BOUND · for the inter-graph gap: gap ≥ the previous graph's GPU wall on the majority"
    );
    let _ = writeln!(
        p,
        "      of measured gaps. For a named api span: its summed time per graph launch ≥ the median graph"
    );
    let _ = writeln!(
        p,
        "      GPU wall. The launch→sync span is excluded from that test by construction, because a blocking"
    );
    let _ = writeln!(
        p,
        "      synchronize contains the card's own execution and reading it as CPU work would manufacture it."
    );
    let _ = writeln!(
        p,
        "    CENSUS-OVERHEAD · census summed duration ÷ graph GPU wall ≥ 0.30 on the majority of graphs."
    );
    let _ = writeln!(
        p,
        "    TRANSFER-BOUND · either clause of the rubric: measured H2D octets/second ≤ 25% of the PCIe gen4"
    );
    let _ = writeln!(
        p,
        "      x16 nominal, OR the transfers serialize with compute — under 1% of H2D time concurrent with any"
    );
    let _ = writeln!(
        p,
        "      kernel, taken by intersecting the transfer intervals with the union of the kernel intervals.\n"
    );
    let _ = writeln!(
        p,
        "  device capacities the rubric read (from source-and-mode.form, which read them from the device):"
    );
    let _ = writeln!(
        p,
        "    device.multiprocessors = {}",
        sms.map(|v| v.to_string())
            .unwrap_or_else(|| profile::UNKNOWN.to_owned())
    );
    let _ = writeln!(
        p,
        "    device.max_threads_per_multiprocessor = {}",
        threads_per_sm
            .map(|v| v.to_string())
            .unwrap_or_else(|| profile::UNKNOWN.to_owned())
    );
    let _ = writeln!(
        p,
        "    device.resident_lanes = {}",
        resident_lanes
            .map(|v| v.to_string())
            .unwrap_or_else(|| profile::UNKNOWN.to_owned())
    );
    let _ = writeln!(
        p,
        "    pcie.nominal_octets_per_second = {}\n",
        pcie_nominal
            .map(|v| v.to_string())
            .unwrap_or_else(|| profile::UNKNOWN.to_owned())
    );

    let _ = writeln!(
        p,
        "================================================================================"
    );
    let _ = writeln!(p, "KERNEL CLASSES");
    let _ = writeln!(
        p,
        "================================================================================"
    );
    if rows.is_empty() {
        let _ = writeln!(
            p,
            "  kernel-timeline.tsv absent or empty — NO kernel class could be classified. Every load-bearing"
        );
        let _ = writeln!(
            p,
            "  class named by the rubric is `unknown`, with the reason that the timeline was not present:"
        );
        for name in profile::LOAD_BEARING {
            let _ = writeln!(p, "    {name:<26} → unknown (kernel-timeline.tsv absent)");
        }
        let _ = writeln!(
            p,
            "    {:<26} → unknown (kernel-timeline.tsv absent)",
            format!("{}*", profile::MOUNT_PREFIX)
        );
    }
    for row in &rows {
        let load_bearing = profile::LOAD_BEARING.contains(&row.object.as_str())
            || row.object.starts_with(profile::MOUNT_PREFIX);
        let _ = writeln!(
            p,
            "\n  ---- {} {}",
            row.object,
            if load_bearing {
                "(load-bearing by the rubric)"
            } else {
                "(not named load-bearing; classified anyway)"
            }
        );
        let _ = writeln!(p, "       class          {}", row.class);
        let _ = writeln!(
            p,
            "       secondary      {}",
            if row.secondary.is_empty() {
                "none".to_owned()
            } else {
                row.secondary.join(", ")
            }
        );
        let _ = writeln!(p, "       confidence     {}", row.confidence);
        let _ = writeln!(p, "       rows cited     {}", row.cited);
        let _ = writeln!(p, "       deciding metrics:");
        for (name, value) in &row.deciding {
            let _ = writeln!(p, "         {name:<36} {value}");
        }
        if row.ncu_needed_for.is_empty() {
            let _ = writeln!(
                p,
                "       ncu needed for none — every deciding metric was reachable"
            );
        } else {
            for need in &row.ncu_needed_for {
                let _ = writeln!(p, "       ncu needed for {need}");
            }
        }
    }
    if let (Some(resources), Some(timeline)) = (&resources, &timeline) {
        let _ = writeln!(
            p,
            "\n  CROSS-CHECK — this join recomputes waves per card from kernel-timeline.tsv; A's"
        );
        let _ = writeln!(
            p,
            "  kernel-resources.tsv states its own waves_per_sm. Both are threads ÷ (SMs × threads per SM),"
        );
        let _ = writeln!(
            p,
            "  so they must agree per geometry. Disagreement is a defect of one of the two readings."
        );
        for row in &resources.rows {
            let kernel = resources.cell(row, "kernel");
            let stated = resources.cell(row, "waves_per_sm");
            let threads = resources.u64_at(row, "threads_per_launch");
            let recomputed = match (threads, resident_lanes) {
                (Some(t), Some(l)) if l > 0 => format!("{:.6}", t as f64 / l as f64),
                _ => profile::UNKNOWN.to_owned(),
            };
            let agrees = match (stated.parse::<f64>(), recomputed.parse::<f64>()) {
                (Ok(a), Ok(b)) => format!("{}", (a - b).abs() < 1e-4),
                _ => profile::UNKNOWN.to_owned(),
            };
            let _ = writeln!(
                p,
                "    {kernel:<26} threads {:<10} A states {stated:<12} recomputed {recomputed:<12} agree {agrees}",
                threads
                    .map(|v| v.to_string())
                    .unwrap_or_else(|| profile::UNKNOWN.to_owned())
            );
        }
        let _ = writeln!(
            p,
            "    (kernel-resources.tsv carries {} geometry row(s); the timeline carries {} class(es))",
            resources.rows.len(),
            timeline.classes.len()
        );
    }

    let _ = writeln!(
        p,
        "\n================================================================================"
    );
    let _ = writeln!(p, "BOUNDARIES");
    let _ = writeln!(
        p,
        "================================================================================"
    );
    for row in &boundary_rows {
        let _ = writeln!(p, "\n  ---- {}", row.object);
        let _ = writeln!(p, "       class          {}", row.class);
        let _ = writeln!(
            p,
            "       secondary      {}",
            if row.secondary.is_empty() {
                "none".to_owned()
            } else {
                row.secondary.join(", ")
            }
        );
        let _ = writeln!(p, "       confidence     {}", row.confidence);
        let _ = writeln!(p, "       rows cited     {}", row.cited);
        for (name, value) in &row.deciding {
            let _ = writeln!(p, "         {name:<36} {value}");
        }
    }
    let _ = writeln!(
        p,
        "\n================================================================================"
    );
    let _ = writeln!(p, "VERDICTS — one line per object");
    let _ = writeln!(
        p,
        "================================================================================"
    );
    for row in rows.iter().chain(boundary_rows.iter()) {
        let _ = writeln!(p, "  {} [{}]", row.verdict, row.confidence);
    }
    if let Some(calibration) = &calibration {
        let _ = writeln!(
            p,
            "\ncalibration.form was present ({} octets); its tool versions, timebases, overhead measurement and",
            calibration.len()
        );
        let _ = writeln!(
            p,
            "its statement of what could not be measured are the frame every row above was taken in."
        );
    } else {
        let _ = writeln!(
            p,
            "\ncalibration.form was ABSENT. Every duration above is therefore on an undeclared timebase and no"
        );
        let _ = writeln!(
            p,
            "profiler-overhead figure exists for this reading. That is a defect of the join, stated rather than"
        );
        let _ = writeln!(
            p,
            "hidden: a measurement without its frame is not a measurement."
        );
    }
    write_form(dir, "profile.form", &p)?;

    // ---------------------------------------------------------------- pressure-joined.form
    let mut j = String::new();
    let _ = writeln!(
        j,
        "PRESSURE, JOINED — the demand columns the exterior telemetry supplied"
    );
    let _ = writeln!(
        j,
        "This file does not overwrite pressure.form: that one is what the passage itself returned, and this"
    );
    let _ = writeln!(
        j,
        "one is that reading with the exterior apparatus's demand columns filled where it measured them."
    );
    let _ = writeln!(
        j,
        "Every species stays a separate coordinate. R = ceil(N / C). Nothing is summed.\n"
    );
    let _ = writeln!(
        j,
        "  the resident-lane species, as the passage returned it (unchanged):"
    );
    for layer in LAYERS_CONDUCTED {
        for key in [
            format!("layer{layer}.traffic.resident_lanes"),
            format!("layer{layer}.traffic.deferred_arrivals"),
            format!("layer{layer}.traffic.reconvergent_sites"),
        ] {
            let _ = writeln!(j, "    {key} = {}", forms.get(&key));
        }
    }
    let _ = writeln!(
        j,
        "\n  the apparatus species, with demand from telemetry where it exists:"
    );
    let _ = writeln!(
        j,
        "    {:<58} {:>20} {:>20} {:>14}",
        "species", "C", "N (measured)", "R = ceil(N/C)"
    );
    let mut species_rows: Vec<(String, String, String)> = Vec::new();
    match &timeline {
        Some(timeline) => {
            for class in &timeline.classes {
                let regs = class.registers_per_thread;
                let block_threads = class
                    .geometries
                    .first()
                    .map(|(g, _, _, _, _)| g.3 * g.4.max(1) * g.5.max(1));
                let per_block = match (regs, block_threads) {
                    (Some(r), Some(t)) => Some(r * t),
                    _ => None,
                };
                species_rows.push((
                    format!("32-bit registers, block of {}", class.name),
                    forms
                        .get("device.attribute.max_registers_per_multiprocessor")
                        .to_owned(),
                    per_block
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                ));
                let shared = match (class.static_shared_octets, class.dynamic_shared_octets) {
                    (Some(a), Some(b)) => Some(a + b),
                    (Some(a), None) => Some(a),
                    (None, Some(b)) => Some(b),
                    _ => None,
                };
                species_rows.push((
                    format!("shared-memory octets, block of {}", class.name),
                    forms
                        .get("device.attribute.max_shared_octets_per_multiprocessor")
                        .to_owned(),
                    shared
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                ));
                species_rows.push((
                    format!("resident threads, WIDEST launch of {}", class.name),
                    forms.get("device.resident_lanes").to_owned(),
                    class
                        .threads_per_launch
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                ));
                species_rows.push((
                    format!("resident threads, NARROWEST launch of {}", class.name),
                    forms.get("device.resident_lanes").to_owned(),
                    class
                        .threads_per_launch_min
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
                ));
            }
        }
        None => {
            for species in [
                "32-bit registers per SM",
                "shared-memory octets per SM",
                "resident threads per SM",
            ] {
                species_rows.push((
                    species.to_owned(),
                    profile::UNKNOWN.to_owned(),
                    profile::UNKNOWN.to_owned(),
                ));
            }
        }
    }
    let h2d = transfer_faces.iter().find(|f| f.kind.contains("htod"));
    species_rows.push((
        "PCIe octets per second".to_owned(),
        pcie_nominal
            .map(|v| v.to_string())
            .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
        h2d.and_then(|f| f.octets_per_second)
            .map(|v| format!("{v:.0}"))
            .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
    ));
    species_rows.push((
        "DRAM octets per second".to_owned(),
        forms
            .get("device.dram_nominal_octets_per_second")
            .split_whitespace()
            .next()
            .unwrap_or(profile::UNKNOWN)
            .to_owned(),
        profile::UNKNOWN.to_owned(),
    ));
    species_rows.push((
        "copy engines (transfers in flight at once)".to_owned(),
        forms.get("device.attribute.async_engine_count").to_owned(),
        transfers
            .as_ref()
            .and_then(profile::max_concurrent_transfers)
            .map(|v| v.to_string())
            .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
    ));
    if let Some(process) = &process {
        let reads: Vec<u64> = process
            .rows
            .iter()
            .filter_map(|r| process.u64_at(r, "io_read_octets"))
            .collect();
        species_rows.push((
            "CPU I/O read octets".to_owned(),
            profile::UNKNOWN.to_owned(),
            reads
                .iter()
                .max()
                .map(|v| v.to_string())
                .unwrap_or_else(|| profile::UNKNOWN.to_owned()),
        ));
    } else {
        species_rows.push((
            "CPU I/O read octets".to_owned(),
            profile::UNKNOWN.to_owned(),
            profile::UNKNOWN.to_owned(),
        ));
    }
    for (species, c, n) in &species_rows {
        let r = match (c.parse::<u64>(), n.parse::<u64>()) {
            (Ok(c), Ok(n)) if c > 0 => n.div_ceil(c).to_string(),
            _ => profile::UNKNOWN.to_owned(),
        };
        let _ = writeln!(j, "    {species:<58} {c:>20} {n:>20} {r:>14}");
    }
    let _ = writeln!(
        j,
        "\n  A row whose C or N is unknown has an unknown R. It is never 0 and never 1."
    );
    write_form(dir, "pressure-joined.form", &j)?;

    println!(
        "\n  the join is complete. Rows classified: {} kernel class(es), {} boundary object(s).",
        rows.len(),
        boundary_rows.len()
    );
    for row in rows.iter().chain(boundary_rows.iter()) {
        println!("    {} [{}]", row.verdict, row.confidence);
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------------

fn main() {
    let args = parse_args();
    let mut clock = Clockings(Vec::new());
    std::fs::create_dir_all(&args.out).expect("output directory");

    if args.receipts {
        println!("THE SCALAR PATH RETURNS ITS PRESSURE AND UTILITY — Deed H0, the semantic half");
        let whole = Instant::now();
        let commit = exterior("git", &["rev-parse", "HEAD"]);
        println!("  closure commit {commit}");

        let readout: &'static ResidentReadout = match ResidentReadout::new() {
            Ok(readout) => Box::leak(Box::new(readout)),
            Err(error) => {
                println!("REFUSED: no resident chart — {error}");
                std::process::exit(3);
            }
        };
        let surface: &'static ResidentSurface<'static> = match ResidentSurface::on(readout) {
            Ok(surface) => Box::leak(Box::new(surface)),
            Err(error) => {
                println!("REFUSED: the resident laws did not load — {error}");
                std::process::exit(3);
            }
        };
        println!(
            "  resident chart: {} · mode kernel content {} · allocation grain {} · memory {} free of {}",
            surface.device_name(),
            surface.mode().kernel_content.as_deref().unwrap_or("?"),
            surface.allocation_grain(),
            surface.memory_at_mount().free_bytes,
            surface.memory_at_mount().total_bytes
        );
        let capacities = read_device_capacities();
        let pcie = (
            exterior(
                "nvidia-smi",
                &["--query-gpu=pcie.link.gen.max", "--format=csv,noheader"],
            ),
            exterior(
                "nvidia-smi",
                &["--query-gpu=pcie.link.width.max", "--format=csv,noheader"],
            ),
        );

        let open_clock = Instant::now();
        let mut source = Source::open(&args.root).expect("source opens");
        let mut header_regions: BTreeMap<String, RegionIdentity> = BTreeMap::new();
        for name in source.container.names() {
            if let Ok(region) = source.region(name, None) {
                header_regions.insert(name.to_owned(), region);
            }
        }
        clock.record(
            &format!(
                "open the container and identify {} regions from its header",
                header_regions.len()
            ),
            open_clock.elapsed().as_secs_f64(),
            "opened",
        );

        let content_sha256 = if args.content_digest {
            let digest_clock = Instant::now();
            let digest = holonic_engine::source_occurrence::AuthenticatedContainer::digest_whole(
                &format!("{}/model.safetensors", args.root),
            )
            .expect("digest");
            clock.record(
                &format!(
                    "digest the whole 16 GB container (sha256 {}…)",
                    &digest[..16]
                ),
                digest_clock.elapsed().as_secs_f64(),
                "digested",
            );
            Some(digest)
        } else {
            None
        };

        println!(
            "\n  CONDUCTING layers {LAYERS_CONDUCTED:?} — layer {REPRESENTATIVE_LAYER} is the representative"
        );
        let (profiles, occurrence) = match conduct_layers(
            surface,
            readout,
            &mut source,
            &args.root,
            &header_regions,
            content_sha256.as_deref(),
            &args.tokens,
            ResidentGrain(args.grain),
            SeriesAperture(args.terms),
            args.chart,
            &mut clock,
        ) {
            Ok(returned) => returned,
            Err(error) => {
                println!("REFUSED: {error}");
                std::process::exit(4);
            }
        };

        for p in &profiles {
            println!(
                "  layer {:>2} {:?} {:?} {:?}: {} fronts · {} members · {} plural fronts · graph {}/{} (intended {}/{}) · captured launches {} · stood {} · a-priori held {}",
                p.layer,
                p.species,
                p.role,
                p.entry,
                p.fronts.len(),
                p.members(),
                p.plural_fronts(),
                p.graph_nodes,
                p.graph_edges,
                p.intended_nodes,
                p.intended_edges,
                p.apparatus.captured_launches,
                p.stood,
                p.a_priori_held
            );
            println!(
                "           deed work {:?}",
                p.deed
                    .coordinates()
                    .iter()
                    .map(|(n, v)| format!("{n}={v}"))
                    .collect::<Vec<_>>()
            );
            println!(
                "           traffic: resident lanes {} · fronts {} · earliest arrival {} · deferred arrivals {} · reconvergent sites {} · junctions {}",
                p.traffic.resident_lanes,
                p.traffic.fronts.len(),
                p.traffic.earliest_arrival,
                p.traffic.deferred_arrivals,
                p.traffic.reconvergent_sites,
                p.traffic.junctions.len()
            );
            println!(
                "           admission: {} semantic + {} apparatus coordinates, {} bounded, {} unbounded, admitted {}",
                p.admission.semantic.len(),
                p.admission.apparatus.len(),
                p.admission.bounded().count(),
                p.admission.unbounded().count(),
                p.admission.is_admitted()
            );
        }

        let mode = surface.mode();
        clock.record(
            "the whole --receipts pass",
            whole.elapsed().as_secs_f64(),
            "complete",
        );
        let source_form = source_and_mode_form(
            &commit,
            &args,
            &occurrence,
            &mode,
            surface,
            &capacities,
            pcie,
            &clock,
        );
        write_form(&args.out, "source-and-mode.form", &source_form).expect("source-and-mode.form");
        write_form(
            &args.out,
            "causal-fronts.form",
            &causal_fronts_form(&profiles),
        )
        .expect("causal-fronts.form");
        write_form(&args.out, "exact-work.form", &exact_work_form(&profiles))
            .expect("exact-work.form");
        write_form(
            &args.out,
            "pressure.form",
            &pressure_form(&profiles, &capacities, surface),
        )
        .expect("pressure.form");
        println!("\n  the semantic half is complete. The exterior telemetry joins it with --join.");
    }

    if args.join {
        let dir = args.telemetry.clone().unwrap_or_else(|| args.out.clone());
        println!("\nTHE SCALAR PATH RETURNS ITS PRESSURE AND UTILITY — Deed H0, the join");
        if let Err(error) = join(&dir) {
            println!("REFUSED: {error}");
            std::process::exit(5);
        }
    }
}
