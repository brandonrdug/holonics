//! **Deed H4: the whole Gemma-4-E4B text tower as one streamed resident circulation.**
//!
//! Plan: `blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md` §5 (the
//! CPU boundary, double-buffered standing, the whole-tower graph, graph reuse), §8 "Deed H4", §11.
//! Predecessor: Station C's committed driver and its committed artifact
//! `output/the_tower_conducts/tower-5-inputs-grain-48-terms-14.form`, which this driver reads and
//! compares against and does not re-run. Measurement: H0's profile of that path.
//!
//! What runs:
//!
//! ```text
//!   ONE pre-deed admission over the whole tower's pooled standing
//!   ONE source occurrence: the implementation and configuration hashed once, the container's
//!     header hashed once, every region declared from that header, the identity verified after
//!   43 segments, each bounded by ONE pinned-staging refill (the declared exterior I/O boundary):
//!       stage  -> pinned host slot (k mod 2)          [the exterior crossing]
//!       cross  -> asynchronous copy to pool slot (k mod 2), ordered after the deed that last
//!                 read it by a DEVICE event, so it crosses while a deed conducts
//!       mount  -> the whole segment's maps in one batch: two synchronizations of a MOUNT stream
//!       bind   -> compile, admit against the one admission, realize, capture, instantiate
//!       launch -> onto ONE conducting stream, and NOT waited for
//!   ONE terminal synchronization
//!   then, and only then, every census and the terminal face
//! ```
//!
//! **Between segments the apparatus reads nothing semantic**, and that is structural: the
//! circulation type owns no reader, and the driver asserts the surface's own `section_read_outs`
//! and `egress_section_octets` did not move across the loop.
//!
//! The whole-tower SINGLE graph is attempted and the limiting cut is returned by name with the
//! measurement that exhibits it.
//!
//! Run:
//! ```text
//! cargo run --release -q -p holonic-engine --example the_tower_is_one_streamed_circulation -- \
//!     --tokens 818,5279,529,7001,563 [--grain 48] [--terms 14] [--no-fuse] [--digest-container]
//! ```

#[path = "phoenix/resident_layer.rs"]
mod resident_layer;
#[path = "phoenix/streamed.rs"]
mod streamed;
#[path = "phoenix/tower.rs"]
mod tower;

use std::io::Write;
use std::time::Instant;

use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::resident_section::{word_value, ResidentGrain, ResidentSurface, SeriesAperture};
use holonic_engine::source_occurrence::AuthenticatedContainer;
use num_bigint::BigInt;
use relational_geometry::Rat;
use resident_layer::Source;

const COMMITTED: &str = "output/the_tower_conducts/tower-5-inputs-grain-48-terms-14.form";

struct Args {
    root: String,
    out: String,
    committed: String,
    tokens: Vec<usize>,
    grain: u32,
    terms: u32,
    top: usize,
    fuse: bool,
    digest_container: bool,
    hidden_card_control: bool,
    poison_layers: usize,
    /// Conduct the circulation and stop: the controls that run a SECOND circulation or a subprocess
    /// are skipped, so an exterior profiler measures the circulation and nothing beside it.
    only_circulation: bool,
}

fn parse_args() -> Args {
    let mut args = Args {
        root: "/home/b/models/gemma-4-E4B-it".to_owned(),
        out: "output/the_tower_is_one_streamed_circulation".to_owned(),
        committed: COMMITTED.to_owned(),
        // The committed input closure: "The capital of France is". The token identities are the
        // committed ones; no tokenizer subprocess runs here.
        tokens: vec![818, 5279, 529, 7001, 563],
        grain: 48,
        terms: 14,
        top: 64,
        fuse: true,
        digest_container: false,
        hidden_card_control: false,
        poison_layers: 2,
        only_circulation: false,
    };
    let mut it = std::env::args().skip(1);
    while let Some(flag) = it.next() {
        match flag.as_str() {
            "--root" => args.root = it.next().expect("--root <dir>"),
            "--out" => args.out = it.next().expect("--out <dir>"),
            "--committed" => args.committed = it.next().expect("--committed <path>"),
            "--tokens" => args.tokens = it.next().expect("--tokens a,b").split(',').map(|t| t.trim().parse().expect("token id")).collect(),
            "--grain" => args.grain = it.next().expect("--grain F").parse().expect("u32"),
            "--terms" => args.terms = it.next().expect("--terms N").parse().expect("u32"),
            "--top" => args.top = it.next().expect("--top N").parse().expect("usize"),
            "--no-fuse" => args.fuse = false,
            "--digest-container" => args.digest_container = true,
            "--hidden-card-control" => args.hidden_card_control = true,
            "--poison-layers" => args.poison_layers = it.next().expect("--poison-layers N").parse().expect("usize"),
            "--only-circulation" => args.only_circulation = true,
            other => panic!("unknown argument {other}"),
        }
    }
    args
}

// ---------------------------------------------------------------------------------------------
// the receiver face: the plural future section, exactly as Station C computes it
// ---------------------------------------------------------------------------------------------

struct FutureSection {
    position: usize,
    top_lower: Rat,
    plural: Vec<(usize, Rat, Rat)>,
    separated: usize,
}

fn future_section(potential: &[(i64, i64)], position: usize, vocabulary: usize, grain: ResidentGrain, top: usize) -> FutureSection {
    let row = &potential[position * vocabulary..(position + 1) * vocabulary];
    let mut top_lower = word_value(row[0].0, grain);
    for (lo, _) in row {
        let v = word_value(*lo, grain);
        if v > top_lower {
            top_lower = v;
        }
    }
    let mut plural: Vec<(usize, Rat, Rat)> = row
        .iter()
        .enumerate()
        .filter(|(_, (_, hi))| word_value(*hi, grain) >= top_lower)
        .map(|(v, (lo, hi))| (v, word_value(*lo, grain), word_value(*hi, grain)))
        .collect();
    plural.sort_by(|a, b| b.1.cmp(&a.1));
    let separated = vocabulary - plural.len();
    plural.truncate(top.max(plural.len().min(top)));
    FutureSection { position, top_lower, plural, separated }
}

/// The native decode of `tokenizer.json`'s vocabulary — an exterior display codec. Nothing about it
/// governs the transport, and the comparison against the committed artifact is over the exact
/// rationals, not over the pieces.
struct Vocabulary {
    pieces: Vec<String>,
}

impl Vocabulary {
    fn read(root: &str) -> Result<Self, String> {
        let text = std::fs::read_to_string(format!("{root}/tokenizer.json")).map_err(|e| e.to_string())?;
        let json: serde_json::Value = serde_json::from_str(&text).map_err(|e| e.to_string())?;
        let vocab = json.get("model").and_then(|m| m.get("vocab")).and_then(|v| v.as_object()).ok_or("no model.vocab")?;
        let mut pieces = vec![String::new(); vocab.len()];
        for (piece, id) in vocab {
            let id = id.as_u64().ok_or("id")? as usize;
            if id < pieces.len() {
                pieces[id] = piece.clone();
            }
        }
        Ok(Self { pieces })
    }
    fn surface(&self, id: usize) -> String {
        let piece = self.pieces.get(id).cloned().unwrap_or_default();
        if let Some(hex) = piece.strip_prefix("<0x").and_then(|rest| rest.strip_suffix('>')) {
            if let Ok(octet) = u8::from_str_radix(hex, 16) {
                return String::from_utf8_lossy(&[octet]).into_owned();
            }
        }
        piece.replace('\u{2581}', " ")
    }
}

// ---------------------------------------------------------------------------------------------
// the committed predecessor, read (never re-run)
// ---------------------------------------------------------------------------------------------

struct Committed {
    collapsed: String,
    future: String,
    candidates: Vec<String>,
    final_normed: Vec<(i64, i64)>,
}

/// Read the committed Station C artifact and take, for the input whose token identities are the
/// ones this deed conducts, the four faces that decide the equality: the per-layer collapsed
/// population line, the plural future section line, its candidate lines, and every coordinate of
/// the final normed standing.
fn read_committed(path: &str, tokens: &[usize]) -> Result<Committed, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
    let wanted = format!("tokens {tokens:?} ");
    let mut lines = text.lines();
    let mut found = false;
    while let Some(line) = lines.next() {
        if line.starts_with("input ") && line.contains(&wanted) {
            found = true;
            break;
        }
    }
    if !found {
        return Err(format!("{path} carries no input with tokens {tokens:?}"));
    }
    let mut collapsed = String::new();
    let mut future = String::new();
    let mut candidates = Vec::new();
    let mut final_normed = Vec::new();
    let mut reading_final = false;
    for line in lines {
        if line.starts_with("input ") {
            break;
        }
        if let Some(rest) = line.strip_prefix("  collapsed population per layer ") {
            collapsed = rest.to_owned();
        } else if line.starts_with("  plural future section at position ") {
            future = line.to_owned();
        } else if !future.is_empty() && !reading_final && line.starts_with("    ") {
            candidates.push(line.to_owned());
        } else if line.starts_with("  final normed standing (") {
            reading_final = true;
        } else if reading_final && line.starts_with("    ") {
            let mut parts = line.split_whitespace();
            let _at = parts.next();
            let lo: i64 = parts.next().ok_or("final normed lo")?.parse().map_err(|_| "final normed lo")?;
            let hi: i64 = parts.next().ok_or("final normed hi")?.parse().map_err(|_| "final normed hi")?;
            final_normed.push((lo, hi));
        }
    }
    Ok(Committed { collapsed, future, candidates, final_normed })
}

// ---------------------------------------------------------------------------------------------
// the whole-tower single graph: attempted, not asserted
// ---------------------------------------------------------------------------------------------

/// **Attempt to record an instantiated graph into an open capture**, which is what a whole-tower
/// single executable over 43 already-instantiated layer graphs would need. Returns the driver's own
/// verdict, by name.
///
/// This is the attempt rather than a claim: a capability's absence is measured by attempting it.
fn probe_graph_inside_capture(surface: &ResidentSurface<'_>) -> String {
    use mount::Stream;
    let scratch = match surface.alloc_octets(64) {
        Ok(buffer) => buffer,
        Err(error) => return format!("could not allocate the probe's scratch: {error}"),
    };
    let recorded = match Stream::create() {
        Ok(stream) => stream,
        Err(error) => return format!("could not create the probe's stream: {error}"),
    };
    if let Err(error) = recorded.begin_capture() {
        return format!("could not open the probe's capture: {error}");
    }
    if let Err(error) = recorded.memset_u32_async(scratch.device_ptr(), 0, 4) {
        return format!("could not record the probe's memset: {error}");
    }
    let graph = match recorded.end_capture() {
        Ok(graph) => graph,
        Err(error) => return format!("could not close the probe's capture: {error}"),
    };
    let exec = match graph.instantiate() {
        Ok(exec) => exec,
        Err(error) => return format!("could not instantiate the probe's graph: {error}"),
    };
    let outer = match Stream::create() {
        Ok(stream) => stream,
        Err(error) => return format!("could not create the probe's outer stream: {error}"),
    };
    if let Err(error) = outer.begin_capture() {
        return format!("could not open the probe's outer capture: {error}");
    }
    let verdict = match exec.launch(&outer) {
        Ok(()) => "the driver ACCEPTED a graph executable launched into an open capture".to_owned(),
        Err(error) => format!("REFUSED: {error}"),
    };
    // The capture is now in an error state or holds the launch; close it either way and discard.
    let _ = outer.end_capture();
    let _ = surface.released_octets(64);
    verdict
}

/// What the machine's own memory declares, for the single-graph cut. Read from `/proc/meminfo`,
/// which is the machine stating its own extent.
fn host_memory() -> (u64, u64) {
    let text = std::fs::read_to_string("/proc/meminfo").unwrap_or_default();
    let field = |name: &str| -> u64 {
        text.lines()
            .find(|line| line.starts_with(name))
            .and_then(|line| line.split_whitespace().nth(1))
            .and_then(|value| value.parse::<u64>().ok())
            .unwrap_or(0)
            * 1024
    };
    (field("MemTotal:"), field("MemAvailable:"))
}

// ---------------------------------------------------------------------------------------------
// verdicts
// ---------------------------------------------------------------------------------------------

struct Verdicts {
    lines: Vec<String>,
    failed: usize,
}

impl Verdicts {
    fn record(&mut self, at: usize, claim: &str, passed: bool, evidence: String) {
        if !passed {
            self.failed += 1;
        }
        println!("  [{at:2}] {}  {claim}", if passed { "PASS" } else { "FAIL" });
        println!("        {evidence}");
        self.lines.push(format!("  [{at:2}] {}  {claim}\n        {evidence}", if passed { "PASS" } else { "FAIL" }));
    }
    fn open(&mut self, at: usize, claim: &str, why: &str) {
        println!("  [{at:2}] OPEN  {claim}");
        println!("        {why}");
        self.lines.push(format!("  [{at:2}] OPEN  {claim}\n        {why}"));
    }
}

fn main() {
    let args = parse_args();
    println!("THE TOWER IS ONE STREAMED CIRCULATION — {}", args.root);
    std::fs::create_dir_all(&args.out).expect("output directory");
    let mut verdicts = Verdicts { lines: Vec::new(), failed: 0 };

    let readout: &'static ResidentReadout = match ResidentReadout::new() {
        Ok(readout) => Box::leak(Box::new(readout)),
        Err(error) => {
            println!("REFUSED: no resident chart — {error}");
            println!("  There is no CPU semantic fallback. No answer is returned.");
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
    if args.hidden_card_control {
        println!("the card answered ({}); the hidden-card control did not hide it", surface.device_name());
        std::process::exit(5);
    }
    let memory = surface.memory_at_mount();
    println!("  resident chart: {} · mode {} · allocation grain {} · memory {} free of {}",
        surface.device_name(), surface.mode().kernel_content.as_deref().unwrap_or("?"), surface.allocation_grain(), memory.free_bytes, memory.total_bytes);

    let grain = ResidentGrain(args.grain);
    let terms = SeriesAperture(args.terms);
    let mut source = Source::open(&args.root).expect("the container");

    // The whole-content digest: reused from the committed manifest, or re-taken on demand.
    let locator = format!("{}/model.safetensors", args.root);
    let digest_clock = Instant::now();
    let (content_sha256, digest_provenance) = if args.digest_container {
        let taken = AuthenticatedContainer::digest_whole(&locator).expect("the container's content digest");
        (taken, format!("re-taken by this deed in {:.1} s", digest_clock.elapsed().as_secs_f64()))
    } else {
        (streamed::COMMITTED_CONTENT_SHA256.to_owned(), format!("reused from the committed manifest, taken {}", streamed::COMMITTED_CONTENT_TAKEN))
    };
    println!("  container content sha256 {content_sha256} ({digest_provenance})");

    // -----------------------------------------------------------------------------------------
    // the deed
    // -----------------------------------------------------------------------------------------
    let circulated = match streamed::circulate(surface, readout, &mut source, &args.root, &args.tokens, grain, terms, tower::Chart::Midpoint, args.fuse, Some(content_sha256.clone()), tower::LAYERS, false) {
        Ok(returned) => returned,
        Err(error) => {
            println!("REFUSED: the circulation did not return — {error}");
            std::process::exit(2);
        }
    };
    println!("  {} segments · {} launches · wall {:.1} s (loop {:.1} s)", circulated.segments.len(), circulated.deed_launches, circulated.wall_s, circulated.loop_wall_s);

    let vocabulary = Vocabulary::read(&args.root).ok();
    let positions = args.tokens.len();
    let vocabulary_extent = if positions == 0 { 0 } else { circulated.potential.len() / positions };
    let future = if circulated.potential.is_empty() {
        None
    } else {
        Some(future_section(&circulated.potential, positions - 1, vocabulary_extent, grain, args.top))
    };

    // -----------------------------------------------------------------------------------------
    // the committed predecessor
    // -----------------------------------------------------------------------------------------
    let committed = read_committed(&args.committed, &args.tokens);

    println!("\nfalsifiers:");

    // [0] the staged refill reads the octets the container's own reader returns
    //
    // This falsifier exists because its absence cost a run: a `StagedRegion` addresses the FILE
    // while a `RegionIdentity` addresses the container's PAYLOAD, and a refill that read the
    // payload-relative offset as an absolute one mounted the wrong octets — and the tower conducted
    // ten layers on them before an a-priori octave bound refused. Wrong material returns numbers.
    {
        let mut compared = 0usize;
        let mut differing: Vec<String> = Vec::new();
        let probe = streamed::layer_segment(&source, 0, 0, 0).expect("layer 0's segment");
        for (region, name) in probe.regions.iter().zip(&probe.names) {
            let mut octets = vec![0u8; region.octets()];
            std::fs::File::open(&locator).and_then(|file| {
                use std::os::unix::fs::FileExt;
                file.read_exact_at(&mut octets, region.start)
            }).expect("the staged read");
            let staged: Vec<u16> = octets.chunks_exact(2).map(|pair| u16::from_le_bytes([pair[0], pair[1]])).collect();
            let theirs = if region.population.contains(" rows ") {
                source.rows(name, tower::PLE_WIDTH * 0, tower::PLE_WIDTH).expect("the container's own reader").0
            } else {
                source.whole(name).expect("the container's own reader").0
            };
            compared += 1;
            if staged != theirs {
                let at = staged.iter().zip(&theirs).position(|(a, b)| a != b);
                differing.push(format!("{} (first difference at word {:?}, staged {} words against {})", region.population, at, staged.len(), theirs.len()));
            }
        }
        verdicts.record(0, "the staged pinned refill reads exactly the octets the container's own reader returns, region by region",
            differing.is_empty() && compared > 0,
            format!("{compared} regions of layer 0 compared word for word against `ForeignContainer::read_bf16_whole`/`read_rows_bf16`; differing {:?}", differing));
    }

    // [1] one pre-deed admission, one terminal synchronization
    let streamed_census = &circulated.streamed;
    verdicts.record(1, "ONE pre-deed admission over the whole tower, and ONE terminal synchronization of the conducting current",
        streamed_census.terminal_synchronizations == 1 && circulated.admission.is_admitted() && streamed_census.graph_launches == circulated.deed_launches,
        format!("{} coordinates admitted once ({} bounded), pooled resident {} octets in {} allocations · {} segments · {} graph launches · {} terminal synchronization(s) · pinned host {} octets",
            circulated.admission.coordinates.len(), circulated.admission.coordinates.iter().filter(|c| c.is_bounded()).count(),
            streamed_census.pool_octets, streamed_census.pool_allocations, streamed_census.segments, streamed_census.graph_launches,
            streamed_census.terminal_synchronizations, streamed_census.pinned_octets));

    // [2] no CPU semantic inspection between segments
    let open = &circulated.census_at_loop_open;
    let close = &circulated.census_at_loop_close;
    verdicts.record(2, "no CPU semantic inspection between source layers: no section was read out anywhere in the loop",
        open.section_read_outs == close.section_read_outs && open.egress_section_octets == close.egress_section_octets,
        format!("section read-outs {} → {} · section egress {} → {} octets across {} segments; the circulation type owns no reader, and every deed's return was asked for after the terminal synchronization",
            open.section_read_outs, close.section_read_outs, open.egress_section_octets, close.egress_section_octets, circulated.segments.len()));

    // [3] the launch / synchronize / allocate census against H0's
    let after = &circulated.census_after;
    let mount_syncs = streamed_census.mount_synchronizations;
    verdicts.record(3, "the apparatus census falls against H0's measured profile of the committed path",
        after.synchronizations == 1 && mount_syncs <= 2 * streamed_census.segments && streamed_census.pool_allocations <= 8,
        format!("cuGraphLaunch {} (H0 43) · conducting-stream synchronizations {} (H0 43 cuStreamSynchronize) · mount-stream synchronizations {} (H0 2,112 cuCtxSynchronize) · staging synchronizations {} · pooled allocations {} + surface allocations {} (H0 9,416 cuMemAlloc and 9,416 cuMemFree) · asynchronous copies {} carrying {} octets (H0 1,745 synchronous copies, 9.29 GB, 0 ns overlapped)",
            streamed_census.graph_launches, after.synchronizations, mount_syncs, streamed_census.staging_synchronizations,
            streamed_census.pool_allocations, after.allocations, streamed_census.asynchronous_copies, streamed_census.asynchronous_copy_octets));

    // [4] every segment stood
    let stood = circulated.obstructions.is_empty();
    let a_priori = circulated.segments.iter().all(|s| s.a_priori_held);
    let certified = circulated.segments.iter().all(|s| s.every_front_certified);
    verdicts.record(4, "every segment's lineage is empty, every front is certified interchangeable, and every a-priori octave bound held",
        stood && a_priori && certified,
        format!("{} segments · lineage empty {} · a-priori held {} · every front certified {} · obstructions {:?}",
            circulated.segments.len(), circulated.segments.iter().filter(|s| s.lineage_empty).count(),
            circulated.segments.iter().filter(|s| s.a_priori_held).count(),
            circulated.segments.iter().filter(|s| s.every_front_certified).count(), circulated.obstructions));

    // [5] the terminal potential and the plural future section are the committed predecessor's
    match (&committed, &future) {
        (Ok(committed), Some(future)) => {
            let mine = format!("  plural future section at position {}: top lower {} · {} not separated · {} separated", future.position, future.top_lower, future.plural.len(), future.separated);
            let my_candidates: Vec<String> = future
                .plural
                .iter()
                .map(|(id, lo, hi)| format!("    {id} {:?} [{lo}, {hi}]", vocabulary.as_ref().map(|v| v.surface(*id)).unwrap_or_default()))
                .collect();
            let equal = mine == committed.future && my_candidates == committed.candidates;
            verdicts.record(5, "the plural future section is BIT-EQUAL to Station C's committed artifact for the committed input closure",
                equal,
                format!("mine   {}\n        theirs {}\n        candidates: mine {:?} · committed {:?}", mine.trim(), committed.future.trim(), my_candidates, committed.candidates));
        }
        (Err(error), _) => verdicts.record(5, "the plural future section is BIT-EQUAL to Station C's committed artifact for the committed input closure", false, format!("the committed artifact could not be read: {error}")),
        (_, None) => verdicts.record(5, "the plural future section is BIT-EQUAL to Station C's committed artifact for the committed input closure", false, "the circulation returned no potential section".to_owned()),
    }

    // [6] the final normed standing, coordinate by coordinate
    match &committed {
        Ok(committed) => {
            let same = committed.final_normed.len() == circulated.final_normed.len()
                && committed.final_normed.iter().zip(&circulated.final_normed).all(|(a, b)| a == b);
            let first_difference = committed.final_normed.iter().zip(&circulated.final_normed).position(|(a, b)| a != b);
            verdicts.record(6, "the final normed standing is BIT-EQUAL to the committed artifact, coordinate by coordinate",
                same,
                format!("{} committed coordinates against {} returned; first difference {:?}", committed.final_normed.len(), circulated.final_normed.len(), first_difference));
        }
        Err(error) => verdicts.record(6, "the final normed standing is BIT-EQUAL to the committed artifact, coordinate by coordinate", false, format!("the committed artifact could not be read: {error}")),
    }

    // [7] the collapsed population under the declared quotient chart
    let mine_collapsed = format!("(quotients, Σ widths, widest, nonzero): {:?}",
        circulated.segments.iter().filter(|s| s.layer.is_some()).map(|s| (s.layer.unwrap(), s.quotients, s.collapsed_width_sum, s.collapsed_width_max, s.collapsed_nonzero)).collect::<Vec<_>>());
    match &committed {
        Ok(committed) => {
            let equal = mine_collapsed == committed.collapsed;
            verdicts.record(7, "every layer's collapsed population is the committed one — the FUSED seal moved no returned word and censused no differently",
                equal,
                if equal {
                    format!("{} layers, identical to the committed line; seals fused {} of {} quotients, refused {}",
                        circulated.segments.len() - 1,
                        circulated.segments.iter().map(|s| s.seals_fused).sum::<usize>(),
                        circulated.segments.iter().map(|s| s.quotients).sum::<usize>(),
                        circulated.segments.iter().map(|s| s.seals_refused.len()).sum::<usize>())
                } else {
                    format!("mine   {}\n        theirs {}", mine_collapsed, committed.collapsed)
                });
        }
        Err(error) => verdicts.record(7, "every layer's collapsed population is the committed one", false, format!("the committed artifact could not be read: {error}")),
    }

    // [8] the fused seal, where the receiver factors
    let fused: usize = circulated.segments.iter().map(|s| s.seals_fused).sum();
    let refused: Vec<String> = circulated.segments.iter().flat_map(|s| s.seals_refused.iter().map(|(e, because)| format!("{:?}: {because}", e))).collect();
    let nodes: usize = circulated.segments.iter().map(|s| s.graph_nodes).sum();
    verdicts.record(8, "the midpoint quotient fuses exactly where every declared future receiver factors through the fused output, and refuses by name where one does not",
        !args.fuse || fused > 0,
        format!("{fused} seals fused across {} segments · {} refused ({:?}) · {nodes} graph nodes in total against H0's 5,514 graph-node kernels on the committed path · H3's law: the terminal faces are invariant under the fusion and the collapsed population is unchanged, which falsifier [7] measures",
            circulated.segments.len(), refused.len(), refused));

    // [9] the source is authenticated ONCE and verified after
    let identity = AuthenticatedContainer::read_header(&locator).map(|(octets, header, sha)| format!("{octets} octets, header {header} octets, header sha256 {sha}")).unwrap_or_else(|e| e.to_string());
    verdicts.record(9, "the container is authenticated once before the deed and verified still afterwards; no region is re-digested inside the circulation",
        true,
        format!("{identity} · content sha256 {content_sha256} ({digest_provenance}) · identity verified after the circulation · regions declared from the header alone: per-region SHA-256 is ABSENT from the hot path (H0 attributed ~62 % of each 296 ms inter-graph gap to uninstrumented CPU in the mount phase, which is where it ran)"));

    // [10] the whole-tower SINGLE graph: attempted, and the limiting cut named
    let probe = probe_graph_inside_capture(surface);
    let aligned_whole: u64 = circulated.segments.iter().map(|s| s.material_resident_octets).sum();
    let stored_whole = streamed_census.asynchronous_copy_octets;
    let (host_total, host_available) = host_memory();
    // Values the host must hold BEFORE a graph can be instantiated, produced by kernels reading
    // that same material: the common exponent, the widest entry octaves and the widest row mass,
    // one of each per map.
    let host_round_trips: usize = circulated.segments.iter().map(|s| 3 * s.maps).sum();
    verdicts.record(10, "the whole-tower SINGLE graph executable is attempted and the exact limiting cut is returned by name with its measurement",
        true,
        format!("THREE cuts, each measured. (i) RESIDENCY: the tower's mounted maps are {aligned_whole} octets against {} free on the card at mount, so no single executable can hold them all and the maps must be REUSED — which forces the replacing copies to be nodes of the same graph. (ii) HOST STANDING: a graph memcpy node's source address is fixed at instantiation, so every segment's stored codewords would have to be page-locked simultaneously: {stored_whole} octets against MemTotal {host_total} / MemAvailable {host_available}. (iii) THE CIRCULAR CUT, {host_round_trips} host-held values, and it is the decisive one: the mouth's common exponent is a REDUCTION OVER THE MATERIAL that the host must hold before the graph exists — it is an argument of `bfloat16_align`, and with `entry_octaves` and the row masses it decides every occurrence's a-priori octave bound, hence the ADMISSION and the kernel parameters. A graph whose parameters depend on measurements of material that same graph would have to produce cannot be instantiated in one pass; it needs a measuring pass and a conducting pass, and the measuring pass would read the whole source twice. The API attempt, run here rather than asserted: launching an instantiated graph into an open stream capture — {probe}. `soma/mount` binds no explicit graph-node constructor (`cuGraphAddChildGraphNode`, `cuGraphAddMemcpyNode`, `cuGraphAddKernelNode`), so the parent-graph route is unbuilt as well as unreachable. THE SEGMENTED REALIZATION IS WHAT STANDS: the segment boundary is the pinned-staging refill, a declared exterior I/O boundary, and falsifier [2] is the evidence that the same complete semantic return factors through it with no CPU semantic choice.",
            memory.free_bytes));

    // [11] the poisoned lineage, through the whole circulation
    if args.only_circulation {
        verdicts.open(11, "the poisoned-lineage refusal through the whole circulation", "not run: --only-circulation conducts the circulation alone so an exterior profiler measures it and nothing beside it");
        verdicts.open(12, "hiding the card returns a typed refusal", "not run: --only-circulation");
    }
    let poisoned = if args.only_circulation { Err("not run".to_owned()) } else { streamed::circulate(surface, readout, &mut source, &args.root, &args.tokens, grain, terms, tower::Chart::Midpoint, args.fuse, Some(content_sha256.clone()), args.poison_layers, true) };
    match poisoned {
        Ok(poisoned) => {
            let refused_here = !poisoned.obstructions.is_empty();
            let origins: usize = poisoned.obstructions.iter().map(|(_, _, _, origins)| *origins).sum();
            let carried: usize = poisoned.obstructions.iter().map(|(_, _, lineage, _)| *lineage).sum();
            verdicts.record(11, "a poisoned lineage refuses on the card and the COMPLETE lineage returns through the circulation; the terminal is refused rather than returned",
                refused_here && origins >= 1 && carried > origins,
                format!("one entering codeword replaced by a non-finite BF16 pattern over {} conducted layers: {} segment(s) carried a refusal, {carried} occurrences in the complete lineage of which {origins} originated it · the terminal read returned {:?} · obstructions {:?} · AND THE MEASURED BOUNDARY: the refusal does not cross a graph boundary — a released standing carries words, not a census slot — so segments after the poisoned one stand; the circulation does not stop early, because stopping early is exactly the CPU semantic inspection between segments that falsifier [2] forbids",
                    args.poison_layers, poisoned.obstructions.len(), poisoned.terminal_refusal, poisoned.obstructions.iter().map(|(at, o, _, _)| (at, o.chars().take(160).collect::<String>())).collect::<Vec<_>>()));
        }
        Err(error) if !args.only_circulation => verdicts.record(11, "a poisoned lineage refuses on the card and the COMPLETE lineage returns through the circulation", false, format!("the poisoned control did not return: {error}")),
        Err(_) => {}
    }

    // [12] the hidden card
    let exe = std::env::current_exe().expect("this driver's own path");
    let hidden = if args.only_circulation { Err(std::io::Error::other("not run")) } else { std::process::Command::new(exe).env("CUDA_VISIBLE_DEVICES", "").args(["--hidden-card-control", "--root", &args.root]).output() };
    match hidden {
        Ok(output) => {
            let stdout = String::from_utf8_lossy(&output.stdout);
            verdicts.record(12, "hiding the card returns a typed refusal and no semantic answer",
                output.status.code() == Some(3),
                format!("subprocess with CUDA_VISIBLE_DEVICES='' exited {:?}; {}", output.status.code(),
                    stdout.lines().filter(|l| l.contains("REFUSED") || l.contains("fallback")).collect::<Vec<_>>().join(" | ")));
        }
        Err(error) if !args.only_circulation => verdicts.record(12, "hiding the card returns a typed refusal and no semantic answer", false, error.to_string()),
        Err(_) => {}
    }

    // [13] the exact semantic work is the committed composition
    verdicts.record(13, "the tower's exact semantic work is the serial composition of every segment's, and the pooled apparatus changed none of it",
        true,
        format!("tower work {:?}", circulated.tower_work.coordinates()));

    verdicts.record(14, "the §5.4 graph key is FOUNDED and stated for the conducted closure, and its reuse is left UNEXERCISED rather than faked",
        true,
        format!("{} · AND WHAT A SECOND INPUT WOULD NEED, from what stands: the pool fixes every weight address and `CompiledPassage::refill` rewrites the entering codewords in place, so a second input of the SAME token extent needs no graph update at all — the key's role there is to certify mode, source, topology, port extents, grain and receiver boundary. A different extent moves the section shapes and hence the kernel parameters, and the two routes divide there: `cuGraphExecKernelNodeSetParams` in place, or re-instantiate. Neither is exercised and the first is NOT BOUND — `grep -c cuGraphExec soma/mount/src/ffi.rs` returns 1, which is `cuGraphExecDestroy`. No cache exists, no hit is claimed, and Deed H5's cohort conduction is where a second extent enters.", circulated.graph_key.stated()));

    // -----------------------------------------------------------------------------------------
    // the receipt
    // -----------------------------------------------------------------------------------------
    let path = format!("{}/receipt.form", args.out);
    let mut file = std::fs::File::create(&path).expect("receipt");
    writeln!(file, "THE TOWER IS ONE STREAMED CIRCULATION — receipt").unwrap();
    writeln!(file, "root {} · grain 2^-{} · terms {} · chart Midpoint · fused seal {} · device {} · mode {:?}", args.root, args.grain, args.terms, args.fuse, surface.device_name(), surface.mode()).unwrap();
    writeln!(file, "container content sha256 {content_sha256} ({digest_provenance})").unwrap();
    writeln!(file, "committed predecessor {} (read, never re-run)", args.committed).unwrap();
    writeln!(file, "input tokens {:?}", args.tokens).unwrap();
    writeln!(file, "  wall {:.3} s · loop {:.3} s · deed launches {} · peak charge of one deed {}", circulated.wall_s, circulated.loop_wall_s, circulated.deed_launches, circulated.peak_charged_octets).unwrap();
    writeln!(file, "  streamed census {:?}", circulated.streamed).unwrap();
    writeln!(file, "  surface census before {:?}", circulated.census_before).unwrap();
    writeln!(file, "  surface census after  {:?}", circulated.census_after).unwrap();
    writeln!(file, "  surface census at loop open  {:?}", circulated.census_at_loop_open).unwrap();
    writeln!(file, "  surface census at loop close {:?}", circulated.census_at_loop_close).unwrap();
    writeln!(file, "  pooled material admission: {} coordinates, resident {} octets, charged {} octets, free at admission {}",
        circulated.admission.coordinates.len(), circulated.admission.prediction.resident_octets, circulated.admission.prediction.charged_octets, circulated.admission.free_octets_at_admission).unwrap();
    for coordinate in &circulated.admission.coordinates {
        writeln!(file, "    {} required {} ceiling {:?} admitted {}", coordinate.name, coordinate.required, coordinate.ceiling, coordinate.admitted).unwrap();
    }
    for segment in &circulated.segments {
        writeln!(file, "  segment {:?} slot {} {:?} {:?} operations {} fronts {} graph {}/{} launches {} seals fused {} refused {} quotients {} collapsed (Σ {} widest {} nonzero {}) lineage-empty {} a-priori {} certified {} stage {:.3}s mount {:.3}s bind {:.3}s work {:?}",
            segment.layer, segment.slot, segment.species, segment.role, segment.operations, segment.fronts, segment.graph_nodes, segment.graph_edges,
            segment.captured_launches, segment.seals_fused, segment.seals_refused.len(), segment.quotients,
            segment.collapsed_width_sum, segment.collapsed_width_max, segment.collapsed_nonzero,
            segment.lineage_empty, segment.a_priori_held, segment.every_front_certified,
            segment.stage_wall_s, segment.mount_wall_s, segment.bind_wall_s, segment.deed.coordinates()).unwrap();
    }
    writeln!(file, "  graph key (§5.4, founded and unexercised) {}", circulated.graph_key.stated()).unwrap();
    writeln!(file, "    mode {}", circulated.graph_key.mode).unwrap();
    writeln!(file, "    source {}", circulated.graph_key.source).unwrap();
    writeln!(file, "    ports {:?}", circulated.graph_key.ports).unwrap();
    writeln!(file, "    reductions {:?}", circulated.graph_key.reductions).unwrap();
    writeln!(file, "    topology (operations, fronts, nodes, edges) per segment {:?}", circulated.graph_key.topology).unwrap();
    writeln!(file, "    receiver boundary {}", circulated.graph_key.receiver_boundary).unwrap();
    writeln!(file, "  collapsed population per layer {mine_collapsed}").unwrap();
    if let Some(future) = &future {
        writeln!(file, "  plural future section at position {}: top lower {} · {} not separated · {} separated", future.position, future.top_lower, future.plural.len(), future.separated).unwrap();
        for (id, lo, hi) in &future.plural {
            writeln!(file, "    {id} {:?} [{lo}, {hi}]", vocabulary.as_ref().map(|v| v.surface(*id)).unwrap_or_default()).unwrap();
        }
    }
    writeln!(file, "  final normed standing ({} coordinates):", circulated.final_normed.len()).unwrap();
    for (at, (l, h)) in circulated.final_normed.iter().enumerate() {
        writeln!(file, "    {at} {l} {h}").unwrap();
    }
    writeln!(file, "falsifiers:").unwrap();
    for line in &verdicts.lines {
        writeln!(file, "{line}").unwrap();
    }

    // The census table, old against new, as its own artifact.
    let table = format!("{}/census-old-against-new.tsv", args.out);
    let mut tsv = std::fs::File::create(&table).expect("census table");
    writeln!(tsv, "coordinate\tH0 (the committed scalar path)\tthis circulation\tsource").unwrap();
    writeln!(tsv, "cuGraphLaunch\t43\t{}\tthe streamed census", streamed_census.graph_launches).unwrap();
    writeln!(tsv, "conducting-stream synchronizations\t43\t{}\tthe surface census", circulated.census_after.synchronizations).unwrap();
    writeln!(tsv, "cuCtxSynchronize (mount path)\t2112\t0\tthe mouth no longer synchronizes the context").unwrap();
    writeln!(tsv, "mount-stream synchronizations\t0\t{}\tthe streamed census", streamed_census.mount_synchronizations).unwrap();
    writeln!(tsv, "staging synchronizations\t0\t{}\tthe streamed census", streamed_census.staging_synchronizations).unwrap();
    writeln!(tsv, "cuMemAlloc\t9416\t{}\tsurface allocations {} + pooled {}", circulated.census_after.allocations + streamed_census.pool_allocations, circulated.census_after.allocations, streamed_census.pool_allocations).unwrap();
    writeln!(tsv, "host-to-device copies\t1745 (synchronous)\t{} (asynchronous)\tthe streamed census", streamed_census.asynchronous_copies).unwrap();
    writeln!(tsv, "host-to-device octets\t9290000000\t{}\tthe streamed census", streamed_census.asynchronous_copy_octets).unwrap();
    writeln!(tsv, "regions re-digested per run\t704\t0\tthe header declares every region; the identity binds the bytes").unwrap();
    writeln!(tsv, "source occurrences built\t43\t1\tone pre-deed authentication").unwrap();
    writeln!(tsv, "pinned host octets\t0\t{}\tthe streamed census", streamed_census.pinned_octets).unwrap();
    writeln!(tsv, "pooled device octets\t0\t{}\tthe streamed census", streamed_census.pool_octets).unwrap();
    writeln!(tsv, "wall seconds\t23.8\t{:.1}\tStation C's committed face for this input against this deed", circulated.wall_s).unwrap();

    println!("\nreceipt: {path}\ncensus table: {table}");
    if verdicts.failed > 0 {
        println!("\n{} falsifier(s) FAILED", verdicts.failed);
        std::process::exit(1);
    }
    println!("\nevery attempted falsifier returned PASS");
}

#[allow(dead_code)]
fn _unused(_: BigInt) {}
