//! **The whole text tower as ONE streamed resident circulation** — the site that replaces the
//! per-layer apparatus foreman of `phoenix/conduct.rs` for Deed H4.
//!
//! The diagram is unchanged: every layer is founded by `phoenix/tower.rs`, from the same source
//! testimony, at the same grain, under the same declared quotient chart. What changes is
//! everything around it, and every change is one of H0's measured findings:
//!
//! ```text
//!   H0 measured                          this site
//!   ----------------------------------   --------------------------------------------------
//!   a SourceOccurrence rebuilt per       ONE, built before the deed: the implementation text
//!   layer (implementation re-read and    hashed once, the configuration once, the container's
//!   re-hashed 43 times)                  header once, every region declared from that header
//!
//!   per-region SHA-256 of every octet    NONE in the circulation. The container's identity
//!   read, every layer, every run         (device/inode/size/mtime/ctime) is taken before and
//!   (~184 ms of the 296 ms gap)          verified after; the whole-content digest is REUSED
//!                                        from the committed manifest with its date stated
//!
//!   9,416 cuMemAlloc + 9,416 cuMemFree   three pooled slots, three allocations, reused
//!
//!   2,112 cuCtxSynchronize (one per      two synchronizations of a MOUNT stream per segment,
//!   mount kernel), each draining the     which is the mouth's own host round trip and nothing
//!   whole context                        else; the conducting stream never waits
//!
//!   1,745 synchronous copies, 0 ns of    one asynchronous copy per region on a copy stream,
//!   them concurrent with any kernel      ordered against the deed that last read the slot by a
//!                                        device event, so a refill crosses while a deed conducts
//!
//!   43 launches, 43 synchronizations     43 launches, ONE terminal synchronization
//! ```
//!
//! **No CPU semantic inspection between source layers**, and it is structural rather than
//! promised: the loop below holds a [`StreamedCirculation`], which has no accessor returning a
//! section, a census slot or a terminal; every deed's return is asked for **after** the terminal
//! synchronization, from a population the loop only ever pushed onto. The driver asserts the
//! surface's own `section_read_outs` and `egress_section_octets` did not move across the loop.
//!
//! This is a site, not a library owner: it binds one source instance and declares no operation.

#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::os::unix::fs::FileExt;
use std::rc::Rc;
use std::time::Instant;

use holonic_engine::causal::EventId;
use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::exact_work::ExactWork;
use holonic_engine::front_passage::{
    factored_seals, DeedReceiver, EnteringRows, FrontPassage, FrontPassageObstruction, MaterialAdmission, MountedPopulation, ResidentMaterial,
    SealedMidpointQuotient,
};
use holonic_engine::resident_section::{Dyadic, ResidentGrain, ResidentSection, ResidentSurface, SeriesAperture, TransferCensus};
use holonic_engine::source_occurrence::{RegionIdentity, SourceOccurrence};
use holonic_engine::streamed_standing::{GraphKey, SlotShape, StagedRegion, StreamedCensus, StreamedCirculation};

use super::resident_layer::Source;
use super::tower::{self, Entry, Intervention, KvRole, Species};

/// The two pool slots the source layers alternate between, and the third the final deed uses.
pub const SLOTS: usize = 3;
pub const FINAL_SLOT: usize = 2;
/// The final boundary's own pinned slot, after the three the source layers alternate between.
pub const FINAL_PINNED: usize = 3;

/// **The whole-content digest of the committed container, reused rather than re-taken.**
///
/// Taken by Station B and carried by Station C's committed receipt
/// (`output/the_tower_conducts/tower-5-inputs-grain-48-terms-14.form`, line 4) on **2026-08-19**
/// over `/home/b/models/gemma-4-E4B-it/model.safetensors`. Digesting 15,992,595,884 octets is
/// ~16 s of exterior apparatus that measures nothing this deed does not already bind: the file
/// identity is taken before the circulation and verified after it, and every region is declared by
/// the header, whose own digest is taken here. The reuse is stated on the receipt; a caller that
/// wants it re-taken passes `--digest-container`.
pub const COMMITTED_CONTENT_SHA256: &str = "cfbd3d2f1cd71bd471c37fe2bf8546d5028d41e5736f64e1ca6c6b8893125503";
pub const COMMITTED_CONTENT_TAKEN: &str = "2026-08-19, Station B/C";

/// One segment's declaration: the regions it stages, the material names they mount as, and the
/// pool slot they land in. A segment boundary is the **pinned-staging refill**, which is the one
/// exterior I/O boundary in the circulation.
pub struct Segment {
    pub layer: Option<usize>,
    pub slot: usize,
    pub pinned: usize,
    pub regions: Vec<StagedRegion>,
    /// The material name each staged region mounts under, in the same order.
    pub names: Vec<String>,
    /// The region carrying the layer scalar, read as a host word and mounted nowhere.
    pub scalar: Option<StagedRegion>,
}

/// The header identity of one population, without a content digest.
fn region_of(source: &Source, population: &str) -> Result<RegionIdentity, String> {
    let tensor = source.container.tensor(population).map_err(|e| e.to_string())?;
    Ok(RegionIdentity {
        population: population.to_owned(),
        dtype: format!("{:?}", tensor.dtype),
        shape: tensor.shape.clone(),
        start: tensor.start,
        end: tensor.end,
        sha256: None,
    })
}

/// A staged region addresses the FILE, so it carries the payload base; a `RegionIdentity`
/// addresses the container's payload, so it does not. Conflating the two reads the wrong octets and
/// the deed still returns numbers — measured 2026-08-19, when it did: the tower conducted ten
/// layers on the wrong weights before an a-priori octave bound refused at layer 10.
fn staged_of(source: &Source, population: &str) -> Result<StagedRegion, String> {
    let tensor = source.container.tensor(population).map_err(|e| e.to_string())?;
    let words = (tensor.end - tensor.start) / 2;
    let dim = *tensor.shape.last().unwrap_or(&0);
    if tensor.dtype != holonic_engine::foreign_map::ForeignDtype::Bf16 {
        return Err(format!("{population} is {:?}; the mouth this circulation stages through admits BF16", tensor.dtype));
    }
    Ok(StagedRegion {
        population: population.to_owned(),
        start: source.container.payload_base() + tensor.start,
        words: u32::try_from(words).map_err(|_| format!("{population} is wider than one staged region"))?,
        dim,
    })
}

/// **Every region the whole tower reads, declared from the container's header alone.** Nothing is
/// opened, nothing is digested, and this is what the one pre-deed source occurrence carries.
pub fn header_regions(source: &Source) -> Result<BTreeMap<String, RegionIdentity>, String> {
    let mut regions = BTreeMap::new();
    for layer in 0..tower::LAYERS {
        for name in tower::populations(layer) {
            regions.insert(name.clone(), region_of(source, &name)?);
        }
        let scalar = tower::named(layer, "layer_scalar");
        regions.insert(scalar.clone(), region_of(source, &scalar)?);
        // The layer's own slice of the per-layer model projection: the octet span read, named.
        let whole = source.container.tensor(tower::PLE_MODEL_PROJECTION).map_err(|e| e.to_string())?;
        let dim = whole.shape[1];
        let mut slice = region_of(source, tower::PLE_MODEL_PROJECTION)?;
        slice.population = format!("{} rows {}..{}", tower::PLE_MODEL_PROJECTION, tower::PLE_WIDTH * layer, tower::PLE_WIDTH * (layer + 1));
        slice.shape = vec![tower::PLE_WIDTH, dim];
        slice.start += (tower::PLE_WIDTH * layer * dim * 2) as u64;
        slice.end = slice.start + (tower::PLE_WIDTH * dim * 2) as u64;
        regions.insert(slice.population.clone(), slice);
    }
    for name in [tower::PLE_MODEL_PROJECTION, tower::PLE_PROJECTION_NORM, tower::EMBED, tower::PLE_EMBED, tower::FINAL_NORM] {
        regions.insert(name.to_owned(), region_of(source, name)?);
    }
    Ok(regions)
}

/// The regions one layer's segment stages, **in the order `tower::mount_layer` mounts them**, so
/// the pooled mount and the per-deed mount name the same maps in the same order.
pub fn layer_segment(source: &Source, layer: usize, slot: usize, pinned: usize) -> Result<Segment, String> {
    let mut regions = Vec::new();
    let mut names = Vec::new();
    for name in tower::populations(layer) {
        regions.push(staged_of(source, &name)?);
        names.push(name);
    }
    // The layer's 256 rows of the per-layer model projection, mounted under the whole tensor's name.
    let whole = source.container.tensor(tower::PLE_MODEL_PROJECTION).map_err(|e| e.to_string())?;
    let dim = whole.shape[1];
    regions.push(StagedRegion {
        population: format!("{} rows {}..{}", tower::PLE_MODEL_PROJECTION, tower::PLE_WIDTH * layer, tower::PLE_WIDTH * (layer + 1)),
        start: source.container.payload_base() + whole.start + (tower::PLE_WIDTH * layer * dim * 2) as u64,
        words: (tower::PLE_WIDTH * dim) as u32,
        dim,
    });
    names.push(tower::PLE_MODEL_PROJECTION.to_owned());
    regions.push(staged_of(source, tower::PLE_PROJECTION_NORM)?);
    names.push(tower::PLE_PROJECTION_NORM.to_owned());
    let scalar = staged_of(source, &tower::named(layer, "layer_scalar"))?;
    Ok(Segment { layer: Some(layer), slot, pinned, regions, names, scalar: Some(scalar) })
}

/// The final deed's segment: the final norm gain and the tied output table.
pub fn final_segment(source: &Source, slot: usize, pinned: usize) -> Result<Segment, String> {
    let mut regions = Vec::new();
    let mut names = Vec::new();
    for name in [tower::FINAL_NORM, tower::EMBED] {
        regions.push(staged_of(source, name)?);
        names.push(name.to_owned());
    }
    Ok(Segment { layer: None, slot, pinned, regions, names, scalar: None })
}

/// The pool slot shapes, from the segments alone: the widest layer decides both alternating slots,
/// and the final deed has its own. Every number is derived from the container's header.
pub fn slot_shapes(layers: &[Segment], last: &Segment) -> Vec<SlotShape> {
    let widest = |segments: &[&Segment]| -> (usize, usize, usize, usize) {
        let mut aligned = 0usize;
        let mut stored = 0usize;
        let mut mass = 0usize;
        let mut maps = 0usize;
        for segment in segments {
            aligned = aligned.max(segment.regions.iter().map(|r| r.words as usize * 8).sum::<usize>());
            stored = stored.max(segment.regions.iter().map(StagedRegion::octets).sum::<usize>());
            mass = mass.max(segment.regions.iter().map(|r| r.rows() * 16).sum::<usize>());
            maps = maps.max(segment.regions.len());
        }
        (aligned, stored, mass, 16 * maps)
    };
    let every: Vec<&Segment> = layers.iter().collect();
    let (aligned, stored, mass, scratch) = widest(&every);
    let (final_aligned, final_stored, final_mass, final_scratch) = widest(&[last]);
    vec![
        SlotShape { name: "pooled source standing, slot 0 (even source layers)".to_owned(), aligned_octets: aligned, stored_octets: stored, mass_octets: mass, scratch_octets: scratch },
        SlotShape { name: "pooled source standing, slot 1 (odd source layers)".to_owned(), aligned_octets: aligned, stored_octets: stored, mass_octets: mass, scratch_octets: scratch },
        SlotShape { name: "pooled source standing, slot 2 (the final boundary)".to_owned(), aligned_octets: final_aligned, stored_octets: final_stored, mass_octets: final_mass, scratch_octets: final_scratch },
    ]
}

/// One layer's receipt in the circulation. Deliberately narrow: the faces a receiver reads are the
/// terminal ones, and the loop reads none of them.
pub struct SegmentReceipt {
    pub layer: Option<usize>,
    pub slot: usize,
    /// Maps staged, crossed and mounted in this segment.
    pub maps: usize,
    pub species: Option<Species>,
    pub role: Option<KvRole>,
    pub operations: usize,
    pub fronts: usize,
    pub graph_nodes: usize,
    pub graph_edges: usize,
    pub captured_launches: u64,
    pub seals_fused: usize,
    pub seals_refused: Vec<(EventId, String)>,
    pub quotients: usize,
    pub collapsed_width_sum: u128,
    pub collapsed_width_max: u64,
    pub collapsed_nonzero: u64,
    pub lineage_empty: bool,
    pub a_priori_held: bool,
    pub every_front_certified: bool,
    pub deed: ExactWork,
    pub material_resident_octets: u64,
    pub stage_wall_s: f64,
    pub mount_wall_s: f64,
    pub bind_wall_s: f64,
}

/// What the whole circulation returned.
pub struct Circulated {
    pub tokens: Vec<usize>,
    pub segments: Vec<SegmentReceipt>,
    pub potential: Vec<(i64, i64)>,
    pub final_normed: Vec<(i64, i64)>,
    pub tower_work: ExactWork,
    pub streamed: StreamedCensus,
    pub census_before: TransferCensus,
    pub census_after: TransferCensus,
    pub census_at_loop_open: TransferCensus,
    pub census_at_loop_close: TransferCensus,
    pub peak_charged_octets: u64,
    pub wall_s: f64,
    pub loop_wall_s: f64,
    pub admission: MaterialAdmission,
    pub deed_launches: u64,
    /// Segments whose lineage carried a refusal, with the obstruction said whole, the population
    /// of the complete lineage and how many of them originated it.
    pub obstructions: Vec<(usize, String, usize, usize)>,
    /// The refusal a terminal read returned instead of words, where one did.
    pub terminal_refusal: Option<String>,
    /// **The §5.4 key this circulation's executables were bound under.** Founded, stated, and
    /// UNEXERCISED: no cache exists here and no reuse is claimed.
    pub graph_key: GraphKey,
}

/// One obstruction, said whole. The same shape `phoenix/conduct.rs` prints, restated here so the
/// streamed site depends on no other site.
pub fn describe(obstruction: &FrontPassageObstruction) -> String {
    match obstruction {
        FrontPassageObstruction::Cover { front, barriers } => format!("CoverBarrier at front {front}: {barriers:?}"),
        FrontPassageObstruction::Interchange { front, because, .. } => format!("InterchangeRefusal at front {front}: {because:?}"),
        FrontPassageObstruction::Resource(resource) => format!("ResourceObstruction: {resource:?}"),
        FrontPassageObstruction::Compile(refusal) => format!("CompileRefusal: {refusal}"),
        FrontPassageObstruction::Refused { occurrence, operation, refusal, lineage, .. } => {
            format!("the card refused at {occurrence:?} ({operation}): {refusal}; lineage {:?}", lineage.refusals)
        }
        FrontPassageObstruction::Sealed { occurrence, quotient, reopening } => {
            format!("the section at {occurrence:?} was sealed away by the fused quotient {quotient:?}; {reopening}")
        }
    }
}

/// Read one BF16 word straight out of the container — the layer scalar, which is a host dyadic and
/// is mounted nowhere.
pub fn scalar_word_of(file: &std::fs::File, region: &StagedRegion) -> Result<u16, String> {
    let mut octets = [0u8; 2];
    file.read_exact_at(&mut octets, region.start).map_err(|e| e.to_string())?;
    Ok(u16::from_le_bytes(octets))
}

/// **The tower, as one streamed circulation.**
///
/// One pre-deed admission, 43 segments each bounded by a pinned-staging refill, 43 graph
/// executables launched onto one conducting current with no synchronization between them, and one
/// terminal synchronization. Between two segments the apparatus stages octets, crosses them,
/// mounts them and launches — and reads nothing.
#[allow(clippy::too_many_arguments)]
pub fn circulate(
    surface: &'static ResidentSurface<'static>,
    _readout: &'static ResidentReadout,
    source: &mut Source,
    root: &str,
    tokens: &[usize],
    grain: ResidentGrain,
    terms: SeriesAperture,
    chart: tower::Chart,
    fuse: bool,
    content_sha256: Option<String>,
    // `limit`: how many source layers to conduct. The whole tower is `tower::LAYERS`; a control
    // conducts fewer and the final boundary still runs on whatever standing arrived.
    // `poison`: a control — one entering codeword replaced by a pattern that is not a finite BF16
    // value, so the mouth refuses it on the card and every successor in that deed carries it.
    limit: usize,
    poison: bool,
) -> Result<Circulated, String> {
    let clock = Instant::now();
    let census_before = surface.census();
    let passage = FrontPassage::new(surface, grain);
    let receiver = DeedReceiver::unbounded();
    let scales = tower::algebraic_scales()?;
    let no_intervention = Intervention::None;

    // ---------------------------------------------------------------------------------------
    // before the deed: the segments, the admission, the standing, and the one source occurrence
    // ---------------------------------------------------------------------------------------
    let mut layer_segments = Vec::with_capacity(tower::LAYERS);
    for layer in 0..tower::LAYERS {
        layer_segments.push(layer_segment(source, layer, layer % 2, layer % 3)?);
    }
    let last = final_segment(source, FINAL_SLOT, FINAL_PINNED)?;
    let shapes = slot_shapes(&layer_segments, &last);
    let refills = vec![(tower::LAYERS as u64).div_ceil(2), (tower::LAYERS as u64) / 2, 1];
    let bands_elements = tower::SLIDING_HEAD / 2 + tower::FULL_HEAD / 2;
    let prediction = passage.predict_pooled_material(&shapes, &refills, bands_elements, tokens.len());
    let admission = passage.admit_material(&prediction).map_err(|o| format!("the tower's pooled material refused: {}", describe(&o)))?;

    let regions = header_regions(source)?;
    let occurrence: SourceOccurrence = super::resident_layer::source_occurrence(root, regions, content_sha256)?;
    let identity_before = occurrence.container.identity.clone();

    // THREE pinned slots for the source layers and one for the final boundary. Three, not two,
    // because the staged read runs two segments ahead of the mount while the crossing runs one
    // ahead: with two slots the read of segment k+2 would have to wait on the copy of segment k+1,
    // which is the copy that is supposed to be crossing while segment k's graph conducts.
    let pinned = vec![shapes[0].stored_octets, shapes[0].stored_octets, shapes[0].stored_octets, shapes[2].stored_octets];
    let mut circulation = StreamedCirculation::open(surface, &shapes, &pinned).map_err(|e| e.to_string())?;

    // The material, held for the WHOLE circulation. The bands, the positions and the entering
    // codewords cross once; only the maps and the carried standings move between segments.
    let mut material = ResidentMaterial::empty();
    let sliding_bands = tower::found_bands(Species::Sliding, super::resident_layer::BAND_TERMS)?;
    let full_bands = tower::found_bands(Species::Full, super::resident_layer::BAND_TERMS)?;
    material.bands.insert(tower::SLIDING_BANDS.to_owned(), (surface.mount_bands(&sliding_bands, tower::BAND_GRAIN).map_err(|e| e.to_string())?, (tokens.len() - 1) as u32));
    material.bands.insert(tower::FULL_BANDS.to_owned(), (surface.mount_bands(&full_bands, tower::BAND_GRAIN).map_err(|e| e.to_string())?, (tokens.len() - 1) as u32));
    let positions: Vec<u32> = (0..tokens.len() as u32).collect();
    material.positions = Some(surface.mount_positions(&positions).map_err(|e| e.to_string())?);

    // The runtime-supplied entering rows, read ONCE for the whole tower: the embedding row of each
    // token, and its per-layer embedding row, which every layer slices differently.
    let mut entering = Vec::with_capacity(tokens.len() * tower::HIDDEN);
    let mut per_layer_rows: Vec<Vec<u16>> = Vec::with_capacity(tokens.len());
    for token in tokens {
        let (row, width) = source.rows(tower::EMBED, *token, 1)?;
        if width != tower::HIDDEN {
            return Err(format!("{} is {width} wide", tower::EMBED));
        }
        entering.extend(row);
        let (row, _) = source.rows(tower::PLE_EMBED, *token, 1)?;
        per_layer_rows.push(row);
    }
    if poison {
        // 0x7F80 is a BF16 infinity: not a finite value, so the mouth raises MALFORMED on the card
        // rather than placing anything, and the refusal travels the deed's declared lineage.
        entering[0] = 0x7F80;
    }
    material.entering.insert(tower::ENTERING.to_owned(), EnteringRows { words: entering, rows: tokens.len(), width: tower::HIDDEN });

    // Every layer's scalar, read before the deed: one stored word each, a host dyadic, mounted
    // nowhere. Reading them here keeps the loop's exterior contact to the staged refill alone.
    let mut layer_scalars = Vec::with_capacity(tower::LAYERS);
    for segment in &layer_segments {
        let region = segment.scalar.as_ref().ok_or("the layer segment carries no layer scalar")?;
        layer_scalars.push(Dyadic::of_bfloat16_bits(scalar_word_of(&source.file, region)?).map_err(|e| e.to_string())?);
    }

    // ---------------------------------------------------------------------------------------
    // the circulation
    // ---------------------------------------------------------------------------------------
    let census_at_loop_open = surface.census();
    let loop_clock = Instant::now();
    let mut carried: Option<(Rc<ResidentSection<'static>>, u32)> = None;
    let mut shared: BTreeMap<&'static str, (Rc<ResidentSection<'static>>, u32)> = BTreeMap::new();
    let mut bound_deeds: Vec<(holonic_engine::front_passage::CompiledPassage<'static>, TransferCensus, BTreeMap<&'static str, EventId>)> = Vec::new();
    let mut receipts: Vec<SegmentReceipt> = Vec::new();
    let mut tower_work = ExactWork::nothing();
    let mut peak_charged_octets = 0u64;
    let mut deed_launches = 0u64;

    // **The pipeline.** The staged read runs two segments ahead of the mount and the crossing one
    // ahead, so segment k+1's copy is issued IMMEDIATELY after segment k's graph is launched and
    // crosses while that graph conducts. Measured 2026-08-19: with the copy issued after the next
    // staged read instead, every copy landed after the graph it was meant to overlap and the
    // profiler read 0 ns of overlap — every stream asynchronous, and nothing concurrent.
    let segments = tower::LAYERS.min(limit) + 1;
    let at = |i: usize| -> &Segment { if i + 1 < segments { &layer_segments[i] } else { &last } };
    let mut offsets: Vec<Vec<usize>> = vec![Vec::new(); segments];
    let mut requests: Vec<Vec<holonic_engine::embedding_fiber::PooledMount>> = vec![Vec::new(); segments];
    let mut stage_wall: Vec<f64> = vec![0.0; segments];
    {
        let first = at(0);
        let clock = Instant::now();
        offsets[0] = circulation.stage(first.pinned, &source.file, source.container.file_octets, &first.regions).map_err(|e| e.to_string())?;
        stage_wall[0] = clock.elapsed().as_secs_f64();
        requests[0] = circulation.cross(first.slot, first.pinned, &offsets[0], &first.regions).map_err(|e| e.to_string())?;
        if segments > 1 {
            let second = at(1);
            let clock = Instant::now();
            offsets[1] = circulation.stage(second.pinned, &source.file, source.container.file_octets, &second.regions).map_err(|e| e.to_string())?;
            stage_wall[1] = clock.elapsed().as_secs_f64();
        }
    }

    for layer in 0..tower::LAYERS.min(limit) {
        let segment = &layer_segments[layer];
        let species = Species::of(layer);
        let role = KvRole::of(layer);
        let layer_scalar = layer_scalars[layer];
        let stage_wall_s = stage_wall[layer];
        // the layer's slice of each token's per-layer embedding row
        let mut per_layer = Vec::with_capacity(tokens.len() * tower::PLE_WIDTH);
        for row in &per_layer_rows {
            let from = layer * tower::PLE_WIDTH;
            if row.len() < from + tower::PLE_WIDTH {
                return Err(format!("{} is {} wide", tower::PLE_EMBED, row.len()));
            }
            per_layer.extend_from_slice(&row[from..from + tower::PLE_WIDTH]);
        }
        material.entering.insert(super::resident_layer::PLE_ENTERING.to_owned(), EnteringRows { words: per_layer, rows: tokens.len(), width: tower::PLE_WIDTH });

        // --- the mouth, on its own current, over the slot the copy already filled ---
        let mount_clock = Instant::now();
        let mounted = circulation.mount(segment.slot, segment.pinned, &requests[layer]).map_err(|e| e.to_string())?;
        material.populations.clear();
        for (name, pooled) in segment.names.iter().zip(mounted) {
            material.populations.insert(name.clone(), MountedPopulation { readout: pooled.readout, mass_value_octaves: pooled.mass_value_octaves });
        }
        let mount_wall_s = mount_clock.elapsed().as_secs_f64();

        // --- the standings this layer enters on ---
        material.standings.clear();
        if let Some((section, bound)) = &carried {
            material.standings.insert(tower::CARRIED_STANDING.to_owned(), (Rc::clone(section), *bound));
        }
        if role == KvRole::Shared {
            let (k_name, v_name) = match species {
                Species::Sliding => (tower::SHARED_K_SLIDING, tower::SHARED_V_SLIDING),
                Species::Full => (tower::SHARED_K_FULL, tower::SHARED_V_FULL),
            };
            let (k, kb) = shared.get(k_name).ok_or_else(|| format!("layer {layer}: no shared K standing"))?;
            let (v, vb) = shared.get(v_name).ok_or_else(|| format!("layer {layer}: no shared V standing"))?;
            material.standings.insert(k_name.to_owned(), (Rc::clone(k), *kb));
            material.standings.insert(v_name.to_owned(), (Rc::clone(v), *vb));
        }

        // --- the diagram, and the apparatus fusion the receiver's declarations admit ---
        let bind_clock = Instant::now();
        let entry = if layer == 0 { Entry::Rows } else { Entry::Carried };
        let mut founded = tower::found_layer(layer, entry, chart, &scales, terms, layer_scalar, &no_intervention, tokens.len())?;
        let terminal = founded.returns[tower::LAYER_RETURN];
        let (fusable, refused) = if fuse {
            factored_seals(&founded.complex, &founded.realization, terminal, &BTreeSet::new())
        } else {
            (Vec::new(), Vec::new())
        };
        for occurrence in &fusable {
            founded.realization.bind(*occurrence, SealedMidpointQuotient);
        }
        let bound = passage
            .bind(&founded.complex, &founded.realization, &material, &occurrence, &receiver, Some(&admission), terminal)
            .map_err(|o| format!("layer {layer} refused at bind: {}", describe(&o)))?;
        let bind_wall_s = bind_clock.elapsed().as_secs_f64();
        peak_charged_octets = peak_charged_octets.max(admission.prediction.charged_octets + bound.apparatus_prediction.charged_octets);
        let (graph, _) = bound.graph();
        let graph_nodes = graph.nodes;
        let graph_edges = graph.edges;

        // --- the deed: launched onto the conducting current, and NOT waited for ---
        circulation.admit_segment(segment.slot).map_err(|e| e.to_string())?;
        let census_at_launch = bound.launch_on(&surface.mode(), circulation.conducting()).map_err(|o| format!("layer {layer} refused at launch: {}", describe(&o)))?;
        circulation.conducted(segment.slot).map_err(|e| e.to_string())?;
        deed_launches += 1;
        tower_work = tower_work.then(&bound.deed_prediction);

        // The next segment's copy, issued now so it crosses while THIS deed conducts, and the one
        // after it staged from the container. Neither reads a semantic value; both are transports.
        if layer + 1 < segments {
            let next = at(layer + 1);
            requests[layer + 1] = circulation.cross(next.slot, next.pinned, &offsets[layer + 1], &next.regions).map_err(|e| e.to_string())?;
        }
        if layer + 2 < segments {
            let after = at(layer + 2);
            let clock = Instant::now();
            offsets[layer + 2] = circulation.stage(after.pinned, &source.file, source.container.file_octets, &after.regions).map_err(|e| e.to_string())?;
            stage_wall[layer + 2] = clock.elapsed().as_secs_f64();
        }

        let mut bound = bound;
        // The standings the next deeds carry. Releasing moves ownership of a device section; it
        // reads nothing and crosses nothing.
        if role == KvRole::OwnAndStore {
            let (k_name, v_name) = match species {
                Species::Sliding => (tower::SHARED_K_SLIDING, tower::SHARED_V_SLIDING),
                Species::Full => (tower::SHARED_K_FULL, tower::SHARED_V_FULL),
            };
            let (k, kb) = bound.release_section(founded.returns[tower::K_STANDING]).ok_or("K standing")?;
            let (v, vb) = bound.release_section(founded.returns[tower::V_STANDING]).ok_or("V standing")?;
            shared.insert(k_name, (Rc::new(k), kb));
            shared.insert(v_name, (Rc::new(v), vb));
        }
        let (out, ob) = bound.release_section(terminal).ok_or("layer return")?;
        carried = Some((Rc::new(out), ob));

        receipts.push(SegmentReceipt {
            layer: Some(layer),
            slot: segment.slot,
            maps: segment.regions.len(),
            species: Some(species),
            role: Some(role),
            operations: founded.complex.operations.len(),
            fronts: bound.fronts().len(),
            graph_nodes,
            graph_edges,
            captured_launches: bound.apparatus_prediction.captured_launches,
            seals_fused: fusable.len(),
            seals_refused: refused,
            quotients: 0,
            collapsed_width_sum: 0,
            collapsed_width_max: 0,
            collapsed_nonzero: 0,
            lineage_empty: false,
            a_priori_held: false,
            every_front_certified: bound.fronts().iter().all(|f| f.certificate.because().is_none()),
            deed: bound.deed_prediction.clone(),
            material_resident_octets: material.resident_octets(),
            stage_wall_s,
            mount_wall_s,
            bind_wall_s,
        });
        let mut named: BTreeMap<&'static str, EventId> = BTreeMap::new();
        for (name, event) in &founded.returns {
            named.insert(name, *event);
        }
        bound_deeds.push((bound, census_at_launch, named));
    }

    // --- the final deed: the same circulation, its own slot, its crossing already in flight ---
    let stage_wall_s = stage_wall[segments - 1];
    let mount_clock = Instant::now();
    let mounted = circulation.mount(last.slot, last.pinned, &requests[segments - 1]).map_err(|e| e.to_string())?;
    material.populations.clear();
    for (name, pooled) in last.names.iter().zip(mounted) {
        material.populations.insert(name.clone(), MountedPopulation { readout: pooled.readout, mass_value_octaves: pooled.mass_value_octaves });
    }
    let mount_wall_s = mount_clock.elapsed().as_secs_f64();
    material.standings.clear();
    let (section, bound_octaves) = carried.take().ok_or("no carried standing")?;
    material.standings.insert(tower::CARRIED_STANDING.to_owned(), (section, bound_octaves));
    let bind_clock = Instant::now();
    let mut founded = tower::found_final(chart, &no_intervention, &scales)?;
    let terminal = founded.returns[tower::POTENTIAL];
    // The final normed standing is a face this receiver reads, and it is itself the QUOTIENT: its
    // own face is the collapsed one, which the fused seal writes into its predecessor's buffer and
    // `read_section` resolves through. Nothing is declared, because the fusion condition is about a
    // quotient's PREDECESSOR and no receiver reads the pre-quotient enclosure here.
    let declared: BTreeSet<EventId> = BTreeSet::new();
    let passage_final = FrontPassage::new(surface, grain);
    let (fusable, refused) = if fuse { factored_seals(&founded.complex, &founded.realization, terminal, &declared) } else { (Vec::new(), Vec::new()) };
    for occurrence in &fusable {
        founded.realization.bind(*occurrence, SealedMidpointQuotient);
    }
    let bound = passage_final
        .bind(&founded.complex, &founded.realization, &material, &occurrence, &receiver, Some(&admission), terminal)
        .map_err(|o| format!("the final deed refused at bind: {}", describe(&o)))?;
    let bind_wall_s = bind_clock.elapsed().as_secs_f64();
    peak_charged_octets = peak_charged_octets.max(admission.prediction.charged_octets + bound.apparatus_prediction.charged_octets);
    let (graph, _) = bound.graph();
    let (graph_nodes, graph_edges) = (graph.nodes, graph.edges);
    circulation.admit_segment(last.slot).map_err(|e| e.to_string())?;
    let census_at_launch = bound.launch_on(&surface.mode(), circulation.conducting()).map_err(|o| format!("the final deed refused at launch: {}", describe(&o)))?;
    circulation.conducted(last.slot).map_err(|e| e.to_string())?;
    deed_launches += 1;
    tower_work = tower_work.then(&bound.deed_prediction);
    receipts.push(SegmentReceipt {
        layer: None,
        slot: last.slot,
        maps: last.regions.len(),
        species: None,
        role: None,
        operations: founded.complex.operations.len(),
        fronts: bound.fronts().len(),
        graph_nodes,
        graph_edges,
        captured_launches: bound.apparatus_prediction.captured_launches,
        seals_fused: fusable.len(),
        seals_refused: refused,
        quotients: 0,
        collapsed_width_sum: 0,
        collapsed_width_max: 0,
        collapsed_nonzero: 0,
        lineage_empty: false,
        a_priori_held: false,
        every_front_certified: bound.fronts().iter().all(|f| f.certificate.because().is_none()),
        deed: bound.deed_prediction.clone(),
        material_resident_octets: material.resident_octets(),
        stage_wall_s,
        mount_wall_s,
        bind_wall_s,
    });
    let mut named: BTreeMap<&'static str, EventId> = BTreeMap::new();
    for (name, event) in &founded.returns {
        named.insert(name, *event);
    }
    bound_deeds.push((bound, census_at_launch, named));

    let census_at_loop_close = surface.census();
    let loop_wall_s = loop_clock.elapsed().as_secs_f64();

    // ---------------------------------------------------------------------------------------
    // ONE terminal synchronization, and only then a reading
    // ---------------------------------------------------------------------------------------
    circulation.terminal().map_err(|e| e.to_string())?;
    let streamed = circulation.census().clone();

    let mut potential = Vec::new();
    let mut final_normed = Vec::new();
    let mut obstructions: Vec<(usize, String, usize, usize)> = Vec::new();
    let mut terminal_refusal: Option<String> = None;
    for (at, (bound, census_at_launch, named)) in bound_deeds.iter().enumerate() {
        let returned = bound.returned(census_at_launch.clone()).map_err(|o| format!("segment {at} did not return: {}", describe(&o)))?;
        if let Err(obstruction) = bound.standing(&returned) {
            // The circulation does not stop: stopping would require the apparatus to inspect a
            // semantic value between segments, which is the one thing this deed forbids. The
            // complete lineage is returned here, after the fact, whole.
            let lineage = returned.obstruction.refusals.len();
            let origins = returned.obstruction.origins().count();
            obstructions.push((at, describe(&obstruction), lineage, origins));
        }
        let receipt = &mut receipts[at];
        receipt.lineage_empty = returned.stands();
        receipt.a_priori_held = returned.measured_octaves.iter().all(|(port, measured)| bound.octave_field.get(port).copied().unwrap_or(0) >= *measured);
        for front in &returned.fronts {
            for reading in &front.readings {
                if reading.operation.starts_with("midpoint-quotient") {
                    receipt.quotients += 1;
                } else if reading.operation != "enter" && reading.operation != "carry" {
                    receipt.collapsed_width_sum += u128::from(reading.measured.width_sum);
                    receipt.collapsed_width_max = receipt.collapsed_width_max.max(reading.measured.max_width);
                    receipt.collapsed_nonzero += u64::from(reading.measured.nonzero_widths);
                }
            }
        }
        if at + 1 == bound_deeds.len() {
            match bound.read_section(&returned, named[tower::FINAL_NORMED]) {
                Ok(read) => final_normed = read,
                Err(obstruction) => terminal_refusal = Some(describe(&obstruction)),
            }
            match bound.read_terminal(&returned) {
                Ok(read) => potential = read,
                Err(obstruction) => terminal_refusal = Some(describe(&obstruction)),
            }
        }
    }

    // The container has not moved under the deed.
    occurrence.container.verify_still().map_err(|e| format!("the container moved under the circulation: {e}"))?;
    if occurrence.container.identity != identity_before {
        return Err("the container's identity moved under the circulation".to_owned());
    }

    // The §5.4 key, composed from what this circulation actually holds. Nothing is hashed and
    // nothing is invented: the mode is the surface's, the source is the occurrence's container, the
    // topology is every segment's own census, the ports are the extents this input closure sizes
    // every kernel by, and the reductions are the first segment's coupling plans verbatim.
    let mut reductions: Vec<(String, u64)> = Vec::new();
    if let Some((first, _, _)) = bound_deeds.first() {
        for front in first.fronts() {
            for coupling in &front.couplings {
                reductions.push((coupling.plan.kernel.to_owned(), coupling.plan.extent));
            }
        }
    }
    let container = &occurrence.container;
    let graph_key = GraphKey {
        mode: format!("{:?}", surface.mode()),
        source: format!(
            "{} octets, header {} octets, header sha256 {}, content sha256 {:?}, identity {:?}",
            container.octets, container.header_octets, container.header_sha256, container.content_sha256, container.identity
        ),
        topology: receipts.iter().map(|r| (r.operations, r.fronts, r.graph_nodes, r.graph_edges)).collect(),
        ports: vec![
            ("continuing standing".to_owned(), tokens.len(), tower::HIDDEN),
            ("per-layer section".to_owned(), tokens.len(), tower::PLE_WIDTH),
            ("gated passage chart".to_owned(), tokens.len(), tower::FFN),
            ("potential section".to_owned(), tokens.len(), tower::VOCABULARY),
        ],
        grain: grain.0,
        series_terms: terms.0,
        reductions,
        receiver_boundary: format!(
            "the declared terminal of each segment ({} layer returns and one potential section); no other face was declared, which is why every seal factored",
            receipts.len() - 1
        ),
        // The residency this circulation's executables baked in: the final deed's carried standing
        // is the one addressed section that is not the pool's, and the pool's own addresses are
        // fixed for the whole circulation. One tower, so no second deed contends for it — which is
        // exactly why H4 could not have found this field, and H5's cohort is where it is exercised.
        // H4 declares no chronology on its key: the circulation holds 43 diagrams and drops each
        // as it launches, so the names are not retained here. Deed H5's cohort retains them,
        // because a cohort is where two deeds share every count and differ by one occurrence.
        chronology: Vec::new(),
        material: material
            .standings
            .iter()
            .map(|(name, (section, _))| (name.clone(), section.ranges()[0].0, section.rows(), section.width()))
            .collect(),
    };

    let census_after = surface.census();
    circulation.close();
    Ok(Circulated {
        tokens: tokens.to_vec(),
        segments: receipts,
        potential,
        final_normed,
        tower_work,
        streamed,
        census_before,
        census_after,
        census_at_loop_open,
        census_at_loop_close,
        peak_charged_octets,
        wall_s: clock.elapsed().as_secs_f64(),
        loop_wall_s,
        admission,
        deed_launches,
        obstructions,
        terminal_refusal,
        graph_key,
    })
}
