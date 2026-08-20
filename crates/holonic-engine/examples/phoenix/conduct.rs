//! # SUPERSEDED 2026-08-20 BY DEED H5. COMMITTED EVIDENCE, NOT A SITE FOR NEW CONSTRUCTION.
//!
//! This is the per-layer apparatus foreman: it rebuilds a `SourceOccurrence` per layer, re-reads
//! and re-digests every region per layer, mounts one map at a time, allocates and frees per deed,
//! launches once and **synchronizes once per layer**, and conducts one complete tower per matched
//! sibling. Deed H4 replaced its circulation (`phoenix/streamed.rs`) and **Deed H5 replaced its
//! dissection** (`phoenix/cohort.rs`): the base prefix conducts once, every sibling conducts only
//! its suffix on the base's standing shared read-only, and one layer's maps mount once for the
//! whole cohort crossing that layer. Every receiver-family comparison of this foreman's committed
//! artifact returns unchanged under the new site — 104 cells of
//! `output/the_source_is_dissected/dissection-5-tokens-grain-48-terms-14.form`, parsed and compared
//! programmatically by `examples/the_dissection_shares_its_prefixes.rs`, 0 drifted — and the same
//! taxon conducted both ways in one circulation returns all 128 faces bit-identical.
//!
//! **Why the file is still here.** The plan's §10 requires that an old path be deleted without
//! fallback once every consumer is located, and every consumer IS located: this module has exactly
//! one, `examples/the_source_is_dissected_by_intervention.rs`, which is the producer of Station D's
//! committed artifact. `meta/DRIVER_CATALOG.tsv` requires every catalogued driver to be in the
//! tree and `meta/OUTPUT_MANIFEST.tsv` binds that artifact to that producer, so deleting either
//! would orphan committed evidence. The lawful form of the deletion is therefore this header: the
//! path is deleted from **live construction**, not from the tree.
//!
//! **What that means concretely, and it is checkable.** No new driver may include this module. The
//! H5 driver includes `phoenix/cohort.rs`, `phoenix/streamed.rs`, `phoenix/tower.rs` and
//! `phoenix/resident_layer.rs` and nothing else; it declares its own `Site` rather than importing
//! this one, so there is **no alias, no fallback and no dual schema** — the new path cannot reach
//! this one at all. `grep -rn 'phoenix/conduct.rs' crates/holonic-engine/examples/` returns exactly
//! one file, measured 2026-08-20, and that file is the committed predecessor. The same holds for
//! the tower-conducting foreman inside Station C's own driver
//! (`examples/the_tower_conducts_layer_by_layer_and_the_future_section_is_plural.rs`): it has no
//! consumer outside itself, it is the producer of Station C's committed artifact, and it stays as
//! evidence under the same rule.
//!
//! ---
//!
//! **The tower deed with one declared intervention site** — the conduction Station C enacts,
//! parameterized by a matched sibling's intervention at one site, reading the receiver family's
//! faces (every layer's return, contact and per-layer input section, the final normed standing and
//! the potential) so a base deed and its sibling can be compared face by face. Shared by the
//! dissection drivers; Station C's driver keeps its own conduction with its own receipt.

use std::collections::BTreeMap;
use std::rc::Rc;
use std::time::Instant;

use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::exact_work::ExactWork;
use holonic_engine::front_passage::{DeedReceiver, FrontPassage, FrontPassageObstruction, MaterialAdmission, ResidentMaterial};
use holonic_engine::resident_section::{ResidentGrain, ResidentSection, ResidentSurface, SeriesAperture};
use holonic_engine::source_occurrence::{RegionIdentity, SourceOccurrence};

use super::resident_layer::{self, Source};
use super::tower::{self, Entry, Intervention, KvRole, Species};

/// Where the sibling's intervention is applied.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Site {
    /// the base deed: no intervention anywhere
    Nowhere,
    /// one layer's graph
    Layer(usize),
    /// every layer's graph (the initial embedding enters every layer)
    EveryLayer,
    /// the final graph
    Final,
}

pub fn describe(obstruction: &FrontPassageObstruction) -> String {
    match obstruction {
        FrontPassageObstruction::Cover { front, barriers } => format!("CoverBarrier at front {front}: {barriers:?}"),
        FrontPassageObstruction::Interchange { front, because, .. } => format!("InterchangeRefusal at front {front}: {because:?}"),
        FrontPassageObstruction::Resource(resource) => format!("ResourceObstruction: {resource:?}"),
        FrontPassageObstruction::Compile(refusal) => format!("CompileRefusal: {refusal}"),
        FrontPassageObstruction::Refused { occurrence, operation, refusal, lineage, .. } => format!("the card refused at {occurrence:?} ({operation}): {refusal}; lineage {:?}", lineage.refusals),
        FrontPassageObstruction::Sealed { occurrence, quotient, reopening } => format!("the section at {occurrence:?} was sealed away by the fused quotient {quotient:?}; {reopening}"),
    }
}

/// One layer's faces and testimony under one deed.
#[allow(dead_code)]
pub struct LayerFace {
    pub layer: usize,
    pub species: Species,
    pub role: KvRole,
    /// every operation of the layer's complex, in chronology: its name and whether its testimony is
    /// wholly the caller's intervention
    pub operations: Vec<(String, bool)>,
    /// how many of them are the caller's interventions (typed so)
    pub intervention_occurrences: usize,
    pub fronts: usize,
    pub graph_nodes: usize,
    pub lineage_empty: bool,
    pub a_priori_held: bool,
    pub deed: ExactWork,
    /// the layer return (every position × HIDDEN), read before the seal: enclosures
    pub terminal: Vec<(i64, i64)>,
    /// the contact section (every position × HEADS·head), read before its seal
    pub contact: Vec<(i64, i64)>,
    /// the per-layer input section after the join (every position × PLE_WIDTH)
    pub ple: Vec<(i64, i64)>,
    pub mount_wall_s: f64,
    pub bind_wall_s: f64,
}

#[allow(dead_code)]
pub struct Conducted {
    pub tokens: Vec<usize>,
    pub layers: Vec<LayerFace>,
    pub final_operations: Vec<(String, bool)>,
    pub final_intervention_occurrences: usize,
    pub final_normed: Vec<(i64, i64)>,
    pub potential: Vec<(i64, i64)>,
    pub tower_work: ExactWork,
    pub deed_launches: u64,
    pub peak_charged_octets: u64,
    pub wall_s: f64,
}

/// Every occurrence of the complex in chronology: its law's name, and whether it is wholly the
/// caller's intervention — decided by its TYPED testimony (every testimony an `Intervention`), never
/// by its name.
pub fn names_of(complex: &holonic_engine::ported_operation::PortedOperationComplex) -> Vec<(String, bool)> {
    complex
        .shape
        .occurrences
        .values()
        .map(|o| {
            let name = complex.shape.laws.get(&o.law).map(|l| l.name.clone()).unwrap_or_default();
            let typed = complex.operations.get(&o.law).is_some_and(|op| !op.testimony.is_empty() && op.testimony.iter().all(|t| matches!(t, holonic_engine::ported_operation::SourceTestimony::Intervention { .. })));
            (name, typed)
        })
        .collect()
}

/// **The tower deed for one input under one intervention site**: 42 layer graphs and the final
/// graph, each admitted, bound, launched once and released, the standings carried on the card.
#[allow(clippy::too_many_arguments)]
pub fn conduct(
    surface: &'static ResidentSurface<'static>,
    readout: &'static ResidentReadout,
    source: &mut Source,
    root: &str,
    header_regions: &BTreeMap<String, RegionIdentity>,
    content_sha256: &str,
    tokens: &[usize],
    grain: ResidentGrain,
    terms: SeriesAperture,
    chart: tower::Chart,
    site: Site,
    intervention: &Intervention,
) -> Result<Conducted, String> {
    let clock = Instant::now();
    let passage = FrontPassage::new(surface, grain);
    let receiver = DeedReceiver::unbounded();
    let scales = tower::algebraic_scales()?;
    let mut regions = header_regions.clone();
    let mut carried: Option<(Rc<ResidentSection<'static>>, u32)> = None;
    let mut shared: BTreeMap<&'static str, (Rc<ResidentSection<'static>>, u32)> = BTreeMap::new();
    let mut tower_work = ExactWork::nothing();
    let mut deed_launches = 0u64;
    let mut peak_charged_octets = 0u64;
    let sliding_bands = tower::found_bands(Species::Sliding, resident_layer::BAND_TERMS)?;
    let full_bands = tower::found_bands(Species::Full, resident_layer::BAND_TERMS)?;
    let identity_sliding = tower::identity_bands(sliding_bands.len());
    let identity_full = tower::identity_bands(full_bands.len());
    let positions: Vec<u32> = (0..tokens.len() as u32).collect();
    let reversed: Vec<u32> = (0..tokens.len() as u32).rev().collect();
    let mut layers: Vec<LayerFace> = Vec::new();
    for layer in 0..tower::LAYERS {
        let species = Species::of(layer);
        let role = KvRole::of(layer);
        let here = match site {
            Site::Layer(l) => l == layer,
            Site::EveryLayer => true,
            _ => false,
        };
        let applied: &Intervention = if here { intervention } else { &Intervention::None };
        let mut material = ResidentMaterial::empty();
        let mut plan = tower::material_plan(source, layer, tokens.len())?;
        // the intervention's own material is predicted with the layer's: a second band set for the
        // identity chronology, a permutation array for the head permutations
        match applied {
            Intervention::IdentityChronology => plan.band_elements += match species { Species::Sliding => identity_sliding.len(), Species::Full => identity_full.len() },
            Intervention::PermuteReceiverHeads { .. } | Intervention::PermuteCarriedHeads { .. } => plan.positions += tower::HEADS,
            _ => {}
        }
        let prediction = passage.predict_material(&plan);
        let admission: MaterialAdmission = passage.admit_material(&prediction).map_err(|o| format!("layer {layer} material refused: {}", describe(&o)))?;
        let mount_clock = Instant::now();
        let mount = tower::mount_layer(source, readout, &mut material, layer)?;
        let mount_wall_s = mount_clock.elapsed().as_secs_f64();
        for (name, region) in mount.regions {
            regions.insert(name, region);
        }
        let layer_scalar = mount.layer_scalar.ok_or("layer_scalar")?;
        let bands = match species {
            Species::Sliding => &sliding_bands,
            Species::Full => &full_bands,
        };
        let mounted_bands = surface.mount_bands(bands, tower::BAND_GRAIN).map_err(|e| e.to_string())?;
        material.bands.insert(species.bands().to_owned(), (mounted_bands, (tokens.len() - 1) as u32));
        if matches!(applied, Intervention::IdentityChronology) {
            let identity = match species {
                Species::Sliding => &identity_sliding,
                Species::Full => &identity_full,
            };
            let mounted = surface.mount_bands(identity, tower::BAND_GRAIN).map_err(|e| e.to_string())?;
            material.bands.insert(tower::IDENTITY_BANDS.to_owned(), (mounted, (tokens.len() - 1) as u32));
        }
        let layer_positions = if matches!(applied, Intervention::ReversedPositions) { &reversed } else { &positions };
        material.positions = Some(surface.mount_positions(layer_positions).map_err(|e| e.to_string())?);
        if let Intervention::PermuteReceiverHeads { a, b } | Intervention::PermuteCarriedHeads { a, b } = applied {
            let permutation: Vec<u32> = tower::swap_permutation(tower::HEADS, *a, *b).into_iter().map(|i| i as u32).collect();
            material.arrays.insert(tower::HEAD_PERMUTATION.to_owned(), surface.mount_positions(&permutation).map_err(|e| e.to_string())?);
        }
        tower::enter(source, tokens, layer, &mut material)?;
        let entry = if layer == 0 { Entry::Rows } else { Entry::Carried };
        if let Some((section, bound)) = &carried {
            material.standings.insert(tower::CARRIED_STANDING.to_owned(), (Rc::clone(section), *bound));
        }
        if role == KvRole::Shared {
            let (k_name, v_name) = match species {
                Species::Sliding => (tower::SHARED_K_SLIDING, tower::SHARED_V_SLIDING),
                Species::Full => (tower::SHARED_K_FULL, tower::SHARED_V_FULL),
            };
            let (k, kb) = shared.get(k_name).ok_or_else(|| format!("layer {layer}: no shared K standing {k_name}"))?;
            let (v, vb) = shared.get(v_name).ok_or_else(|| format!("layer {layer}: no shared V standing {v_name}"))?;
            material.standings.insert(k_name.to_owned(), (Rc::clone(k), *kb));
            material.standings.insert(v_name.to_owned(), (Rc::clone(v), *vb));
        }
        let occurrence: SourceOccurrence = resident_layer::source_occurrence(root, regions.clone(), Some(content_sha256.to_owned()))?;
        let founded = tower::found_layer(layer, entry, chart, &scales, terms, layer_scalar, applied, tokens.len())?;
        let operations = names_of(&founded.complex);
        let intervention_occurrences = operations.iter().filter(|(_, typed)| *typed).count();
        let bind_clock = Instant::now();
        let mut bound = passage.bind(&founded.complex, &founded.realization, &material, &occurrence, &receiver, Some(&admission), founded.returns[tower::LAYER_RETURN]).map_err(|o| format!("layer {layer} refused at bind: {}", describe(&o)))?;
        let bind_wall_s = bind_clock.elapsed().as_secs_f64();
        peak_charged_octets = peak_charged_octets.max(admission.prediction.charged_octets + bound.apparatus_prediction.charged_octets);
        let returned = bound.launch(&surface.mode()).map_err(|o| format!("layer {layer} refused at launch: {}", describe(&o)))?;
        deed_launches += 1;
        if let Err(o) = bound.standing(&returned) {
            let mut lines = Vec::new();
            for front in &returned.fronts {
                for r in &front.readings {
                    lines.push(format!("{}:{}≤{}{}", r.operation, r.measured.max_octave, r.bound, if r.measured.refused != 0 { format!("!{}", r.measured.refused) } else { String::new() }));
                }
            }
            return Err(format!("layer {layer} did not stand: {} · readings [{}]", describe(&o), lines.join(" ")));
        }
        let (graph, _) = bound.graph();
        let mut a_priori_held = true;
        for (port, measured) in &returned.measured_octaves {
            let b = bound.octave_field.get(port).copied().unwrap_or(0);
            if b < *measured {
                a_priori_held = false;
            }
        }
        let terminal = bound.read_section(&returned, founded.returns[tower::LAYER_ENCLOSURE]).map_err(|o| describe(&o))?;
        let contact = bound.read_section(&returned, founded.returns[tower::CONTACT]).map_err(|o| describe(&o))?;
        let ple = bound.read_section(&returned, founded.returns[tower::PLE_SECTION]).map_err(|o| describe(&o))?;
        tower_work = tower_work.then(&bound.deed_prediction);
        layers.push(LayerFace {
            layer,
            species,
            role,
            operations,
            intervention_occurrences,
            fronts: bound.fronts().len(),
            graph_nodes: graph.nodes,
            lineage_empty: returned.stands(),
            a_priori_held,
            deed: bound.deed_prediction.clone(),
            terminal,
            contact,
            ple,
            mount_wall_s,
            bind_wall_s,
        });
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
        let (out, ob) = bound.release_section(founded.returns[tower::LAYER_RETURN]).ok_or("layer return")?;
        carried = Some((Rc::new(out), ob));
        drop(bound);
        drop(material);
    }
    // the final deed
    let applied: &Intervention = if site == Site::Final { intervention } else { &Intervention::None };
    let mut material = ResidentMaterial::empty();
    let plan = tower::final_material_plan(source)?;
    let prediction = passage.predict_material(&plan);
    let admission = passage.admit_material(&prediction).map_err(|o| format!("final material refused: {}", describe(&o)))?;
    let mount = tower::mount_final(source, readout, &mut material)?;
    for (name, region) in mount.regions {
        regions.insert(name, region);
    }
    let (section, bound_octaves) = carried.take().ok_or("no carried standing")?;
    material.standings.insert(tower::CARRIED_STANDING.to_owned(), (section, bound_octaves));
    let occurrence = resident_layer::source_occurrence(root, regions.clone(), Some(content_sha256.to_owned()))?;
    let founded = tower::found_final(chart, applied, &scales)?;
    let final_operations = names_of(&founded.complex);
    let final_intervention_occurrences = final_operations.iter().filter(|(_, typed)| *typed).count();
    let bound = passage.bind(&founded.complex, &founded.realization, &material, &occurrence, &receiver, Some(&admission), founded.returns[tower::POTENTIAL]).map_err(|o| format!("final refused at bind: {}", describe(&o)))?;
    peak_charged_octets = peak_charged_octets.max(admission.prediction.charged_octets + bound.apparatus_prediction.charged_octets);
    let returned = bound.launch(&surface.mode()).map_err(|o| format!("final refused at launch: {}", describe(&o)))?;
    deed_launches += 1;
    bound.standing(&returned).map_err(|o| format!("final did not stand: {}", describe(&o)))?;
    let final_normed = bound.read_section(&returned, founded.returns[tower::FINAL_NORMED]).map_err(|o| describe(&o))?;
    let potential = bound.read_terminal(&returned).map_err(|o| describe(&o))?;
    tower_work = tower_work.then(&bound.deed_prediction);
    Ok(Conducted {
        tokens: tokens.to_vec(),
        layers,
        final_operations,
        final_intervention_occurrences,
        final_normed,
        potential,
        tower_work,
        deed_launches,
        peak_charged_octets,
        wall_s: clock.elapsed().as_secs_f64(),
    })
}
