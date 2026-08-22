//! **The dissection as one streamed circulation with shared prefixes** — the site that replaces
//! the per-tower foreman of `phoenix/conduct.rs` for Deed H5.
//!
//! The diagram is unchanged: every layer is founded by `phoenix/tower.rs`, from the same source
//! testimony, at the same grain, under the same declared quotient chart, with the same
//! `Intervention` at the same site. What changes is that **one base prefix is conducted once and
//! every matched sibling conducts only its suffix on it**, and that **one layer's maps are mounted
//! once for the whole cohort crossing that layer**.
//!
//! ```text
//!   the committed predecessor                 this site
//!   ---------------------------------------   ------------------------------------------------
//!   18 complete towers, each re-reading the    ONE pass over the container: every layer's maps
//!   whole container and re-mounting every      staged, crossed and mounted ONCE, and every
//!   layer (18 x 9.29 GB, 18 x 704 regions)     tower crossing that layer conducts on them
//!
//!   a sibling at layer L re-derives layers     the sibling ENTERS at L on the base's released
//!   0..L-1 identically to the base             standing, shared READ-ONLY: `Standing` records a
//!                                              `section_carry` whose only write is its own fresh
//!                                              output section
//!
//!   43 launches, 43 synchronizations per       one conducting current; the terminal
//!   tower                                      synchronization is per BAND, and a band's
//!                                              population is declared before the first launch
//! ```
//!
//! # What prefix sharing costs, stated before it is used
//!
//! A sibling that does not conduct layers `0..L` has **no faces of its own there**. The committed
//! predecessor MEASURED that those faces are bit-identical to the base's; here they *are* the
//! base's, so that control is **structural** and carries no evidence. It is reported as such and
//! never as a measurement. What remains falsifiable is the claim this site makes — that conducting
//! a suffix on a shared standing returns the same suffix faces a complete tower returns — and that
//! is answered two ways: against the committed artifact of the independent predecessor, and by the
//! **prefix control tower**, one declared sibling conducted BOTH ways in the same circulation.
//!
//! # The cohort's form, and what it saves
//!
//! The simplest lawful form: **plural bound passages per segment**. Weights mount once per layer
//! for the whole cohort; each sibling owns its own standings, its own sections and its own graph.
//! Rows are NOT batched into one kernel, so no cohort boundary is needed inside the contact law —
//! cross-sibling contact is impossible by construction rather than by a guard, because no two
//! siblings' rows ever enter one section. What this does not save: graph instantiations and graph
//! launches, which stay one per sibling per layer, and the entering codewords, which cross once
//! per deed.
//!
//! This is the owner-local plural-passage circulation. A driver supplies one authenticated
//! material occurrence and the declared siblings; this module owns only the shared-prefix and
//! once-per-region transport which all such consumers require.

#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;
use std::time::Instant;

use crate::causal::EventId;
use crate::embedding_fiber::ResidentReadout;
use crate::exact_work::ExactWork;
use crate::front_passage::{
    CompiledPassage, DeedReceiver, EnteringRows, FrontPassage, FrontPassageObstruction,
    MaterialAdmission, MountedPopulation, PooledMaterialAuxiliary, ResidentMaterial,
    ResourceObstruction, SealedMidpointQuotient, factored_seals,
};
use crate::interaction::OccurrencePort;
use crate::resident_section::{
    Dyadic, Positions, ResidentGrain, ResidentSection, ResidentSurface, SeriesAperture,
    TransferCensus,
};
use crate::streamed_standing::{
    GraphKey, Instantiation, KeyedInstantiations, StreamedCensus, StreamedCirculation,
};

use super::streamed::{
    FINAL_PINNED, FINAL_SLOT, MaterialSource, Segment, final_segment, layer_segment, slot_shapes,
};
use super::tower::{self, Entry, Intervention, KvRole, Species};

/// Where a matched sibling's intervention is applied. The same four sites the committed
/// predecessor declared, restated here so the streamed path depends on no superseded site.
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

impl Site {
    /// The first layer whose faces this site can move. An intervention never reaches its own past
    /// (the predecessor's twelfth falsifier), so every earlier layer is the base's.
    pub fn first_layer(self) -> usize {
        match self {
            Site::Nowhere | Site::EveryLayer => 0,
            Site::Layer(l) => l,
            Site::Final => tower::LAYERS,
        }
    }
}

/// **One tower the cohort conducts.** The base and the replay are towers with no intervention; a
/// matched sibling is a tower whose intervention is applied at its site alone.
#[derive(Clone, Debug)]
pub struct TowerDeclaration {
    pub name: String,
    pub site: Site,
    pub intervention: Intervention,
    /// The first layer this tower conducts. `shares_prefix` false forces it to 0: a control tower
    /// re-derives the prefix it could have shared, so the two readings can be compared.
    pub enters_at: usize,
    /// Whether this tower's faces before `enters_at` are the base's (true) or its own (false).
    pub shares_prefix: bool,
}

impl TowerDeclaration {
    pub fn sharing(name: &str, site: Site, intervention: Intervention) -> Self {
        Self {
            name: name.to_owned(),
            site,
            intervention,
            enters_at: site.first_layer(),
            shares_prefix: true,
        }
    }
    /// A tower that shares nothing: the committed predecessor's mechanism, conducted here as the
    /// control for the shared-prefix claim.
    pub fn whole(name: &str, site: Site, intervention: Intervention) -> Self {
        Self {
            name: name.to_owned(),
            site,
            intervention,
            enters_at: 0,
            shares_prefix: false,
        }
    }
}

/// One layer's faces and testimony under one tower — exactly the three faces the committed
/// receiver family reads per layer, plus what the deed itself testified.
#[derive(Clone)]
pub struct LayerFace {
    pub layer: usize,
    pub species: Species,
    pub role: KvRole,
    /// every operation of the layer's complex, in chronology: its name and whether its testimony is
    /// wholly the caller's intervention
    pub operations: Vec<(String, bool)>,
    pub fronts: usize,
    pub graph_nodes: usize,
    pub graph_edges: usize,
    pub seals_fused: usize,
    pub seals_refused: Vec<(EventId, String)>,
    pub lineage_empty: bool,
    pub a_priori_held: bool,
    pub deed: ExactWork,
    /// the layer scalar's own enclosure, before the terminal quotient (`LAYER_ENCLOSURE`)
    pub terminal: Vec<(i64, i64)>,
    /// the contact section under the chart's seal
    pub contact: Vec<(i64, i64)>,
    /// the per-layer input section after the join
    pub ple: Vec<(i64, i64)>,
}

/// What one tower returned. `layers` holds only the layers this tower conducted; every earlier
/// layer's face is the base's, by construction, and the driver says so.
pub struct TowerReturn {
    pub declaration: TowerDeclaration,
    pub layers: BTreeMap<usize, LayerFace>,
    pub final_operations: Vec<(String, bool)>,
    pub final_normed: Vec<(i64, i64)>,
    pub potential: Vec<(i64, i64)>,
    pub final_fronts: usize,
    pub final_graph_nodes: usize,
    pub final_lineage_empty: bool,
    pub final_a_priori_held: bool,
    pub work: ExactWork,
    pub launches: u64,
    pub obstructions: Vec<(usize, String)>,
}

impl TowerReturn {
    pub fn stood(&self) -> bool {
        self.obstructions.is_empty()
            && self
                .layers
                .values()
                .all(|l| l.lineage_empty && l.a_priori_held)
            && self.final_lineage_empty
            && self.final_a_priori_held
    }
}

/// The reuse the §5.4 ledger actually admitted: one instantiated executable relaunched on the
/// identical material, with both readings kept so the equality is measured rather than asserted.
pub struct ReuseReceipt {
    pub label: String,
    pub instantiation: usize,
    pub first_potential: Vec<(i64, i64)>,
    pub second_potential: Vec<(i64, i64)>,
    pub first_final_normed: Vec<(i64, i64)>,
    pub second_final_normed: Vec<(i64, i64)>,
}

/// The complete address of one standing released by the base tower and shared read-only with a
/// sibling.  `resident_ranges` is apparatus testimony; occurrence identity is the base tower's
/// released output port together with the population and layer which own it.  Neither field may be
/// replaced by a row number, cohort label or content digest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SharedStandingOccurrence {
    pub owner_tower: usize,
    pub released_after_layer: usize,
    pub population: String,
    pub output: OccurrencePort,
    pub resident_ranges: [(u64, u64); 2],
    pub rows: usize,
    pub width: usize,
    pub bound: u32,
}

/// One leg of the actual pullback: a released base standing is presented by a named occurrence in
/// the sibling complex while the same resident section remains its material owner.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrefixPullbackLeg {
    pub standing: SharedStandingOccurrence,
    pub sibling_entry: OccurrencePort,
}

/// One actual pullback of a sibling suffix over base standing.  A receipt is emitted only after
/// every leg passed `Rc::ptr_eq` at the instant the suffix entered.  It therefore testifies to
/// identity of the shared resident object, not equality of two later readings.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrefixPullbackReceipt {
    pub tower: usize,
    pub enters_at: usize,
    pub legs: Vec<PrefixPullbackLeg>,
}

/// An exact apparatus-pressure cut inserted before one tower was realized.  Previously launched
/// passages were terminally joined and released, then the same already-compiled deed was admitted
/// against the changed partition.  No ceiling or semantic aperture was enlarged.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PressurePartitionReceipt {
    pub layer: usize,
    pub before_tower: usize,
    pub coordinate: String,
    pub required: String,
    pub former_ceiling: String,
}

/// The whole cohort's return.
pub struct Cohorted {
    /// Authenticated rested/foreign material occurrence.  This is lineage for the circulation and
    /// never a transport-family classifier.
    pub source_identity: String,
    pub tokens: Vec<usize>,
    pub towers: Vec<TowerReturn>,
    pub bands: Vec<(usize, usize)>,
    /// Per band: the surface census as the band opened and as it closed, so *"nothing was read
    /// inside a band"* is a measurement and not a promise.
    pub band_census: Vec<(usize, TransferCensus, TransferCensus)>,
    pub streamed: StreamedCensus,
    pub census_before: TransferCensus,
    pub census_after: TransferCensus,
    pub instantiations: KeyedInstantiations,
    /// The same offers, keyed as H4 founded the key (nothing addressed) and keyed with the carried
    /// standings alone. The difference between the three hit counts IS the omission's measurement.
    pub instantiations_as_h4: KeyedInstantiations,
    pub instantiations_standings: KeyedInstantiations,
    pub reuse: Option<ReuseReceipt>,
    /// Exact resident objects over which shared suffixes pull back.
    pub prefix_pullbacks: Vec<PrefixPullbackReceipt>,
    pub pressure_partitions: Vec<PressurePartitionReceipt>,
    /// The base's stored K/V standings read at the band boundary BEFORE any sibling could reach
    /// them, and again after every sibling had conducted: the read-only share, measured.
    pub shared_before: BTreeMap<String, Vec<(i64, i64)>>,
    pub shared_after: BTreeMap<String, Vec<(i64, i64)>>,
    pub peak_charged_octets: u64,
    pub admission: MaterialAdmission,
    pub deed_launches: u64,
    /// Passages actually bound — one graph instantiation each, built by this run.
    pub passages_bound: u64,
    /// What the §5.4 ledger, offered the same keys, would have instantiated.
    pub graph_instantiations: u64,
    pub wall_s: f64,
    pub loop_wall_s: f64,
    /// the layer at which the shared-standing snapshot was taken
    pub snapshot_layer: usize,
}

/// One obstruction, said whole.
pub fn describe(obstruction: &FrontPassageObstruction) -> String {
    super::streamed::describe(obstruction)
}

/// Every occurrence of the complex in chronology: its law's name, and whether it is wholly the
/// caller's intervention — decided by its TYPED testimony, never by its name.
pub fn names_of(complex: &crate::ported_operation::PortedOperationComplex) -> Vec<(String, bool)> {
    complex
        .shape
        .occurrences
        .values()
        .map(|o| {
            let name = complex
                .shape
                .laws
                .get(&o.law)
                .map(|l| l.name.clone())
                .unwrap_or_default();
            let typed = complex.operations.get(&o.law).is_some_and(|op| {
                !op.testimony.is_empty()
                    && op.testimony.iter().all(|t| {
                        matches!(
                            t,
                            crate::ported_operation::SourceTestimony::Intervention { .. }
                        )
                    })
            });
            (name, typed)
        })
        .collect()
}

/// One launched deed, held until its band's terminal synchronization.
struct Pending {
    tower: usize,
    layer: Option<usize>,
    label: String,
    bound: CompiledPassage<'static>,
    census: TransferCensus,
    returns: BTreeMap<&'static str, EventId>,
    operations: Vec<(String, bool)>,
    species: Option<Species>,
    role: Option<KvRole>,
    graph_nodes: usize,
    graph_edges: usize,
    seals_fused: usize,
    seals_refused: Vec<(EventId, String)>,
}

/// One tower's live standings while the circulation runs.
#[derive(Default)]
struct Live {
    carried: Option<AddressedStanding>,
    shared: BTreeMap<&'static str, AddressedStanding>,
    entered: bool,
    launches: u64,
    work: ExactWork,
}

#[derive(Clone)]
struct AddressedStanding {
    section: Rc<ResidentSection<'static>>,
    address: SharedStandingOccurrence,
}

impl AddressedStanding {
    fn found(
        section: ResidentSection<'static>,
        bound: u32,
        owner_tower: usize,
        released_after_layer: usize,
        population: impl Into<String>,
        output: OccurrencePort,
    ) -> Self {
        let section = Rc::new(section);
        let address = SharedStandingOccurrence {
            owner_tower,
            released_after_layer,
            population: population.into(),
            output,
            resident_ranges: section.ranges(),
            rows: section.rows(),
            width: section.width(),
            bound,
        };
        Self { section, address }
    }

    fn material(&self) -> (Rc<ResidentSection<'static>>, u32) {
        (Rc::clone(&self.section), self.address.bound)
    }
}

/// **How much of a deed's addressed material the key carries.** Three levels, offered to three
/// ledgers in the same run, because the omission is only visible as a difference between them.
///
/// * `AsH4Founded` — the fields H4 founded: mode, source, topology, ports, grain, terms,
///   reductions, receiver boundary. Nothing addressed.
/// * `Standings` — those plus the carried standings a sibling enters on.
/// * `Whole` — those plus the MOUNTED MAPS. A pooled slot is refilled between segments, so two
///   deeds at the same slot address read different weights; without the population names in the
///   key, two different LAYERS of the same species are one key.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Residency {
    AsH4Founded,
    Standings,
    Whole,
}

/// The §5.4 key of one bound deed, composed from what the deed actually holds.
#[allow(clippy::too_many_arguments)]
fn key_of(
    surface: &ResidentSurface<'_>,
    source_identity: &str,
    bound: &CompiledPassage<'_>,
    material: &ResidentMaterial<'_>,
    tokens: usize,
    grain: ResidentGrain,
    terms: SeriesAperture,
    operations: usize,
    graph_nodes: usize,
    graph_edges: usize,
    receiver_boundary: String,
    residency: Residency,
    chronology: &[(String, bool)],
) -> GraphKey {
    let mut reductions: Vec<(String, u64)> = Vec::new();
    for front in bound.fronts() {
        for coupling in &front.couplings {
            reductions.push((coupling.plan.kernel.to_owned(), coupling.plan.extent));
        }
    }
    let mut addressed: Vec<(String, u64, usize, usize)> = Vec::new();
    if residency >= Residency::Standings {
        addressed.extend(material.standings.iter().map(|(name, (section, _))| {
            (
                name.clone(),
                section.ranges()[0].0,
                section.rows(),
                section.width(),
            )
        }));
    }
    if residency >= Residency::Whole {
        addressed.extend(material.populations.iter().map(|(name, mounted)| {
            (
                name.clone(),
                mounted.readout.aligned_address(),
                mounted.readout.rows(),
                mounted.readout.width(),
            )
        }));
        addressed.extend(material.bands.iter().map(|(name, (bands, raised))| {
            (
                name.clone(),
                bands.resident_address(),
                bands.bands(),
                *raised as usize,
            )
        }));
        addressed.extend(material.arrays.iter().map(|(name, positions)| {
            (
                name.clone(),
                positions.resident_address(),
                positions.rows(),
                0,
            )
        }));
        // The positions are a single unnamed slot on the material, and they are the one addressed
        // thing two matched siblings can differ by while every name in the diagram agrees — the
        // reversed-position sibling and the identity-chronology sibling name their laws identically.
        if let Some(positions) = &material.positions {
            addressed.push((
                "the mounted positions".to_owned(),
                positions.resident_address(),
                positions.rows(),
                0,
            ));
        }
    }
    addressed.sort();
    GraphKey {
        mode: format!("{:?}", surface.mode()),
        source: format!("{}", source_identity),
        topology: vec![(operations, bound.fronts().len(), graph_nodes, graph_edges)],
        ports: vec![
            ("continuing standing".to_owned(), tokens, tower::HIDDEN),
            ("per-layer section".to_owned(), tokens, tower::PLE_WIDTH),
            ("gated passage chart".to_owned(), tokens, tower::FFN),
        ],
        grain: grain.0,
        series_terms: terms.0,
        reductions,
        receiver_boundary,
        material: addressed,
        chronology: chronology.iter().map(|(name, _)| name.clone()).collect(),
    }
}

/// **The dissection, as one streamed circulation with shared prefixes and per-layer cohorts.**
///
/// `band` is an apparatus aperture on residency, not a semantic level: every deed of every band is
/// declared before the first launch, so a band boundary decides nothing about what conducts. It
/// exists because the card holds one section per occurrence per pending deed and a cohort of
/// seventeen towers over forty-two layers does not fit at once.
#[allow(clippy::too_many_arguments)]
pub fn circulate_cohort(
    surface: &'static ResidentSurface<'static>,
    _readout: &'static ResidentReadout,
    source: &mut dyn MaterialSource,
    tokens: &[usize],
    grain: ResidentGrain,
    terms: SeriesAperture,
    chart: tower::Chart,
    declarations: &[TowerDeclaration],
    band: usize,
) -> Result<Cohorted, String> {
    let clock = Instant::now();
    let source_identity = source.source_identity();
    let census_before = surface.census();
    let receiver = DeedReceiver::unbounded();
    let scales = tower::algebraic_scales()?;
    let none = Intervention::None;

    // ---------------------------------------------------------------------------------------
    // before the deed: the segments, the admission, the material, the one source occurrence
    // ---------------------------------------------------------------------------------------
    let mut layer_segments = Vec::with_capacity(tower::LAYERS);
    for layer in 0..tower::LAYERS {
        layer_segments.push(layer_segment(source, layer, layer % 2, layer % 3)?);
    }
    let last = final_segment(source, FINAL_SLOT, FINAL_PINNED)?;
    let shapes = slot_shapes(&layer_segments, &last);
    let refills = vec![
        (tower::LAYERS as u64).div_ceil(2),
        (tower::LAYERS as u64) / 2,
        1,
    ];
    // the source's own two band sets, plus the identity band set one sibling replaces its site
    // layer's chronology with — its length is the SITE's species, read off the declaration rather
    // than assumed — and the head permutation array two siblings mount
    let identity_site_species = declarations
        .iter()
        .find(|d| matches!(d.intervention, Intervention::IdentityChronology))
        .and_then(|d| match d.site {
            Site::Layer(l) => Some(Species::of(l)),
            _ => None,
        });
    let mut auxiliaries = vec![
        PooledMaterialAuxiliary::BandElements(tower::SLIDING_HEAD / 2),
        PooledMaterialAuxiliary::BandElements(tower::FULL_HEAD / 2),
        PooledMaterialAuxiliary::Positions(tokens.len()),
        PooledMaterialAuxiliary::Positions(tokens.len()),
    ];
    if let Some(species) = identity_site_species {
        auxiliaries.push(PooledMaterialAuxiliary::BandElements(
            species.head_width() / 2,
        ));
    }
    if declarations.iter().any(|declaration| {
        matches!(
            declaration.intervention,
            Intervention::PermuteReceiverHeads { .. } | Intervention::PermuteCarriedHeads { .. }
        )
    }) {
        auxiliaries.push(PooledMaterialAuxiliary::Positions(tower::HEADS));
    }
    let passage_zero = FrontPassage::new(surface, grain);
    let prediction = passage_zero.predict_pooled_material(&shapes, &refills, &auxiliaries);
    let admission = passage_zero
        .admit_material(&prediction)
        .map_err(|o| format!("the cohort's pooled material refused: {}", describe(&o)))?;

    let identity_before = source.source_identity();

    let pinned = vec![
        shapes[0].stored_octets,
        shapes[0].stored_octets,
        shapes[0].stored_octets,
        shapes[2].stored_octets,
    ];
    let mut circulation =
        StreamedCirculation::open(surface, &shapes, &pinned).map_err(|e| e.to_string())?;

    // The material, held for the WHOLE circulation and shared by every tower of every cohort.
    let mut material = ResidentMaterial::empty();
    let sliding_bands = tower::found_bands(Species::Sliding, tower::BAND_TERMS)?;
    let full_bands = tower::found_bands(Species::Full, tower::BAND_TERMS)?;
    material.bands.insert(
        tower::SLIDING_BANDS.to_owned(),
        (
            surface
                .mount_bands(&sliding_bands, tower::BAND_GRAIN)
                .map_err(|e| e.to_string())?,
            (tokens.len() - 1) as u32,
        ),
    );
    material.bands.insert(
        tower::FULL_BANDS.to_owned(),
        (
            surface
                .mount_bands(&full_bands, tower::BAND_GRAIN)
                .map_err(|e| e.to_string())?,
            (tokens.len() - 1) as u32,
        ),
    );
    // The identity chronology's own material. Its sibling's site is one SLIDING layer, so one
    // identity band set is mounted; a site on a full layer would need the other and the material
    // plan would have to say so, which is why the length is taken from the site rather than assumed.
    if let Some(species) = identity_site_species {
        let pairs = match species {
            Species::Sliding => sliding_bands.len(),
            Species::Full => full_bands.len(),
        };
        let identity = tower::identity_bands(pairs);
        material.bands.insert(
            tower::IDENTITY_BANDS.to_owned(),
            (
                surface
                    .mount_bands(&identity, tower::BAND_GRAIN)
                    .map_err(|e| e.to_string())?,
                (tokens.len() - 1) as u32,
            ),
        );
    }
    let forward: Vec<u32> = (0..tokens.len() as u32).collect();
    let backward: Vec<u32> = (0..tokens.len() as u32).rev().collect();
    material.positions = Some(
        surface
            .mount_positions(&forward)
            .map_err(|e| e.to_string())?,
    );
    // Held, never dropped: a launched graph names this address and the circulation has not
    // synchronized. The reversed positions are swapped IN for one sibling's one deed and swapped
    // back out; nothing is ever freed while a graph still reads it.
    let mut spare_positions: Option<Positions<'static>> = Some(
        surface
            .mount_positions(&backward)
            .map_err(|e| e.to_string())?,
    );
    if declarations.iter().any(|d| {
        matches!(
            d.intervention,
            Intervention::PermuteReceiverHeads { .. } | Intervention::PermuteCarriedHeads { .. }
        )
    }) {
        let permutation: Vec<u32> = tower::swap_permutation(tower::HEADS, 0, 1)
            .into_iter()
            .map(|i| i as u32)
            .collect();
        material.arrays.insert(
            tower::HEAD_PERMUTATION.to_owned(),
            surface
                .mount_positions(&permutation)
                .map_err(|e| e.to_string())?,
        );
    }

    // the runtime-supplied entering rows, read ONCE for the whole cohort
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
    material.entering.insert(
        tower::ENTERING.to_owned(),
        EnteringRows {
            words: entering,
            rows: tokens.len(),
            width: tower::HIDDEN,
        },
    );

    let mut layer_scalars = Vec::with_capacity(tower::LAYERS);
    for segment in &layer_segments {
        let region = segment
            .scalar
            .as_ref()
            .ok_or("the layer segment carries no layer scalar")?;
        layer_scalars.push(
            Dyadic::of_bfloat16_bits(super::streamed::scalar_word_of(source.file()?, region)?)
                .map_err(|e| e.to_string())?,
        );
    }

    // ---------------------------------------------------------------------------------------
    // the cohort
    // ---------------------------------------------------------------------------------------
    let loop_clock = Instant::now();
    let mut live: Vec<Live> = declarations.iter().map(|_| Live::default()).collect();
    let mut returns: Vec<TowerReturn> = declarations
        .iter()
        .map(|d| TowerReturn {
            declaration: d.clone(),
            layers: BTreeMap::new(),
            final_operations: Vec::new(),
            final_normed: Vec::new(),
            potential: Vec::new(),
            final_fronts: 0,
            final_graph_nodes: 0,
            final_lineage_empty: false,
            final_a_priori_held: false,
            work: ExactWork::nothing(),
            launches: 0,
            obstructions: Vec::new(),
        })
        .collect();
    // The base's own released standings, kept per layer: the standing a tower entering at layer L
    // reads is the base's release from layer L-1, shared through `Rc` and written by nobody.
    let mut base_entry: Vec<Option<AddressedStanding>> = vec![None; tower::LAYERS + 1];
    let mut base_shared: BTreeMap<&'static str, AddressedStanding> = BTreeMap::new();
    let mut pending: Vec<Pending> = Vec::new();
    let mut instantiations = KeyedInstantiations::new();
    let mut instantiations_as_h4 = KeyedInstantiations::new();
    let mut instantiations_standings = KeyedInstantiations::new();
    let mut peak_charged_octets = 0u64;
    let mut deed_launches = 0u64;
    let mut band_census: Vec<(usize, TransferCensus, TransferCensus)> = Vec::new();
    let mut bands: Vec<(usize, usize)> = Vec::new();
    let mut shared_before: BTreeMap<String, Vec<(i64, i64)>> = BTreeMap::new();
    let mut shared_after: BTreeMap<String, Vec<(i64, i64)>> = BTreeMap::new();
    let mut prefix_pullbacks = Vec::new();
    let mut pressure_partitions = Vec::new();

    // The snapshot layer: the first layer at which a tower reads the base's STORED K/V standings
    // rather than building its own. The band boundary is put there deliberately, so the base's
    // shared standings can be read once before any sibling could reach them and once after all of
    // them have conducted.
    let snapshot_layer = declarations
        .iter()
        .filter(|d| {
            d.shares_prefix && matches!(d.intervention, Intervention::WithdrawSharedKvFamily { .. })
        })
        .map(|d| d.enters_at)
        .min()
        .unwrap_or(tower::LAYERS);

    let segments = tower::LAYERS + 1;
    let at = |i: usize| -> &Segment {
        if i + 1 < segments {
            &layer_segments[i]
        } else {
            &last
        }
    };
    let mut offsets: Vec<Vec<usize>> = vec![Vec::new(); segments];
    let mut requests: Vec<Vec<crate::embedding_fiber::PooledMount>> = vec![Vec::new(); segments];
    {
        let first = at(0);
        offsets[0] = circulation
            .stage(
                first.pinned,
                source.file()?,
                source.file_octets()?,
                &first.regions,
            )
            .map_err(|e| e.to_string())?;
        requests[0] = circulation
            .cross(first.slot, first.pinned, &offsets[0], &first.regions)
            .map_err(|e| e.to_string())?;
        let second = at(1);
        offsets[1] = circulation
            .stage(
                second.pinned,
                source.file()?,
                source.file_octets()?,
                &second.regions,
            )
            .map_err(|e| e.to_string())?;
    }

    let mut band_open = surface.census();
    let mut band_first = 0usize;
    for layer in 0..tower::LAYERS {
        let segment = &layer_segments[layer];
        let species = Species::of(layer);
        let role = KvRole::of(layer);
        let layer_scalar = layer_scalars[layer];

        // the layer's slice of each token's per-layer embedding row — one host population for the
        // whole cohort at this layer
        let mut per_layer = Vec::with_capacity(tokens.len() * tower::PLE_WIDTH);
        for row in &per_layer_rows {
            let from = layer * tower::PLE_WIDTH;
            if row.len() < from + tower::PLE_WIDTH {
                return Err(format!("{} is {} wide", tower::PLE_EMBED, row.len()));
            }
            per_layer.extend_from_slice(&row[from..from + tower::PLE_WIDTH]);
        }
        material.entering.insert(
            super::site::PLE_ENTERING.to_owned(),
            EnteringRows {
                words: per_layer,
                rows: tokens.len(),
                width: tower::PLE_WIDTH,
            },
        );

        // --- the mouth, ONCE for the whole cohort crossing this layer ---
        let mounted = circulation
            .mount(segment.slot, segment.pinned, &requests[layer])
            .map_err(|e| e.to_string())?;
        material.populations.clear();
        for (name, pooled) in segment.names.iter().zip(mounted) {
            material.populations.insert(
                name.clone(),
                MountedPopulation {
                    readout: pooled.readout,
                    mass_value_octaves: pooled.mass_value_octaves,
                },
            );
        }
        circulation
            .admit_segment(segment.slot)
            .map_err(|e| e.to_string())?;

        for (index, declaration) in declarations.iter().enumerate() {
            if layer < declaration.enters_at {
                continue;
            }
            let applied: &Intervention = match declaration.site {
                Site::Layer(l) if l == layer => &declaration.intervention,
                Site::EveryLayer => &declaration.intervention,
                _ => &none,
            };

            // --- the standings this tower enters on ---
            material.standings.clear();
            let mut entering_over: Option<Vec<AddressedStanding>> = None;
            if !live[index].entered {
                // the moment this tower enters: it takes the BASE's standing at this layer, and
                // the base's stored K/V standings as they were when the base passed this layer.
                live[index].carried = base_entry[layer].clone();
                live[index].shared = base_shared.clone();
                if declaration.shares_prefix && layer > 0 {
                    let mut shared = Vec::new();
                    if let (Some(base), Some(entered)) =
                        (base_entry[layer].as_ref(), live[index].carried.as_ref())
                    {
                        if !Rc::ptr_eq(&base.section, &entered.section) {
                            return Err(format!(
                                "{}: the carried prefix at layer {layer} is a copied resident owner",
                                declaration.name
                            ));
                        }
                        shared.push(base.clone());
                    } else {
                        return Err(format!(
                            "{}: the carried prefix at layer {layer} is absent",
                            declaration.name
                        ));
                    }

                    // Stored K/V standing participates in the pullback only where this receiving
                    // layer actually reads it.  Merely retaining an unused object is co-presence,
                    // not contact.
                    if role == KvRole::Shared {
                        let populations = match species {
                            Species::Sliding => [tower::SHARED_K_SLIDING, tower::SHARED_V_SLIDING],
                            Species::Full => [tower::SHARED_K_FULL, tower::SHARED_V_FULL],
                        };
                        for population in populations {
                            let base = base_shared.get(population).ok_or_else(|| {
                                format!(
                                    "{}: base {population} is absent at shared layer {layer}",
                                    declaration.name
                                )
                            })?;
                            let entered = live[index].shared.get(population).ok_or_else(|| {
                                format!(
                                    "{}: entered {population} is absent at shared layer {layer}",
                                    declaration.name
                                )
                            })?;
                            if !Rc::ptr_eq(&base.section, &entered.section) {
                                return Err(format!(
                                    "{}: {population} at layer {layer} is a copied resident owner",
                                    declaration.name
                                ));
                            }
                            shared.push(base.clone());
                        }
                    }
                    entering_over = Some(shared);
                }
                live[index].entered = true;
            }
            if let Some(standing) = &live[index].carried {
                material
                    .standings
                    .insert(tower::CARRIED_STANDING.to_owned(), standing.material());
            } else if layer != 0 {
                return Err(format!(
                    "{}: no carried standing at layer {layer}",
                    declaration.name
                ));
            }
            if role == KvRole::Shared {
                let (k_name, v_name) = match species {
                    Species::Sliding => (tower::SHARED_K_SLIDING, tower::SHARED_V_SLIDING),
                    Species::Full => (tower::SHARED_K_FULL, tower::SHARED_V_FULL),
                };
                let k = live[index].shared.get(k_name).ok_or_else(|| {
                    format!(
                        "{}: no shared K standing at layer {layer}",
                        declaration.name
                    )
                })?;
                let v = live[index].shared.get(v_name).ok_or_else(|| {
                    format!(
                        "{}: no shared V standing at layer {layer}",
                        declaration.name
                    )
                })?;
                material.standings.insert(k_name.to_owned(), k.material());
                material.standings.insert(v_name.to_owned(), v.material());
            }

            // --- the reversed-position sibling's own material, swapped in and back out ---
            let reversed = matches!(applied, Intervention::ReversedPositions);
            if reversed {
                let spare = spare_positions
                    .take()
                    .ok_or("the reversed positions are already mounted")?;
                spare_positions = material.positions.replace(spare);
            }

            let entry = if layer == 0 {
                Entry::Rows
            } else {
                Entry::Carried
            };
            let mut founded = tower::found_layer(
                layer,
                entry,
                chart,
                &scales,
                terms,
                layer_scalar,
                applied,
                tokens.len(),
                tower::InputSectionReceiver::SourceRows,
            )?;
            if let Some(shared) = entering_over {
                let mut legs = Vec::with_capacity(shared.len());
                for standing in shared {
                    let event = if standing.address.population == tower::CARRIED_STANDING {
                        founded.returns.get(tower::CARRIED_ENTRY)
                    } else {
                        founded.returns.get(standing.address.population.as_str())
                    }
                    .copied()
                    .ok_or_else(|| {
                        format!(
                            "{}: receiving occurrence for {} is absent at layer {layer}",
                            declaration.name, standing.address.population
                        )
                    })?;
                    legs.push(PrefixPullbackLeg {
                        standing: standing.address,
                        sibling_entry: OccurrencePort::output(event, 0),
                    });
                }
                prefix_pullbacks.push(PrefixPullbackReceipt {
                    tower: index,
                    enters_at: layer,
                    legs,
                });
            }
            let operations = names_of(&founded.complex);
            let terminal = founded.returns[tower::LAYER_RETURN];
            // **The receiver's declared faces.** Three per layer, exactly the committed family: the
            // per-layer input section, the contact and the layer's own enclosure before the
            // terminal quotient. The third is a QUOTIENT'S PREDECESSOR, so declaring it refuses
            // that one fusion by name and keeps the pre-quotient enclosure the family reads; the
            // first two are quotients themselves and read through their fused seals.
            let declared: BTreeSet<EventId> = [
                founded.returns[tower::PLE_SECTION],
                founded.returns[tower::CONTACT],
                founded.returns[tower::LAYER_ENCLOSURE],
            ]
            .into_iter()
            .collect();
            let (fusable, refused) =
                factored_seals(&founded.complex, &founded.realization, terminal, &declared);
            for quotient in &fusable {
                founded.realization.bind(*quotient, SealedMidpointQuotient);
            }
            let passage = FrontPassage::new(surface, grain).reading(declared.iter().copied());
            let plan = passage
                .compile(
                    &founded.complex,
                    &founded.realization,
                    &material,
                    source.occurrence(),
                    terminal,
                )
                .map_err(|o| {
                    format!(
                        "{} layer {layer} refused at compile: {}",
                        declaration.name,
                        describe(&o)
                    )
                })?;
            let deed_admission = match passage.admit(&plan, &receiver, Some(&admission)) {
                Ok(admitted) => admitted,
                Err(FrontPassageObstruction::Resource(ResourceObstruction::Apparatus {
                    coordinate,
                })) if coordinate.name == "charged-resident-octets" && !pending.is_empty() => {
                    // Pressure changes the same body's partition.  Join and release the already
                    // launched population, retain the exact cut, then re-ask admission for the
                    // unchanged compiled deed.  This is not a retry under a wider bound.
                    pressure_partitions.push(PressurePartitionReceipt {
                        layer,
                        before_tower: index,
                        coordinate: coordinate.name.to_owned(),
                        required: coordinate.required.to_string(),
                        former_ceiling: match &coordinate.ceiling {
                            crate::front_passage::Ceiling::Bounded { ceiling, .. } => {
                                ceiling.to_string()
                            }
                            crate::front_passage::Ceiling::Unbounded { because, .. } => {
                                format!("unbounded: {because}")
                            }
                        },
                    });
                    circulation.terminal().map_err(|e| e.to_string())?;
                    let band_close = surface.census();
                    band_census.push((band_first, band_open.clone(), band_close));
                    bands.push((band_first, layer));
                    drain(&mut pending, &mut returns)?;
                    band_first = layer;
                    band_open = surface.census();
                    passage
                        .admit(&plan, &receiver, Some(&admission))
                        .map_err(|o| {
                            format!(
                                "{} layer {layer} remained refused after exact pressure partition: {}",
                                declaration.name,
                                describe(&o)
                            )
                        })?
                }
                Err(o) => {
                    return Err(format!(
                        "{} layer {layer} refused at admission: {}",
                        declaration.name,
                        describe(&o)
                    ));
                }
            };
            let mut bound = passage
                .realize(plan, &material, deed_admission)
                .map_err(|o| {
                    format!(
                        "{} layer {layer} refused at realization: {}",
                        declaration.name,
                        describe(&o)
                    )
                })?;
            peak_charged_octets = peak_charged_octets.max(
                admission.prediction.charged_octets + bound.apparatus_prediction.charged_octets,
            );
            let (graph, _) = bound.graph();
            let (graph_nodes, graph_edges) = (graph.nodes, graph.edges);

            let label = format!("{} · layer {layer}", declaration.name);
            let boundary = format!(
                "the layer return, with {} declared faces (per-layer input, contact, layer enclosure)",
                declared.len()
            );
            for (level, ledger) in [
                (Residency::AsH4Founded, &mut instantiations_as_h4),
                (Residency::Standings, &mut instantiations_standings),
                (Residency::Whole, &mut instantiations),
            ] {
                let key = key_of(
                    surface,
                    &identity_before,
                    &bound,
                    &material,
                    tokens.len(),
                    grain,
                    terms,
                    founded.complex.operations.len(),
                    graph_nodes,
                    graph_edges,
                    boundary.clone(),
                    level,
                    &operations,
                );
                let _ = ledger.offer(&label, &key);
            }

            let census_at_launch = bound
                .launch_on(&surface.mode(), circulation.conducting())
                .map_err(|o| {
                    format!(
                        "{} layer {layer} refused at launch: {}",
                        declaration.name,
                        describe(&o)
                    )
                })?;
            circulation
                .conducted(segment.slot)
                .map_err(|e| e.to_string())?;
            deed_launches += 1;
            live[index].launches += 1;
            let carried_work = live[index].work.then(&bound.deed_prediction);
            live[index].work = carried_work;

            if reversed {
                let spare = spare_positions
                    .take()
                    .ok_or("the forward positions are already mounted")?;
                spare_positions = material.positions.replace(spare);
            }

            // The standings the tower's next deeds carry. Releasing moves ownership of a device
            // section out of THIS passage; it reads nothing and writes nothing.
            if role == KvRole::OwnAndStore {
                let (k_name, v_name) = match species {
                    Species::Sliding => (tower::SHARED_K_SLIDING, tower::SHARED_V_SLIDING),
                    Species::Full => (tower::SHARED_K_FULL, tower::SHARED_V_FULL),
                };
                let (k, kb) = bound
                    .release_section(founded.returns[tower::K_STANDING])
                    .ok_or("K standing")?;
                let (v, vb) = bound
                    .release_section(founded.returns[tower::V_STANDING])
                    .ok_or("V standing")?;
                live[index].shared.insert(
                    k_name,
                    AddressedStanding::found(
                        k,
                        kb,
                        index,
                        layer,
                        k_name,
                        OccurrencePort::output(founded.returns[tower::K_STANDING], 0),
                    ),
                );
                live[index].shared.insert(
                    v_name,
                    AddressedStanding::found(
                        v,
                        vb,
                        index,
                        layer,
                        v_name,
                        OccurrencePort::output(founded.returns[tower::V_STANDING], 0),
                    ),
                );
                if index == 0 {
                    base_shared = live[index].shared.clone();
                }
            }
            let (out, ob) = bound.release_section(terminal).ok_or("layer return")?;
            let out = AddressedStanding::found(
                out,
                ob,
                index,
                layer,
                tower::CARRIED_STANDING,
                OccurrencePort::output(terminal, 0),
            );
            live[index].carried = Some(out.clone());
            if index == 0 {
                base_entry[layer + 1] = Some(out);
            }

            let mut named: BTreeMap<&'static str, EventId> = BTreeMap::new();
            for (name, event) in &founded.returns {
                named.insert(name, *event);
            }
            pending.push(Pending {
                tower: index,
                layer: Some(layer),
                label,
                bound,
                census: census_at_launch,
                returns: named,
                operations,
                species: Some(species),
                role: Some(role),
                graph_nodes,
                graph_edges,
                seals_fused: fusable.len(),
                seals_refused: refused,
            });
        }

        // the next segment's copy, issued now so it crosses while THIS cohort conducts, and the one
        // after it staged from the container
        if layer + 1 < segments {
            let next = at(layer + 1);
            requests[layer + 1] = circulation
                .cross(next.slot, next.pinned, &offsets[layer + 1], &next.regions)
                .map_err(|e| e.to_string())?;
        }
        if layer + 2 < segments {
            let after = at(layer + 2);
            offsets[layer + 2] = circulation
                .stage(
                    after.pinned,
                    source.file()?,
                    source.file_octets()?,
                    &after.regions,
                )
                .map_err(|e| e.to_string())?;
        }

        // **The band boundary.** A residency aperture, declared before the first launch: which
        // deeds are in which band is fixed by the panel and the band width, and no reading here
        // decides anything that conducts later.
        let boundary =
            layer + 1 == tower::LAYERS || (layer + 1) % band == 0 || layer + 1 == snapshot_layer;
        if boundary {
            circulation.terminal().map_err(|e| e.to_string())?;
            let band_close = surface.census();
            band_census.push((band_first, band_open.clone(), band_close));
            bands.push((band_first, layer));
            drain(&mut pending, &mut returns)?;
            if layer + 1 == snapshot_layer {
                for (name, standing) in &base_shared {
                    shared_before.insert(
                        (*name).to_owned(),
                        surface
                            .read_out(&standing.section)
                            .map_err(|e| e.to_string())?,
                    );
                }
            }
            band_first = layer + 1;
            band_open = surface.census();
        }
    }

    // ---------------------------------------------------------------------------------------
    // the final boundary: one cohort of its own, on the standing each tower carried out of 41
    // ---------------------------------------------------------------------------------------
    let mounted = circulation
        .mount(last.slot, last.pinned, &requests[segments - 1])
        .map_err(|e| e.to_string())?;
    material.populations.clear();
    for (name, pooled) in last.names.iter().zip(mounted) {
        material.populations.insert(
            name.clone(),
            MountedPopulation {
                readout: pooled.readout,
                mass_value_octaves: pooled.mass_value_octaves,
            },
        );
    }
    circulation
        .admit_segment(last.slot)
        .map_err(|e| e.to_string())?;
    let mut base_final: Option<(BTreeMap<&'static str, EventId>, GraphKey, String)> = None;
    for (index, declaration) in declarations.iter().enumerate() {
        let applied: &Intervention = if declaration.site == Site::Final {
            &declaration.intervention
        } else {
            &none
        };
        if !live[index].entered {
            live[index].carried = base_entry[tower::LAYERS].clone();
            live[index].shared = base_shared.clone();
            let entering_over = if let (Some(base), Some(entered)) = (
                base_entry[tower::LAYERS].as_ref(),
                live[index].carried.as_ref(),
            ) {
                if !Rc::ptr_eq(&base.section, &entered.section) {
                    return Err(format!(
                        "{}: the final carried prefix is a copied resident owner",
                        declaration.name
                    ));
                }
                base.clone()
            } else {
                return Err(format!(
                    "{}: the final carried prefix is absent",
                    declaration.name
                ));
            };
            live[index].entered = true;
            // The exact receiving occurrence is founded below with the final complex.
            live[index].carried = Some(entering_over);
        }
        material.standings.clear();
        let standing = live[index].carried.as_ref().ok_or_else(|| {
            format!(
                "{}: no carried standing at the final boundary",
                declaration.name
            )
        })?;
        material
            .standings
            .insert(tower::CARRIED_STANDING.to_owned(), standing.material());
        let mut founded =
            tower::found_final(chart, applied, &scales, tower::OutputSectionReceiver::Whole)?;
        if declaration.shares_prefix && declaration.enters_at == tower::LAYERS {
            let standing = live[index]
                .carried
                .as_ref()
                .ok_or_else(|| format!("{}: final shared standing is absent", declaration.name))?;
            let entry = founded
                .returns
                .get(tower::CARRIED_ENTRY)
                .copied()
                .ok_or_else(|| {
                    format!("{}: final receiving occurrence is absent", declaration.name)
                })?;
            prefix_pullbacks.push(PrefixPullbackReceipt {
                tower: index,
                enters_at: tower::LAYERS,
                legs: vec![PrefixPullbackLeg {
                    standing: standing.address.clone(),
                    sibling_entry: OccurrencePort::output(entry, 0),
                }],
            });
        }
        let operations = names_of(&founded.complex);
        let terminal = founded.returns[tower::POTENTIAL];
        let declared: BTreeSet<EventId> =
            [founded.returns[tower::FINAL_NORMED]].into_iter().collect();
        let (fusable, refused) =
            factored_seals(&founded.complex, &founded.realization, terminal, &declared);
        for quotient in &fusable {
            founded.realization.bind(*quotient, SealedMidpointQuotient);
        }
        let passage = FrontPassage::new(surface, grain).reading(declared.iter().copied());
        let bound = passage
            .bind(
                &founded.complex,
                &founded.realization,
                &material,
                source.occurrence(),
                &receiver,
                Some(&admission),
                terminal,
            )
            .map_err(|o| {
                format!(
                    "{} refused at the final bind: {}",
                    declaration.name,
                    describe(&o)
                )
            })?;
        peak_charged_octets = peak_charged_octets
            .max(admission.prediction.charged_octets + bound.apparatus_prediction.charged_octets);
        let (graph, _) = bound.graph();
        let (graph_nodes, graph_edges) = (graph.nodes, graph.edges);
        let label = format!("{} · final boundary", declaration.name);
        let boundary = "the potential section, with the final normed standing declared".to_owned();
        for (level, ledger) in [
            (Residency::AsH4Founded, &mut instantiations_as_h4),
            (Residency::Standings, &mut instantiations_standings),
        ] {
            let key = key_of(
                surface,
                &identity_before,
                &bound,
                &material,
                tokens.len(),
                grain,
                terms,
                founded.complex.operations.len(),
                graph_nodes,
                graph_edges,
                boundary.clone(),
                level,
                &operations,
            );
            let _ = ledger.offer(&label, &key);
        }
        let key = key_of(
            surface,
            &identity_before,
            &bound,
            &material,
            tokens.len(),
            grain,
            terms,
            founded.complex.operations.len(),
            graph_nodes,
            graph_edges,
            boundary,
            Residency::Whole,
            &operations,
        );
        let _ = instantiations.offer(&label, &key);
        let census_at_launch = bound
            .launch_on(&surface.mode(), circulation.conducting())
            .map_err(|o| {
                format!(
                    "{} refused at the final launch: {}",
                    declaration.name,
                    describe(&o)
                )
            })?;
        circulation
            .conducted(last.slot)
            .map_err(|e| e.to_string())?;
        deed_launches += 1;
        live[index].launches += 1;
        let carried_work = live[index].work.then(&bound.deed_prediction);
        live[index].work = carried_work;
        let mut named: BTreeMap<&'static str, EventId> = BTreeMap::new();
        for (name, event) in &founded.returns {
            named.insert(name, *event);
        }
        if index == 0 {
            base_final = Some((named.clone(), key, label.clone()));
        }
        pending.push(Pending {
            tower: index,
            layer: None,
            label,
            bound,
            census: census_at_launch,
            returns: named,
            operations,
            species: None,
            role: None,
            graph_nodes,
            graph_edges,
            seals_fused: fusable.len(),
            seals_refused: refused,
        });
    }
    let (base_named, base_key, base_label) =
        base_final.ok_or("the base tower declared no final boundary")?;
    let base_index = 0usize;
    circulation.terminal().map_err(|e| e.to_string())?;
    let census_after_final = surface.census();
    band_census.push((band_first, band_open, census_after_final));
    bands.push((band_first, tower::LAYERS));
    let base_bound = drain_keeping(&mut pending, &mut returns, base_index)?;

    // ---------------------------------------------------------------------------------------
    // the one lawful reuse: the base's final executable, relaunched on the IDENTICAL material
    // ---------------------------------------------------------------------------------------
    let mut reuse = None;
    if let Some(bound) = base_bound {
        let first_potential = returns[base_index].potential.clone();
        let first_final_normed = returns[base_index].final_normed.clone();
        match instantiations.offer(&format!("{base_label} · relaunched"), &base_key) {
            Instantiation::Reused { index, .. } => {
                let census_at_launch =
                    bound
                        .launch_on(&surface.mode(), circulation.conducting())
                        .map_err(|o| format!("the reuse relaunch refused: {}", describe(&o)))?;
                circulation
                    .conducted(last.slot)
                    .map_err(|e| e.to_string())?;
                deed_launches += 1;
                circulation.terminal().map_err(|e| e.to_string())?;
                let returned = bound
                    .returned(census_at_launch)
                    .map_err(|o| format!("the relaunched deed did not return: {}", describe(&o)))?;
                let second_final_normed = bound
                    .read_section(&returned, base_named[tower::FINAL_NORMED])
                    .map_err(|o| describe(&o))?;
                let second_potential = bound.read_terminal(&returned).map_err(|o| describe(&o))?;
                reuse = Some(ReuseReceipt {
                    label: base_label,
                    instantiation: index,
                    first_potential,
                    second_potential,
                    first_final_normed,
                    second_final_normed,
                });
            }
            Instantiation::New { nearest, .. } => {
                return Err(format!(
                    "the base's own final executable was refused a reuse of itself on identical material: {:?}",
                    nearest
                ));
            }
        }
    }

    // the base's shared standings, read again after every sibling has conducted
    for (name, standing) in &base_shared {
        shared_after.insert(
            (*name).to_owned(),
            surface
                .read_out(&standing.section)
                .map_err(|e| e.to_string())?,
        );
    }

    source
        .verify_stable()
        .map_err(|e| format!("the container moved under the circulation: {e}"))?;
    if source.source_identity() != identity_before {
        return Err("the container's identity moved under the circulation".to_owned());
    }

    for (index, tower_return) in returns.iter_mut().enumerate() {
        tower_return.work = live[index].work.clone();
        tower_return.launches = live[index].launches;
    }
    let loop_wall_s = loop_clock.elapsed().as_secs_f64();
    let streamed = circulation.census().clone();
    let census_after = surface.census();
    let graph_instantiations = instantiations.instantiations() as u64;
    let passages_bound = deed_launches - u64::from(reuse.is_some());
    circulation.close();
    drop(material);
    drop(spare_positions);
    Ok(Cohorted {
        source_identity,
        tokens: tokens.to_vec(),
        towers: returns,
        bands,
        band_census,
        streamed,
        census_before,
        census_after,
        instantiations,
        instantiations_as_h4,
        instantiations_standings,
        reuse,
        prefix_pullbacks,
        pressure_partitions,
        shared_before,
        shared_after,
        peak_charged_octets,
        admission,
        deed_launches,
        passages_bound,
        graph_instantiations,
        wall_s: clock.elapsed().as_secs_f64(),
        loop_wall_s,
        snapshot_layer,
    })
}

/// Read every pending deed's faces after the band's terminal synchronization, and drop it.
fn drain(pending: &mut Vec<Pending>, returns: &mut [TowerReturn]) -> Result<(), String> {
    for deed in pending.drain(..) {
        read_into(&deed, returns)?;
    }
    Ok(())
}

/// The same, keeping one tower's final deed alive so its executable can be relaunched.
fn drain_keeping(
    pending: &mut Vec<Pending>,
    returns: &mut [TowerReturn],
    keep: usize,
) -> Result<Option<CompiledPassage<'static>>, String> {
    let mut kept = None;
    for deed in pending.drain(..) {
        read_into(&deed, returns)?;
        if deed.tower == keep && deed.layer.is_none() {
            kept = Some(deed.bound);
        }
    }
    Ok(kept)
}

fn read_into(deed: &Pending, returns: &mut [TowerReturn]) -> Result<(), String> {
    let returned = deed
        .bound
        .returned(deed.census.clone())
        .map_err(|o| format!("{} did not return: {}", deed.label, describe(&o)))?;
    let stands = returned.stands();
    let a_priori = returned.measured_octaves.iter().all(|(port, measured)| {
        deed.bound.octave_field.get(port).copied().unwrap_or(0) >= *measured
    });
    if let Err(obstruction) = deed.bound.standing(&returned) {
        returns[deed.tower].obstructions.push((
            deed.layer.unwrap_or(usize::MAX),
            format!("{}: {}", deed.label, describe(&obstruction)),
        ));
        return Ok(());
    }
    match deed.layer {
        Some(layer) => {
            let terminal = deed
                .bound
                .read_section(&returned, deed.returns[tower::LAYER_ENCLOSURE])
                .map_err(|o| format!("{}: {}", deed.label, describe(&o)))?;
            let contact = deed
                .bound
                .read_section(&returned, deed.returns[tower::CONTACT])
                .map_err(|o| format!("{}: {}", deed.label, describe(&o)))?;
            let ple = deed
                .bound
                .read_section(&returned, deed.returns[tower::PLE_SECTION])
                .map_err(|o| format!("{}: {}", deed.label, describe(&o)))?;
            returns[deed.tower].layers.insert(
                layer,
                LayerFace {
                    layer,
                    species: deed.species.unwrap_or(Species::Sliding),
                    role: deed.role.unwrap_or(KvRole::Own),
                    operations: deed.operations.clone(),
                    fronts: deed.bound.fronts().len(),
                    graph_nodes: deed.graph_nodes,
                    graph_edges: deed.graph_edges,
                    seals_fused: deed.seals_fused,
                    seals_refused: deed.seals_refused.clone(),
                    lineage_empty: stands,
                    a_priori_held: a_priori,
                    deed: deed.bound.deed_prediction.clone(),
                    terminal,
                    contact,
                    ple,
                },
            );
        }
        None => {
            let final_normed = deed
                .bound
                .read_section(&returned, deed.returns[tower::FINAL_NORMED])
                .map_err(|o| format!("{}: {}", deed.label, describe(&o)))?;
            let potential = deed
                .bound
                .read_terminal(&returned)
                .map_err(|o| format!("{}: {}", deed.label, describe(&o)))?;
            returns[deed.tower].final_normed = final_normed;
            returns[deed.tower].potential = potential;
            returns[deed.tower].final_operations = deed.operations.clone();
            returns[deed.tower].final_fronts = deed.bound.fronts().len();
            returns[deed.tower].final_graph_nodes = deed.graph_nodes;
            returns[deed.tower].final_lineage_empty = stands;
            returns[deed.tower].final_a_priori_held = a_priori;
        }
    }
    Ok(())
}
