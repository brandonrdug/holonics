//! **Pooled source standing, refilled from an exterior container while the card conducts.**
//!
//! # What was absent, and why it is not one of the standing owners
//!
//! Composition was attempted before this module was written, and it is worth recording what each
//! standing owner does and does not carry, because the gap is narrow:
//!
//! * [`crate::front_passage`] owns prediction, admission, the diagram's fronts, the graph and the
//!   deed. It has no notion of a standing that outlives one deed and is *rewritten* for the next.
//! * [`crate::resident_section`] owns sections, band elements, positions, staged codewords and the
//!   passage. Every one of them is allocated per deed and released with it; `StagedWords::refill`
//!   is the closest relation and it is a **synchronous** refill of one entering population of a
//!   fixed extent, not a slot reused by populations of different extents across many deeds.
//! * [`crate::embedding_fiber`] owns the BF16 mouth. Until H4 it allocated the standing it mounted
//!   into, so the mount and the residency were one act and neither could be reused.
//! * `mount` owns streams, events, graphs and device buffers, and now page-locked host standing.
//!
//! **The absent relation is the pool: one device standing, admitted once, whose content is
//! replaced between deeds by a copy the card itself orders.** Everything else here follows from
//! it — the pinned staging exists because a copy engine will not read pageable memory without
//! staging it through a bounce buffer, and the double buffering exists because the content that is
//! being replaced must not be the content a launched graph is still reading.
//!
//! # The measured occasion
//!
//! H0 profiled the committed tower: 43 graph launches carrying 1.36 s of card work inside a 13.3 s
//! kernel span, with **296 ms of apparatus between consecutive graphs** — a per-region SHA-256 of
//! every octet read, 2,112 `cuCtxSynchronize` calls (one per mount kernel), 9,416 allocate/free
//! pairs, and 9.29 GB of transfers of which **0 ns overlapped any kernel**. None of that is the
//! law; all of it is how the material arrived.
//!
//! # What this owner does not do
//!
//! It carries no semantics. It reads no section, holds no receiver, and names no operation. The
//! ordering it declares is between *arrivals of material* and *the deeds that read it*, which is
//! an apparatus relation; which deed runs, and what it computes, is the caller's diagram and the
//! front passage's admission. A [`StreamedCirculation`] has no field from which a section, a
//! census face or a terminal can be reached, so *"the apparatus made no semantic choice between
//! segments"* is a property of the type rather than a promise of the loop.

use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::os::unix::fs::FileExt;

use mount::{DeviceBuffer, Event, PinnedHost, Stream};
use serde::Serialize;
use thiserror::Error;

use crate::embedding_fiber::{PooledMount, PooledReadout};
use crate::resident_section::{ResidentRefusal, ResidentSurface};

/// **Every way the streamed standing refuses.** None of them is answered by conducting anyway.
#[derive(Debug, Error)]
pub enum StreamedRefusal {
    #[error("the apparatus refused: {0}")]
    Surface(#[from] ResidentRefusal),
    #[error("the apparatus refused: {0}")]
    Apparatus(#[from] mount::CudaError),
    #[error("the mouth refused: {0}")]
    Mouth(String),
    #[error("slot {slot} carries {capacity} octets and the segment declared {required}")]
    SlotTooNarrow {
        slot: usize,
        capacity: usize,
        required: usize,
    },
    #[error("there is no slot {slot}; the pool was opened with {slots}")]
    NoSuchSlot { slot: usize, slots: usize },
    #[error(
        "region {population} reads {octets} octets at {start} of a container of {container} octets"
    )]
    RegionOutsideContainer {
        population: String,
        start: u64,
        octets: usize,
        container: u64,
    },
    #[error("reading {population} from the container returned {reason}")]
    Unreadable { population: String, reason: String },
    #[error("{what}")]
    Declaration { what: String },
}

/// **One pool slot's declared shape**, predicted from the container's header before any octet is
/// read: the aligned standing the mouth writes, the stored codewords that cross into it, the row
/// masses its reductions write, and the mouth's scratch words.
///
/// Every extent is in octets and every one of them is admitted before the slot is opened.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SlotShape {
    pub name: String,
    /// `words × 8` — the exact aligned form of every map the slot will carry at once.
    pub aligned_octets: usize,
    /// `words × 2` — the stored codewords of the same maps.
    pub stored_octets: usize,
    /// `rows × 16` summed over the maps — the row-mass low/high pairs.
    pub mass_octets: usize,
    /// `16 × maps` — the mouth's four reduction words per map.
    pub scratch_octets: usize,
}

impl SlotShape {
    pub fn octets(&self) -> usize {
        self.aligned_octets + self.stored_octets + self.mass_octets + self.scratch_octets
    }
}

/// One opened slot: a single device allocation, sub-divided at declared offsets. The subdivision
/// is arithmetic on one base address, so the slot costs **one** allocation however many maps it
/// carries — which is the whole of what replaces 9,416 allocate/free pairs.
pub struct StandingSlot {
    shape: SlotShape,
    buffer: DeviceBuffer<u8>,
    /// The event recorded on the conducting stream after the last deed that read this slot. A
    /// refill waits on it; nothing else does.
    freed: Event,
    /// Whether a deed has ever been conducted from this slot, so the first refill waits on nothing.
    conducted: bool,
    stored_cursor: usize,
    aligned_cursor: usize,
    mass_cursor: usize,
    maps: usize,
}

impl StandingSlot {
    pub fn shape(&self) -> &SlotShape {
        &self.shape
    }
    fn base(&self) -> u64 {
        self.buffer.device_ptr()
    }
    fn stored_base(&self) -> u64 {
        self.base()
    }
    fn aligned_base(&self) -> u64 {
        self.base() + self.shape.stored_octets as u64
    }
    fn mass_base(&self) -> u64 {
        self.aligned_base() + self.shape.aligned_octets as u64
    }
    fn scratch_base(&self) -> u64 {
        self.mass_base() + self.shape.mass_octets as u64
    }
    /// Forget every sub-allocation; the next segment lays its own maps out from the base.
    fn rewind(&mut self) {
        self.stored_cursor = 0;
        self.aligned_cursor = 0;
        self.mass_cursor = 0;
        self.maps = 0;
    }
}

/// **One region of the exterior container a segment stages**: where it lives in the container, and
/// the shape it will be mounted at. The identity of the region is the container's header; nothing
/// here re-derives it and nothing here digests it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StagedRegion {
    pub population: String,
    /// The region's first octet in the container, as its header declares.
    pub start: u64,
    /// How many BF16 codewords the region carries.
    pub words: u32,
    /// The declared last-axis width; `words / dim` is the row population.
    pub dim: usize,
}

impl StagedRegion {
    pub fn octets(&self) -> usize {
        self.words as usize * 2
    }
    pub fn rows(&self) -> usize {
        if self.dim == 0 {
            0
        } else {
            self.words as usize / self.dim
        }
    }
}

/// **The census of the streamed path**, beside the surface's own. Every field is a count of an
/// apparatus act; none of them decides anything.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize)]
pub struct StreamedCensus {
    /// Page-locked host standing held at once.
    pub pinned_octets: u64,
    /// Device standing held by the pool at once, and how many allocations bought it.
    pub pool_octets: u64,
    pub pool_allocations: u64,
    /// Segments: one declared exterior I/O boundary each.
    pub segments: u64,
    /// Regions read out of the container into pinned standing, and their octets.
    pub staged_regions: u64,
    pub staged_octets: u64,
    /// Host→device copies issued on the copy current, and their octets. Every one is asynchronous.
    pub asynchronous_copies: u64,
    pub asynchronous_copy_octets: u64,
    /// Mouth kernels recorded on the mount current, and the synchronizations the mouth's own host
    /// round trip costs — **two per segment**, not two per map.
    pub mount_launches: u64,
    pub mount_synchronizations: u64,
    /// Synchronizations of the copy current, taken before a pinned slot is rewritten.
    pub staging_synchronizations: u64,
    /// Graph executables launched onto the conducting current without waiting for them.
    pub graph_launches: u64,
    /// Synchronizations of the conducting current. The deed's terminal.
    pub terminal_synchronizations: u64,
}

/// **The identity a bound graph executable is bound UNDER** — the plan's §5.4 key, founded so a
/// later deed can state what it would be reusing, and **unexercised here**: this deed conducts one
/// input closure, no cache exists, and no hit is claimed. A key is apparatus reuse testimony and
/// never semantic identity; two deeds with equal keys are two deeds, and the receipt says so.
///
/// # What a second input of the same extent would actually need, measured on what stands
///
/// In the pooled realization the weight addresses are **fixed by the pool**, and the entering
/// codewords are refilled through `CompiledPassage::refill` into the same staged buffer at the same
/// address. So a second input of the same token extent needs **no graph update at all** — the
/// executable's every pointer is already the one it will read. The key's whole role there is to
/// certify that the mode, the source, the topology, the port extents, the grain and the receiver
/// boundary are the ones the executable was instantiated for.
///
/// An input of a **different** extent moves the section shapes, hence the kernel parameters, and
/// that is where the two routes divide: `cuGraphExecKernelNodeSetParams` updates an instantiated
/// executable's node in place, or the passage is re-instantiated. **Neither is exercised and the
/// first is not bound** — `soma/mount/src/ffi.rs` carries no `cuGraphExecKernelNodeSetParams`,
/// measured 2026-08-19 by `grep -c cuGraphExec soma/mount/src/ffi.rs` → 1, which is
/// `cuGraphExecDestroy`. Deed H5's cohort conduction is where a second extent
/// enters.
///
/// # The residency the key omitted, found by Deed H5
///
/// H4 founded this key over the mode, the source, the topology, the port extents, the grain and
/// the receiver boundary — every field a *diagram* has. It carried nothing about **where the
/// deed's carried standings live**, because H4 conducts one tower and every standing in it is
/// produced and consumed by the same circulation. A cohort is the first caller for which that is
/// false: sixteen matched siblings conduct the same layer diagram, at the same extents, under the
/// same mode and source, over **different carried standings** — different device sections, whose
/// addresses the executable's kernel parameters baked in at capture. Under H4's fields alone those
/// deeds' keys are equal, so a cache keyed on them would relaunch one sibling's executable for
/// another and the second sibling would read the first's standing. [`GraphKey::material`] is that
/// missing field, and [`GraphKey::reuse_refused`] is the comparison that names which field stopped
/// a reuse rather than merely reporting that two keys differ.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphKey {
    /// The surface's complete mode identity, said whole: source law, ABI, kernel, device,
    /// arithmetic, apparatus, and the kernel content digest.
    pub mode: String,
    /// The container the source occurrence authenticated: its locator-free identity, its header
    /// digest and its whole-content digest where one was taken.
    pub source: String,
    /// The diagram as it was bound: occurrences, fronts, graph nodes and graph edges per segment.
    /// Plural, not a digest — a topology that differs is meant to be readable, not merely unequal.
    ///
    /// **These are COUNTS, and Deed H5 measured what a count cannot separate.** Two matched
    /// siblings whose interventions each insert exactly one occurrence at different sites carry the
    /// same four numbers at every segment. [`GraphKey::chronology`] is the diagram itself.
    pub topology: Vec<(usize, usize, usize, usize)>,
    /// **Every occurrence's law name, in the chronology the passage bound them in.** The diagram,
    /// not its census. Empty means the caller declared none, which is a statement about the caller.
    pub chronology: Vec<String>,
    /// The declared port extents this executable's kernels were sized for: `(name, rows, width)`.
    pub ports: Vec<(String, usize, usize)>,
    /// The carrier grain `2^-F` and the series aperture.
    pub grain: u32,
    pub series_terms: u32,
    /// The reductions the deed named, verbatim rather than digested: `(kernel, extent)` per
    /// coupling. A collapsed digest would say two keys differ; this says where.
    pub reductions: Vec<(String, u64)>,
    /// The receiver's boundary: the declared terminal and every face it said it would read.
    pub receiver_boundary: String,
    /// **The residency the executable's kernel parameters baked in**: every carried standing and
    /// mounted map the deed reads by address, as `(name, device address, rows, width)`. Two deeds
    /// whose every other field agrees but whose material sits elsewhere are **not** the same
    /// executable, and the whole content of this field is that a reuse hit on the rest would read
    /// the wrong section. Empty means the caller declared no addressed material — which is a
    /// statement about the caller, not a licence.
    pub material: Vec<(String, u64, usize, usize)>,
}

impl GraphKey {
    /// One line, for a receipt. Every field verbatim; nothing is hashed here.
    pub fn stated(&self) -> String {
        format!(
            "mode {} · source {} · grain 2^-{} · terms {} · segments {} · occurrences {} · ports {} · reductions {} · material {} · receiver {}",
            self.mode,
            self.source,
            self.grain,
            self.series_terms,
            self.topology.len(),
            self.chronology.len(),
            self.ports.len(),
            self.reductions.len(),
            self.material.len(),
            self.receiver_boundary
        )
    }

    /// **Why an executable bound under `self` may not be relaunched for a deed keyed `other`** —
    /// the first field that differs, said in words. `None` when every field agrees, which is the
    /// only condition under which relaunching an instantiated executable returns the deed the
    /// caller asked for.
    ///
    /// The order is the order in which a difference is *cheap to see*, and `material` is checked
    /// last because it is the one H4's key did not carry: a caller reading this receipt sees
    /// immediately whether two deeds were separated by their diagram or only by where their
    /// standings live.
    pub fn reuse_refused(&self, other: &GraphKey) -> Option<String> {
        if self.mode != other.mode {
            return Some(format!(
                "the mode differs: {} against {}",
                self.mode, other.mode
            ));
        }
        if self.source != other.source {
            return Some("the authenticated source container differs".to_owned());
        }
        if self.grain != other.grain || self.series_terms != other.series_terms {
            return Some(format!(
                "the carrier differs: grain 2^-{} terms {} against grain 2^-{} terms {}",
                self.grain, self.series_terms, other.grain, other.series_terms
            ));
        }
        if self.ports != other.ports {
            return Some(
                "the declared port extents differ, so the kernels were sized for other sections"
                    .to_owned(),
            );
        }
        if self.chronology != other.chronology {
            let mine: BTreeSet<&str> = self.chronology.iter().map(String::as_str).collect();
            let theirs: BTreeSet<&str> = other.chronology.iter().map(String::as_str).collect();
            let only_mine: Vec<&&str> = mine.difference(&theirs).collect();
            let only_theirs: Vec<&&str> = theirs.difference(&mine).collect();
            // The difference is a MULTISET difference, not a positional one: inserting one
            // occurrence early shifts every later name, and reporting 68 of 68 for a
            // one-occurrence intervention would be a count standing in for the object.
            let mut mine_counted: BTreeMap<&str, usize> = BTreeMap::new();
            for name in &self.chronology {
                *mine_counted.entry(name.as_str()).or_default() += 1;
            }
            let mut theirs_counted: BTreeMap<&str, usize> = BTreeMap::new();
            for name in &other.chronology {
                *theirs_counted.entry(name.as_str()).or_default() += 1;
            }
            let differing: usize = mine_counted
                .keys()
                .chain(theirs_counted.keys())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .map(|name| {
                    mine_counted
                        .get(name)
                        .copied()
                        .unwrap_or(0)
                        .abs_diff(theirs_counted.get(name).copied().unwrap_or(0))
                })
                .sum();
            return Some(format!(
                "the diagram's chronology differs by {differing} occurrence(s) of {}; only in the instantiated one {only_mine:?}, only in the offered one {only_theirs:?}",
                self.chronology.len()
            ));
        }
        if self.topology != other.topology {
            return Some(format!(
                "the diagram's census differs: {:?} against {:?} (occurrences, fronts, graph nodes, graph edges)",
                self.topology, other.topology
            ));
        }
        if self.reductions != other.reductions {
            return Some("the named reductions differ".to_owned());
        }
        if self.receiver_boundary != other.receiver_boundary {
            return Some("the receiver declared a different boundary, so a different population of seals factored".to_owned());
        }
        if self.material != other.material {
            let mine: Vec<&str> = self
                .material
                .iter()
                .map(|(n, _, _, _)| n.as_str())
                .collect();
            let theirs: Vec<&str> = other
                .material
                .iter()
                .map(|(n, _, _, _)| n.as_str())
                .collect();
            if mine != theirs {
                return Some(format!(
                    "the addressed material differs by name: {mine:?} against {theirs:?}"
                ));
            }
            let moved: Vec<String> = self
                .material
                .iter()
                .zip(&other.material)
                .filter(|((_, a, _, _), (_, b, _, _))| a != b)
                .map(|((n, a, _, _), (_, b, _, _))| format!("{n} at {a:#x} against {b:#x}"))
                .collect();
            return Some(format!(
                "every field of the diagram agrees and the RESIDENCY differs — {} of {} addressed sections moved: {}",
                moved.len(),
                self.material.len(),
                moved.join("; ")
            ));
        }
        None
    }
}

/// **Instantiations counted against launches, with every refusal named.**
///
/// A caller binding many deeds offers each one's key here before instantiating. An offer that
/// matches a stored key is a [`Instantiation::Reused`] — the caller may relaunch that executable —
/// and every other offer is a [`Instantiation::New`] carrying, where one exists, the nearest
/// stored key and the sentence saying what stopped the reuse. Nothing here launches anything, and
/// nothing here decides a semantics: it is the apparatus ledger §5.4 asks a cohort to keep.
#[derive(Debug, Default)]
pub struct KeyedInstantiations {
    keys: Vec<(String, GraphKey)>,
    /// Every offer that did not match, with the offered label, the nearest stored key's label and
    /// the sentence naming the field that stopped it.
    pub refusals: Vec<(String, String, String)>,
    /// Every offer that DID match, with the offered label and the instantiated one's. A hit is a
    /// claim that two deeds are one executable, so it is kept by name and never as a count alone.
    pub hits_named: Vec<(String, String)>,
    pub offers: u64,
    pub hits: u64,
}

/// What an offer returned: an executable to relaunch, or a new instantiation with the nearest
/// stored key and why it did not serve.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Instantiation {
    Reused {
        index: usize,
        label: String,
    },
    New {
        index: usize,
        nearest: Option<(String, String)>,
    },
}

impl KeyedInstantiations {
    pub fn new() -> Self {
        Self::default()
    }

    /// The stored keys, in instantiation order.
    pub fn instantiations(&self) -> usize {
        self.keys.len()
    }

    /// **Offer one deed's key.** `label` names the deed for the receipt; it takes no part in the
    /// comparison, so two deeds cannot be separated by their names.
    pub fn offer(&mut self, label: &str, key: &GraphKey) -> Instantiation {
        self.offers += 1;
        if let Some((index, (stored_label, _))) = self
            .keys
            .iter()
            .enumerate()
            .find(|(_, (_, stored))| stored.reuse_refused(key).is_none())
        {
            self.hits += 1;
            self.hits_named
                .push((label.to_owned(), stored_label.clone()));
            return Instantiation::Reused {
                index,
                label: stored_label.clone(),
            };
        }
        // The nearest stored key: the last one whose refusal is the residency alone, else the last
        // stored key at all. "Nearest" is a reading aid and never a licence.
        let nearest = self
            .keys
            .iter()
            .rev()
            .find_map(|(stored_label, stored)| {
                stored
                    .reuse_refused(key)
                    .filter(|because| because.starts_with("every field of the diagram agrees"))
                    .map(|because| (stored_label.clone(), because))
            })
            .or_else(|| {
                self.keys.last().and_then(|(stored_label, stored)| {
                    stored
                        .reuse_refused(key)
                        .map(|because| (stored_label.clone(), because))
                })
            });
        if let Some((stored_label, because)) = &nearest {
            self.refusals
                .push((label.to_owned(), stored_label.clone(), because.clone()));
        }
        self.keys.push((label.to_owned(), key.clone()));
        Instantiation::New {
            index: self.keys.len() - 1,
            nearest,
        }
    }

    /// How many refusals were the residency alone — every field of the diagram agreeing while the
    /// addressed sections differ. This is the population H4's key could not have separated.
    pub fn residency_only_refusals(&self) -> usize {
        self.refusals
            .iter()
            .filter(|(_, _, because)| because.starts_with("every field of the diagram agrees"))
            .count()
    }
}

/// **The circulation**: the pool, the pinned staging, the three currents and the events that order
/// them.
///
/// It owns no reader. There is no accessor here that returns a section, a coordinate, a census
/// slot or a terminal, and the type carries no passage, so between two segments the apparatus
/// **cannot** inspect a semantic value — not by discipline but by construction. The caller holds
/// its own deeds and reads them after [`StreamedCirculation::terminal`].
pub struct StreamedCirculation<'chart> {
    surface: &'chart ResidentSurface<'chart>,
    /// The conducting current: every deed's graph, in order, no synchronization between them.
    conducting: Stream,
    /// The copy current: host→device refills, so a refill can cross while a deed conducts.
    copying: Stream,
    /// The mount current: the mouth's kernels over a refilled slot.
    mounting: Stream,
    slots: Vec<StandingSlot>,
    pinned: Vec<PinnedHost>,
    /// Per pinned slot, the event recorded after the copy that last read it.
    crossed: Vec<Event>,
    crossed_once: Vec<bool>,
    /// The event recorded after the last mount, which a deed waits on.
    mounted: Event,
    census: StreamedCensus,
}

impl<'chart> StreamedCirculation<'chart> {
    /// **Open the pool and the staging.** Every slot is one allocation and every pinned slot one
    /// page-locked host allocation; the caller has already admitted them. Nothing is read and
    /// nothing crosses here.
    pub fn open(
        surface: &'chart ResidentSurface<'chart>,
        shapes: &[SlotShape],
        pinned_octets: &[usize],
    ) -> Result<Self, StreamedRefusal> {
        let mut slots = Vec::with_capacity(shapes.len());
        let mut census = StreamedCensus::default();
        for shape in shapes {
            let buffer = surface.alloc_octets(shape.octets())?;
            census.pool_octets += shape.octets() as u64;
            census.pool_allocations += 1;
            slots.push(StandingSlot {
                shape: shape.clone(),
                buffer,
                freed: Event::create()?,
                conducted: false,
                stored_cursor: 0,
                aligned_cursor: 0,
                mass_cursor: 0,
                maps: 0,
            });
        }
        let mut pinned = Vec::with_capacity(pinned_octets.len());
        let mut crossed = Vec::with_capacity(pinned_octets.len());
        for octets in pinned_octets {
            pinned.push(PinnedHost::alloc(*octets)?);
            crossed.push(Event::create()?);
            census.pinned_octets += *octets as u64;
        }
        Ok(Self {
            surface,
            conducting: Stream::create()?,
            copying: Stream::create()?,
            mounting: Stream::create()?,
            slots,
            pinned,
            crossed_once: vec![false; pinned_octets.len()],
            crossed,
            mounted: Event::create()?,
            census,
        })
    }

    pub fn census(&self) -> &StreamedCensus {
        &self.census
    }
    pub fn slots(&self) -> usize {
        self.slots.len()
    }
    pub fn slot_shape(&self, slot: usize) -> Option<&SlotShape> {
        self.slots.get(slot).map(StandingSlot::shape)
    }
    /// The conducting current, for a caller launching its own graph onto it.
    pub fn conducting(&self) -> &Stream {
        &self.conducting
    }

    /// **Stage a segment's regions out of the exterior container into a pinned slot.**
    ///
    /// This is the declared exterior I/O boundary, and it is the only place in the circulation
    /// where the apparatus touches the exterior. The pinned slot is not rewritten until the copy
    /// that last read it has completed — that is one synchronization of the copy current, counted,
    /// and it is a wait on an *apparatus transfer*, never on a deed.
    ///
    /// Returns each region's offset in the pinned slot, in the order given.
    pub fn stage(
        &mut self,
        pinned_slot: usize,
        file: &File,
        container_octets: u64,
        regions: &[StagedRegion],
    ) -> Result<Vec<usize>, StreamedRefusal> {
        let slot = self
            .pinned
            .get(pinned_slot)
            .ok_or(StreamedRefusal::NoSuchSlot {
                slot: pinned_slot,
                slots: self.pinned.len(),
            })?;
        let required: usize = regions.iter().map(StagedRegion::octets).sum();
        if required > slot.octets() {
            return Err(StreamedRefusal::SlotTooNarrow {
                slot: pinned_slot,
                capacity: slot.octets(),
                required,
            });
        }
        // Wait on the copy that last read THIS slot, and on nothing else: synchronizing the copy
        // current would also wait for the copy that is meant to be crossing while a deed conducts,
        // which is how an overlap reads 0 ns while every stream is asynchronous.
        if self.crossed_once[pinned_slot] {
            self.crossed[pinned_slot].synchronize()?;
            self.census.staging_synchronizations += 1;
        }
        let mut offsets = Vec::with_capacity(regions.len());
        let mut at = 0usize;
        // SAFETY: the copy that last read this slot has completed (the synchronization above), and
        // no copy has been issued against it since.
        let octets = unsafe { self.pinned[pinned_slot].as_octets_unchecked() };
        for region in regions {
            let span = region.octets();
            if region.start + span as u64 > container_octets {
                return Err(StreamedRefusal::RegionOutsideContainer {
                    population: region.population.clone(),
                    start: region.start,
                    octets: span,
                    container: container_octets,
                });
            }
            file.read_exact_at(&mut octets[at..at + span], region.start)
                .map_err(|error| StreamedRefusal::Unreadable {
                    population: region.population.clone(),
                    reason: error.to_string(),
                })?;
            offsets.push(at);
            at += span;
            self.census.staged_regions += 1;
            self.census.staged_octets += span as u64;
        }
        Ok(offsets)
    }

    /// **Cross a staged segment into a pool slot, asynchronously, on the copy current.**
    ///
    /// The copy is ordered after the event recorded when the last deed that read this slot was
    /// launched — so the double buffering is a *device* dependency and the apparatus does not wait
    /// for it. It returns the per-map addresses the mouth will read and write, laid out from the
    /// slot's own base.
    pub fn cross(
        &mut self,
        slot: usize,
        pinned_slot: usize,
        offsets: &[usize],
        regions: &[StagedRegion],
    ) -> Result<Vec<PooledMount>, StreamedRefusal> {
        if slot >= self.slots.len() {
            return Err(StreamedRefusal::NoSuchSlot {
                slot,
                slots: self.slots.len(),
            });
        }
        if offsets.len() != regions.len() {
            return Err(StreamedRefusal::Declaration {
                what: format!(
                    "{} staged offsets for {} regions",
                    offsets.len(),
                    regions.len()
                ),
            });
        }
        self.slots[slot].rewind();
        let (stored_base, aligned_base, mass_base) = {
            let s = &self.slots[slot];
            (s.stored_base(), s.aligned_base(), s.mass_base())
        };
        if self.slots[slot].conducted {
            let freed = &self.slots[slot].freed;
            self.copying.wait_event(freed)?;
        }
        let mut requests = Vec::with_capacity(regions.len());
        for (region, offset) in regions.iter().zip(offsets) {
            let stored_span = region.octets();
            let aligned_span = region.words as usize * 8;
            let mass_span = region.rows() * 16;
            let (stored_at, aligned_at, mass_at) = {
                let s = &self.slots[slot];
                (s.stored_cursor, s.aligned_cursor, s.mass_cursor)
            };
            {
                let shape = self.slots[slot].shape.clone();
                if stored_at + stored_span > shape.stored_octets {
                    return Err(StreamedRefusal::SlotTooNarrow {
                        slot,
                        capacity: shape.stored_octets,
                        required: stored_at + stored_span,
                    });
                }
                if aligned_at + aligned_span > shape.aligned_octets {
                    return Err(StreamedRefusal::SlotTooNarrow {
                        slot,
                        capacity: shape.aligned_octets,
                        required: aligned_at + aligned_span,
                    });
                }
                if mass_at + mass_span > shape.mass_octets {
                    return Err(StreamedRefusal::SlotTooNarrow {
                        slot,
                        capacity: shape.mass_octets,
                        required: mass_at + mass_span,
                    });
                }
            }
            // SAFETY: the source is page-locked host standing owned here; the copy current waits
            // on the event that freed this slot, and the pinned slot is not rewritten until this
            // copy has completed (`stage` synchronizes the copy current first).
            unsafe {
                let source = self.pinned[pinned_slot]
                    .as_ptr()
                    .cast::<u8>()
                    .add(*offset)
                    .cast();
                self.copying.copy_host_to_device_async(
                    stored_base + stored_at as u64,
                    source,
                    stored_span,
                )?;
            }
            self.census.asynchronous_copies += 1;
            self.census.asynchronous_copy_octets += stored_span as u64;
            requests.push(PooledMount {
                stored: stored_base + stored_at as u64,
                aligned: aligned_base + aligned_at as u64,
                mass: mass_base + mass_at as u64,
                count: region.words,
                rows: region.rows(),
                dim: region.dim,
            });
            let s = &mut self.slots[slot];
            s.stored_cursor += stored_span;
            s.aligned_cursor += aligned_span;
            s.mass_cursor += mass_span;
            s.maps += 1;
        }
        self.crossed[pinned_slot].record(&self.copying)?;
        self.crossed_once[pinned_slot] = true;
        Ok(requests)
    }

    /// **Mount a whole segment's maps at once on the mount current**, after the copy that brought
    /// them. Two synchronizations of the mount current — the mouth's exponent reduction is a host
    /// round trip and cannot be otherwise — against `3 × maps` in the per-map path.
    ///
    /// The conducting current is untouched: whatever deed is running keeps running.
    pub fn mount(
        &mut self,
        slot: usize,
        pinned_slot: usize,
        requests: &[PooledMount],
    ) -> Result<Vec<PooledReadout<'chart>>, StreamedRefusal> {
        if slot >= self.slots.len() {
            return Err(StreamedRefusal::NoSuchSlot {
                slot,
                slots: self.slots.len(),
            });
        }
        let required = 16 * requests.len();
        if required > self.slots[slot].shape.scratch_octets {
            return Err(StreamedRefusal::SlotTooNarrow {
                slot,
                capacity: self.slots[slot].shape.scratch_octets,
                required,
            });
        }
        self.mounting.wait_event(&self.crossed[pinned_slot])?;
        let scratch = self.slots[slot].scratch_base();
        // SAFETY: the mount current is a live stream of this surface's context, and every address
        // in `requests` names this slot, which the copy current has just filled and which no other
        // current writes.
        let mounted = unsafe {
            self.surface
                .readout()
                .mount_bfloat16_pooled(self.mounting.raw(), scratch, requests)
        }
        .map_err(|error| StreamedRefusal::Mouth(format!("{error:?}")))?;
        self.census.mount_launches +=
            (2 * requests.len() + requests.iter().filter(|r| r.rows > 0).count()) as u64;
        self.census.mount_synchronizations += 2;
        self.mounted.record(&self.mounting)?;
        Ok(mounted)
    }

    /// **Order the conducting current after the segment's mount, and record that the slot is in
    /// use.** A caller launches its deed onto [`StreamedCirculation::conducting`] between this call
    /// and [`StreamedCirculation::conducted`].
    pub fn admit_segment(&mut self, slot: usize) -> Result<(), StreamedRefusal> {
        if slot >= self.slots.len() {
            return Err(StreamedRefusal::NoSuchSlot {
                slot,
                slots: self.slots.len(),
            });
        }
        self.conducting.wait_event(&self.mounted)?;
        self.census.segments += 1;
        Ok(())
    }

    /// **Record that the deed reading this slot has been launched.** The event is what a later
    /// refill of the same slot waits on, and it is recorded on the conducting current *after* the
    /// launch, so the refill cannot overtake the deed.
    pub fn conducted(&mut self, slot: usize) -> Result<(), StreamedRefusal> {
        if slot >= self.slots.len() {
            return Err(StreamedRefusal::NoSuchSlot {
                slot,
                slots: self.slots.len(),
            });
        }
        self.slots[slot].freed.record(&self.conducting)?;
        self.slots[slot].conducted = true;
        self.census.graph_launches += 1;
        Ok(())
    }

    /// **The terminal synchronization.** One wait, at the end, for the whole circulation. Only
    /// after this may a caller read any deed's census or any section: before it, every returned
    /// word is the word of a deed that has not finished.
    pub fn terminal(&mut self) -> Result<(), StreamedRefusal> {
        self.surface.synchronize_counted(&self.conducting)?;
        self.copying.synchronize()?;
        self.mounting.synchronize()?;
        self.census.terminal_synchronizations += 1;
        self.census.staging_synchronizations += 2;
        Ok(())
    }

    /// Release the pool's octets from the surface's resident census. The buffers free themselves.
    pub fn close(self) {
        let octets: u64 = self.slots.iter().map(|s| s.shape.octets() as u64).sum();
        self.surface.released_octets(octets);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_slot_shape_sums_its_four_regions() {
        let shape = SlotShape {
            name: "one".to_owned(),
            aligned_octets: 800,
            stored_octets: 200,
            mass_octets: 32,
            scratch_octets: 16,
        };
        assert_eq!(shape.octets(), 1048);
    }

    #[test]
    fn a_staged_region_reports_its_octets_and_rows_from_the_header_alone() {
        let region = StagedRegion {
            population: "m".to_owned(),
            start: 64,
            words: 2560 * 8,
            dim: 2560,
        };
        assert_eq!(region.octets(), 2560 * 8 * 2);
        assert_eq!(region.rows(), 8);
        // A rank-0 region has no width; it is a word, and the row population is empty rather than
        // a division by zero.
        let scalar = StagedRegion {
            population: "s".to_owned(),
            start: 0,
            words: 1,
            dim: 0,
        };
        assert_eq!(scalar.rows(), 0);
    }

    /// The key is stated verbatim and nothing in it is collapsed to a scalar: a receipt that says
    /// two executables differ must say WHERE.
    #[test]
    fn a_graph_key_states_every_field_it_carries_and_hashes_none_of_them() {
        let key = GraphKey {
            mode: "exact-integer-interval-v2/exact_resident_section".to_owned(),
            source: "identity+header".to_owned(),
            topology: vec![(69, 45, 106, 113)],
            ports: vec![("continuing standing, 2560".to_owned(), 5, 2560)],
            grain: 48,
            series_terms: 14,
            reductions: vec![("section_rms_rebase".to_owned(), 2560)],
            receiver_boundary: "terminal EventId(0)".to_owned(),
            material: vec![("carried standing".to_owned(), 0x7f00_0000, 5, 2560)],
            chronology: vec!["entering standing".to_owned(), "input rebase".to_owned()],
        };
        let stated = key.stated();
        assert!(stated.contains("grain 2^-48"), "{stated}");
        assert!(stated.contains("terms 14"), "{stated}");
        assert!(stated.contains("segments 1"), "{stated}");
        assert!(stated.contains("material 1"), "{stated}");
        assert!(stated.contains("occurrences 2"), "{stated}");
        assert_eq!(
            key.clone(),
            key,
            "the key is a value, compared field by field"
        );
    }

    fn cohort_key(standing: u64) -> GraphKey {
        GraphKey {
            mode: "exact-integer-interval-v2/exact_resident_section".to_owned(),
            source: "identity+header".to_owned(),
            topology: vec![(69, 45, 106, 113)],
            ports: vec![("continuing standing, 2560".to_owned(), 5, 2560)],
            grain: 48,
            series_terms: 14,
            reductions: vec![("section_rms_rebase".to_owned(), 2560)],
            receiver_boundary: "terminal EventId(0)".to_owned(),
            material: vec![("carried standing".to_owned(), standing, 5, 2560)],
            chronology: vec![
                "entering standing".to_owned(),
                "input rebase".to_owned(),
                "contact and carried construction".to_owned(),
            ],
        }
    }

    /// **The cohort's decisive key reading.** Two matched siblings conduct the same layer diagram
    /// at the same extents under the same mode and source; only their carried standings sit at
    /// different addresses. Under H4's fields alone the two keys are equal, so a cache keyed on
    /// them would relaunch one sibling's executable for the other and the second would read the
    /// first's standing. The residency field is what refuses it, and the refusal says so in words.
    #[test]
    fn a_cohort_sibling_may_not_reuse_a_sibling_executable_whose_standing_sits_elsewhere() {
        let first = cohort_key(0x7f00_0000);
        let second = cohort_key(0x7f10_0000);
        let because = first
            .reuse_refused(&second)
            .expect("the residency differs, so the reuse is refused");
        assert!(
            because.starts_with("every field of the diagram agrees"),
            "{because}"
        );
        assert!(because.contains("carried standing"), "{because}");
        assert!(
            because.contains("0x7f000000") && because.contains("0x7f100000"),
            "{because}"
        );
        // and the diagram itself is identical: nothing but the residency separates them
        let mut stripped = second.clone();
        stripped.material = first.material.clone();
        assert_eq!(
            first.reuse_refused(&stripped),
            None,
            "with one residency the two deeds are one executable"
        );
    }

    /// A key difference in the diagram is named as such, and never confused with a residency move.
    #[test]
    fn a_cohort_key_names_which_field_stopped_the_reuse() {
        let base = cohort_key(0x7f00_0000);
        let mut intervened = base.clone();
        intervened.topology = vec![(71, 45, 108, 116)];
        let because = base
            .reuse_refused(&intervened)
            .expect("the diagram differs");
        assert!(
            because.starts_with("the diagram's census differs"),
            "{because}"
        );
        // **What a count cannot separate, and the chronology can.** Two matched siblings whose
        // interventions each insert exactly ONE occurrence, at different sites, carry the same four
        // numbers — measured on the real cohort, where keying on the census admitted 697 of 714
        // offers as reuses. The chronology names the occurrence and refuses.
        let mut left = base.clone();
        left.chronology
            .push("per-layer input withdrawn (intervention)".to_owned());
        left.topology = vec![(70, 45, 109, 116)];
        let mut right = base.clone();
        right
            .chronology
            .push("gated passage span withdrawn (intervention)".to_owned());
        right.topology = vec![(70, 45, 109, 116)];
        assert_eq!(
            left.topology, right.topology,
            "one inserted occurrence each: the census cannot tell them apart"
        );
        let because = left.reuse_refused(&right).expect("the chronology differs");
        assert!(
            because.starts_with("the diagram's chronology differs by 2 occurrence(s)"),
            "{because}"
        );
        assert!(
            because.contains("per-layer input withdrawn")
                && because.contains("gated passage span withdrawn"),
            "{because}"
        );
        let mut coarser = base.clone();
        coarser.grain = 24;
        assert!(
            base.reuse_refused(&coarser)
                .is_some_and(|b| b.starts_with("the carrier differs"))
        );
        let mut other_extent = base.clone();
        other_extent.ports = vec![("continuing standing, 2560".to_owned(), 7, 2560)];
        assert!(
            base.reuse_refused(&other_extent)
                .is_some_and(|b| b.starts_with("the declared port extents differ"))
        );
    }

    /// The ledger counts instantiations against offers and keeps every refusal by name — including
    /// the population H4's key could not have separated.
    #[test]
    fn the_cohort_instantiation_ledger_counts_hits_and_keeps_every_refusal() {
        let mut ledger = KeyedInstantiations::new();
        let first = ledger.offer("base layer 24", &cohort_key(0x7f00_0000));
        assert!(matches!(
            first,
            Instantiation::New {
                index: 0,
                nearest: None
            }
        ));
        let sibling = ledger.offer("sibling layer 24", &cohort_key(0x7f10_0000));
        match sibling {
            Instantiation::New {
                index,
                nearest: Some((label, because)),
            } => {
                assert_eq!(index, 1);
                assert_eq!(label, "base layer 24");
                assert!(
                    because.starts_with("every field of the diagram agrees"),
                    "{because}"
                );
            }
            other => panic!("a sibling on another standing is a new instantiation: {other:?}"),
        }
        // the same deed offered again on the same material is one executable relaunched
        let again = ledger.offer("base layer 24 relaunched", &cohort_key(0x7f00_0000));
        assert!(
            matches!(again, Instantiation::Reused { index: 0, .. }),
            "{again:?}"
        );
        assert_eq!(ledger.instantiations(), 2);
        assert_eq!(ledger.offers, 3);
        assert_eq!(ledger.hits, 1);
        assert_eq!(ledger.residency_only_refusals(), 1);
    }

    #[test]
    fn the_streamed_census_starts_empty_and_every_field_is_a_count() {
        let census = StreamedCensus::default();
        assert_eq!(census.segments, 0);
        assert_eq!(census.graph_launches, 0);
        assert_eq!(census.terminal_synchronizations, 0);
        assert_eq!(census.mount_synchronizations, 0);
    }
}
