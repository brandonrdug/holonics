//! The material hands over its own incidence atlas.
//!
//! `soma/life/src/incidence_production.rs` founds `L_t = (K_t, ∂_t, o_t, ⪯_t, Γ_t)` from
//! [`DeclaredOccurrence`]s whose only structure is an **inscription patch sequence**. Every
//! material — Lean, Rust, arithmetic, prose — therefore enters through one byte chart and conducts
//! by adjacency. The ratified law
//! `research/records/2026-07-19_THE_INCIDENCE_REACTS_THE_COMPOUND_EXPOSES_ITS_BOUNDARY_THE_REGION_CARRIES_THE_FIELD.md`
//! §I is explicit that this is not what the source owes:
//!
//! > *"The source therefore owes more than a sequence of relation words and less than an authored
//! > meaning. It supplies a bounded oriented incidence atlas."*
//!
//! and §III is equally explicit that a byte chart is **lawful** and may not **counterfeit** the
//! others: *"The first chart cannot counterfeit the others."* Lean, Rust and arithmetic each carry
//! their own oriented incidence; nothing had handed it over.
//!
//! # What this module is
//!
//! A [`MaterialAtlas`] — the source-native `L_t` — and one **intake seam** that serializes it into
//! the vocabulary [`IncidenceComplex::found`] already accepts, without editing that owner and
//! without founding a second complex beside it.
//!
//! | law term | supplied by |
//! |---|---|
//! | `K_t` | [`MaterialAtlas::constituents`] — declarations, items, expression nodes, patches |
//! | `∂_t` | [`MaterialAtlas::contacts`], each with its [`ContactSpecies`] and its **owner** |
//! | `o_t` | the contact's direction, plus [`ContactSpecies::OperandOrder`], which is a hand written as a cell |
//! | `⪯_t` | [`MaterialAtlas::heights`] — the material's own dependency height, SCC-collapsed. **Never a line number, never a slice position**, both of which are carried beside it as `storage_ordinal` so the two can be exhibited apart. |
//! | `Γ_t` | left to the complex, which reads ingress and exposed boundary off in/out degree |
//!
//! # The seam, stated exactly, because it is the part that could lie
//!
//! One [`DeclaredOccurrence`] per contact, `text = "<from> <to>"`, at `patch_extent = 2`. The
//! occurrence's causal rank must come out as the **owner's** dependency rank, and
//! `incidence_production`'s `causal_ranks` derives rank by longest path over `caused_by`. So each
//! occurrence at rank `r > 0` names **one canonical occurrence of rank `r − 1`** as its cause. The
//! rank that results is the material's; the representative is a **gauge**, and
//! [`MaterialAtlas::rank_gauge_orbit`] takes its orbit — least-identity against greatest-identity —
//! and requires every rank to be unmoved. A representative that changed a rank would mean the
//! intake was reading its own bookkeeping.
//!
//! Ranks are **densified**: the sorted distinct owner heights are re-indexed to `0..n`. That is a
//! rebase — order-preserving, invertible, zero remainder (`H.0104`) — and it is required because
//! longest path over a chain cannot skip a rank.
//!
//! [`MaterialAtlas::faithfulness`] then reads the founded complex back and requires every declared
//! contact to be present as a bond between the expected surfaces at the expected rank. That is the
//! anti-orthography guard: without it, this module would be a way of writing prose that happens to
//! spell a structure.
//!
//! # The contact face crosses; the reaction class does not
//!
//! [`ContactSpecies`] is retained on `incidence_production::Bond` as a [`DeclaredContactFace`]. It
//! is exterior lineage and decides nothing in that owner. A later receiver/history quotient may
//! find that faces with different names conduct alike or that equal names separate. This closes the
//! prior erasure without turning the source atlas into an authored internal chemistry.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_rational::BigRational;

use crate::incidence_production::{
    DeclaredContactFace, DeclaredOccurrence, IncidenceComplex, IncidenceProductionError, PhaseChart,
};

/// The exact rational carrier. No float enters this module at any point.
pub type Rat = BigRational;

// ---------------------------------------------------------------------------------------------
// The atlas
// ---------------------------------------------------------------------------------------------

/// Which material supplied the atlas. It is provenance and it decides nothing.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum MaterialKind {
    /// Lean declarations and the declarations they recruit.
    Lean,
    /// Rust items and the items they name.
    Rust,
    /// Expression nodes and their operands.
    Arithmetic,
    /// Inscription patches and their byte-serialization adjacency — the tape chart, carried as a
    /// declared control so the other three have something to be different from.
    Prose,
}

impl MaterialKind {
    pub const fn name(self) -> &'static str {
        match self {
            Self::Lean => "lean",
            Self::Rust => "rust",
            Self::Arithmetic => "arithmetic",
            Self::Prose => "prose",
        }
    }
}

/// What kind of relation one contact is. §IV: these name **transport relations**, not labels
/// attached to isolated payloads.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ContactSpecies {
    /// Lean: a declaration named another declaration in **term** position — what it is about.
    Recruits,
    /// Lean: a declaration named another in **tactic** position — how it was conducted. Returned
    /// beside the terms and never merged into them.
    Conducts,
    /// Rust: an item named another item.
    Calls,
    /// Arithmetic: a node's operand.
    Operand,
    /// Arithmetic: left before right on a **non-commutative** node. This is `o_t` written as a
    /// cell: a commutative node has quotiented its own hand away and emits no such contact, so
    /// `2 − 3` closes a boundary and `2 + 2` does not.
    OperandOrder,
    /// Prose: byte-serialization adjacency. §III's lawful first chart.
    Adjacency,
}

impl ContactSpecies {
    pub const fn name(self) -> &'static str {
        match self {
            Self::Recruits => "recruits",
            Self::Conducts => "conducts",
            Self::Calls => "calls",
            Self::Operand => "operand",
            Self::OperandOrder => "operand-order",
            Self::Adjacency => "adjacency",
        }
    }
}

/// One oriented contact of the material's own incidence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StructuralContact {
    pub from: usize,
    pub to: usize,
    /// The constituent whose structure this contact belongs to. For a recruitment or a call that
    /// is the source; for an operand-order contact it is the **parent node**, because the hand is
    /// a fact about the node and not about its left operand. The owner fixes the contact's rank,
    /// which is what keeps a node's whole star at one rank and therefore able to close.
    pub owner: usize,
    pub species: ContactSpecies,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MaterialIncidenceError {
    /// A constituent name carries whitespace, so the two-patch intake could not address it.
    ConstituentCarriesWhitespace(String),
    EmptyConstituent,
    /// The declared material founded no contact at all.
    NoContact,
    Extent,
    /// `incidence_production` refused the serialized atlas.
    Complex(IncidenceProductionError),
    Arithmetic(ArithmeticError),
}

/// Which occurrence carries the rank chain. A **gauge**: the ranks must not move under it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RankRepresentative {
    Least,
    Greatest,
}

/// The counted work of one intake. Never a clock (`CLAUDE.md` §8).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct IntakeWork {
    pub constituents: u64,
    pub contacts: u64,
    pub occurrences: u64,
    pub caused_by_edges: u64,
    /// Distinct dependency ranks after densification.
    pub ranks: u64,
    /// Contacts whose two endpoints lie in one strongly connected core of the material's own
    /// relation — mutual recursion in Rust, a recurring word in prose, and zero by construction in
    /// an expression tree.
    pub cyclic_contacts: u64,
    pub strongly_connected_cores: u64,
    /// Joins the reading refused because the name resolved to more than one declaration. `OPEN`
    /// may not be closed by choosing (`lean_development::open_recruitment`'s own discipline).
    pub open_joins: u64,
    pub containers: u64,
}

/// The source-native `L_t`.
#[derive(Clone, Debug)]
pub struct MaterialAtlas {
    kind: MaterialKind,
    constituents: Vec<String>,
    /// The material's own serialization index per constituent — a file order, a line, a slice
    /// position. Carried **only** so `⪯` can be shown not to be it.
    storage_ordinal: Vec<u64>,
    contacts: Vec<StructuralContact>,
    open_joins: u64,
    containers: u64,
}

impl MaterialAtlas {
    /// Found an atlas from a declared constituent population and a declared contact population.
    pub fn new(
        kind: MaterialKind,
        constituents: Vec<String>,
        storage_ordinal: Vec<u64>,
        contacts: Vec<StructuralContact>,
        open_joins: u64,
        containers: u64,
    ) -> Result<Self, MaterialIncidenceError> {
        if constituents.len() != storage_ordinal.len() {
            return Err(MaterialIncidenceError::Extent);
        }
        for name in &constituents {
            if name.is_empty() {
                return Err(MaterialIncidenceError::EmptyConstituent);
            }
            if name.split_whitespace().count() != 1 {
                return Err(MaterialIncidenceError::ConstituentCarriesWhitespace(
                    name.clone(),
                ));
            }
        }
        for contact in &contacts {
            if contact.from >= constituents.len()
                || contact.to >= constituents.len()
                || contact.owner >= constituents.len()
            {
                return Err(MaterialIncidenceError::Extent);
            }
        }
        Ok(Self {
            kind,
            constituents,
            storage_ordinal,
            contacts,
            open_joins,
            containers,
        })
    }

    pub const fn kind(&self) -> MaterialKind {
        self.kind
    }
    pub fn constituents(&self) -> &[String] {
        &self.constituents
    }
    pub fn contacts(&self) -> &[StructuralContact] {
        &self.contacts
    }

    /// `⪯_t`: the material's own dependency height, strongly-connected cores collapsed.
    ///
    /// `height(c) = 0` when `c` recruits nothing; otherwise `1 + max` over the heights of the
    /// cores it reaches. A leaf primitive sits at 0 and a deep theorem sits high, which is
    /// definition-before-use read off the material rather than off a line number. Mutual recursion
    /// is a single core at one height, which is the honest reading: neither member precedes the
    /// other.
    ///
    /// Returns `(height per constituent, core index per constituent, core population)`.
    pub fn heights(&self) -> (Vec<u32>, Vec<u32>, u32) {
        let population = self.constituents.len();
        let mut outgoing = vec![Vec::<usize>::new(); population];
        for contact in &self.contacts {
            outgoing[contact.from].push(contact.to);
        }
        let (core, cores) = strongly_connected_cores(&outgoing);

        // Tarjan emits a core only after every core it reaches, so heights settle in emission
        // order. `core_height` is indexed by core, and a core's height is one above the tallest
        // core any of its members reaches.
        let mut core_height = vec![0u32; cores as usize];
        // Members grouped by core, so a core is settled in one pass over its own out-edges.
        let mut members = vec![Vec::<usize>::new(); cores as usize];
        for (constituent, at) in core.iter().enumerate() {
            members[*at as usize].push(constituent);
        }
        // Cores are emitted by Tarjan in reverse topological order and numbered in emission order,
        // so core `k` only reaches cores `< k`.
        for at in 0..cores as usize {
            let mut height = 0u32;
            for member in &members[at] {
                for reached in &outgoing[*member] {
                    let other = core[*reached] as usize;
                    if other == at {
                        continue;
                    }
                    height = height.max(core_height[other].saturating_add(1));
                }
            }
            core_height[at] = height;
        }
        let heights = core
            .iter()
            .map(|at| core_height[*at as usize])
            .collect::<Vec<_>>();
        (heights, core, cores)
    }

    /// The counted work of serializing this atlas, taken before anything is founded.
    pub fn intake_work(&self) -> IntakeWork {
        let (heights, core, cores) = self.heights();
        let mut owner_heights = self
            .contacts
            .iter()
            .map(|contact| heights[contact.owner])
            .collect::<Vec<_>>();
        owner_heights.sort_unstable();
        owner_heights.dedup();
        let cyclic = self
            .contacts
            .iter()
            .filter(|contact| core[contact.from] == core[contact.to])
            .count() as u64;
        let occurrences = self.contacts.len() as u64;
        let ranks = owner_heights.len() as u64;
        IntakeWork {
            constituents: self.constituents.len() as u64,
            contacts: self.contacts.len() as u64,
            occurrences,
            // Exactly one cause per occurrence above rank zero.
            caused_by_edges: occurrences.saturating_sub(self.rank_zero_occurrences(&heights)),
            ranks,
            cyclic_contacts: cyclic,
            strongly_connected_cores: cores as u64,
            open_joins: self.open_joins,
            containers: self.containers,
        }
    }

    fn rank_zero_occurrences(&self, heights: &[u32]) -> u64 {
        let least = self
            .contacts
            .iter()
            .map(|contact| heights[contact.owner])
            .min()
            .unwrap_or(0);
        self.contacts
            .iter()
            .filter(|contact| heights[contact.owner] == least)
            .count() as u64
    }

    /// The dense rank of every contact-occurrence: the position of its owner's height in the
    /// sorted distinct owner-height set.
    pub fn occurrence_ranks(&self) -> Vec<u32> {
        let (heights, _, _) = self.heights();
        let mut present = self
            .contacts
            .iter()
            .map(|contact| heights[contact.owner])
            .collect::<Vec<_>>();
        present.sort_unstable();
        present.dedup();
        let dense = present
            .iter()
            .enumerate()
            .map(|(at, height)| (*height, at as u32))
            .collect::<BTreeMap<_, _>>();
        self.contacts
            .iter()
            .map(|contact| dense[&heights[contact.owner]])
            .collect()
    }

    /// Serialize the atlas into the intake's own vocabulary.
    ///
    /// One occurrence per contact, two patches, `caused_by` carrying the rank chain through one
    /// canonical representative per rank.
    pub fn declared_occurrences(
        &self,
        representative: RankRepresentative,
    ) -> Result<Vec<DeclaredOccurrence>, MaterialIncidenceError> {
        if self.contacts.is_empty() {
            return Err(MaterialIncidenceError::NoContact);
        }
        let ranks = self.occurrence_ranks();
        let identity = |at: usize| format!("{}:contact:{at}", self.kind.name());

        let highest = ranks.iter().copied().max().unwrap_or(0);
        let mut carrier = vec![Option::<usize>::None; highest as usize + 1];
        for (at, rank) in ranks.iter().enumerate() {
            let slot = &mut carrier[*rank as usize];
            *slot = Some(match (*slot, representative) {
                (None, _) => at,
                (Some(held), RankRepresentative::Least) => {
                    if identity(at) < identity(held) {
                        at
                    } else {
                        held
                    }
                }
                (Some(held), RankRepresentative::Greatest) => {
                    if identity(at) > identity(held) {
                        at
                    } else {
                        held
                    }
                }
            });
        }

        let mut occurrences = Vec::with_capacity(self.contacts.len());
        for (at, contact) in self.contacts.iter().enumerate() {
            let rank = ranks[at];
            let mut caused_by = BTreeSet::new();
            if rank > 0 {
                if let Some(Some(cause)) = carrier.get(rank as usize - 1) {
                    caused_by.insert(identity(*cause));
                }
            }
            occurrences.push(
                DeclaredOccurrence::from_text(
                    identity(at),
                    self.storage_ordinal[contact.owner],
                    caused_by,
                    &format!(
                        "{} {}",
                        self.constituents[contact.from], self.constituents[contact.to]
                    ),
                )
                .map_err(MaterialIncidenceError::Complex)?,
            );
        }
        Ok(occurrences)
    }

    /// Hand the atlas to `incidence_production::IncidenceComplex`. **The constructor beside
    /// `found`**, living here rather than there.
    pub fn found(
        &self,
        representative: RankRepresentative,
    ) -> Result<IncidenceComplex, MaterialIncidenceError> {
        let occurrences = self.declared_occurrences(representative)?;
        let contact_faces = self
            .contacts
            .iter()
            .map(|contact| {
                DeclaredContactFace::new(contact.species.name())
                    .map(|face| vec![face])
                    .map_err(MaterialIncidenceError::Complex)
            })
            .collect::<Result<Vec<_>, _>>()?;
        // A 1-cell has exactly two boundary 0-cells; the aperture is the contact itself and its
        // outside is empty by construction, which `patches_outside_extent` reports as zero.
        IncidenceComplex::found_with_contact_faces(&occurrences, 2, &contact_faces)
            .map_err(MaterialIncidenceError::Complex)
    }

    /// The gauge orbit of the rank representative. Every rank must be unmoved.
    pub fn rank_gauge_orbit(&self) -> Result<RankGaugeOrbit, MaterialIncidenceError> {
        let least = self.found(RankRepresentative::Least)?;
        let greatest = self.found(RankRepresentative::Greatest)?;
        let reading = |complex: &IncidenceComplex| {
            complex
                .sites()
                .iter()
                .map(|site| (site.surface.clone(), site.causal_rank))
                .collect::<BTreeSet<_>>()
        };
        Ok(RankGaugeOrbit {
            least_sites: least.sites().len(),
            greatest_sites: greatest.sites().len(),
            ranks_unmoved: reading(&least) == reading(&greatest),
        })
    }

    /// Read the founded complex back and require the material's own structure to be in it.
    ///
    /// Without this the module would be a way of spelling a structure in prose. With it, every
    /// declared contact must appear as a bond between the expected surfaces at the expected rank,
    /// or be accounted for as a refused self-contact.
    pub fn faithfulness(&self, complex: &IncidenceComplex) -> Faithfulness {
        let ranks = self.occurrence_ranks();
        let site_key = complex
            .sites()
            .iter()
            .enumerate()
            .map(|(at, site)| ((site.causal_rank, site.surface.as_str()), at))
            .collect::<BTreeMap<_, _>>();
        let founded = complex
            .bonds()
            .iter()
            .flat_map(|bond| {
                bond.contact_faces.iter().map(|face| {
                    (
                        complex.sites()[bond.from].causal_rank,
                        complex.sites()[bond.from].surface.as_str(),
                        complex.sites()[bond.to].surface.as_str(),
                        face.name(),
                    )
                })
            })
            .collect::<BTreeSet<_>>();

        let mut present = 0u64;
        let mut refused_self = 0u64;
        let mut absent = Vec::new();
        for (at, contact) in self.contacts.iter().enumerate() {
            let rank = ranks[at];
            let from = self.constituents[contact.from].as_str();
            let to = self.constituents[contact.to].as_str();
            if from == to {
                refused_self += 1;
                continue;
            }
            if founded.contains(&(rank, from, to, contact.species.name())) {
                present += 1;
            } else if absent.len() < 8 {
                absent.push(format!("{from} ⟶ {to} at rank {rank}"));
            }
        }
        let surfaces = site_key
            .keys()
            .map(|(_, surface)| *surface)
            .collect::<BTreeSet<_>>();
        let constituents_present = self
            .constituents
            .iter()
            .filter(|name| surfaces.contains(name.as_str()))
            .count() as u64;
        Faithfulness {
            contacts_declared: self.contacts.len() as u64,
            contacts_present: present,
            self_contacts_refused: refused_self,
            constituents_declared: self.constituents.len() as u64,
            constituents_present,
            absent,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RankGaugeOrbit {
    pub least_sites: usize,
    pub greatest_sites: usize,
    /// The representative is a gauge only if this is true.
    pub ranks_unmoved: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Faithfulness {
    pub contacts_declared: u64,
    pub contacts_present: u64,
    pub self_contacts_refused: u64,
    pub constituents_declared: u64,
    pub constituents_present: u64,
    /// Up to eight declared contacts the complex does not carry. A non-empty list is a defect.
    pub absent: Vec<String>,
}

impl Faithfulness {
    pub const fn is_faithful(&self) -> bool {
        self.absent.is_empty()
            && self.contacts_present + self.self_contacts_refused == self.contacts_declared
    }
}

/// Tarjan's algorithm, iterative so a 30,000-constituent atlas cannot overflow the cpu stack.
///
/// Returns `(core index per node, core population)`. Cores are numbered in emission order, which
/// is reverse topological: core `k` reaches only cores `< k`.
fn strongly_connected_cores(outgoing: &[Vec<usize>]) -> (Vec<u32>, u32) {
    let population = outgoing.len();
    let mut index = vec![u32::MAX; population];
    let mut low = vec![0u32; population];
    let mut on_stack = vec![false; population];
    let mut core = vec![u32::MAX; population];
    let mut stack = Vec::<usize>::new();
    let mut next_index = 0u32;
    let mut cores = 0u32;

    for root in 0..population {
        if index[root] != u32::MAX {
            continue;
        }
        let mut frame = vec![(root, 0usize)];
        index[root] = next_index;
        low[root] = next_index;
        next_index += 1;
        stack.push(root);
        on_stack[root] = true;

        while let Some((at, cursor)) = frame.pop() {
            if cursor < outgoing[at].len() {
                let next = outgoing[at][cursor];
                frame.push((at, cursor + 1));
                if index[next] == u32::MAX {
                    index[next] = next_index;
                    low[next] = next_index;
                    next_index += 1;
                    stack.push(next);
                    on_stack[next] = true;
                    frame.push((next, 0));
                } else if on_stack[next] {
                    low[at] = low[at].min(index[next]);
                }
                continue;
            }
            if low[at] == index[at] {
                while let Some(member) = stack.pop() {
                    on_stack[member] = false;
                    core[member] = cores;
                    if member == at {
                        break;
                    }
                }
                cores += 1;
            }
            if let Some((parent, _)) = frame.last().copied() {
                low[parent] = low[parent].min(low[at]);
            }
        }
    }
    (core, cores)
}

// ---------------------------------------------------------------------------------------------
// The conduct reading — taken identically for every material
// ---------------------------------------------------------------------------------------------

/// Everything the driver takes on one founded complex, so that four materials can be compared on
/// one row each. Every field is a count of something the complex returned; the emitted successors
/// themselves are returned separately and in full by [`ConductReading::emissions`].
#[derive(Clone, Debug)]
pub struct ConductReading {
    pub kind: MaterialKind,
    pub constituents: usize,
    pub contacts: usize,
    pub dependency_edges: usize,
    pub closed_boundaries: usize,
    pub ingress: usize,
    pub exposed: usize,
    pub self_contacts_refused: u64,
    pub greatest_multiplicity: u64,
    pub greatest_causal_rank: u32,
    /// Routes enumerated from the declared source aperture.
    pub routes: usize,
    /// Arrivals reached by more than one route — the vertices.
    pub plural_arrivals: usize,
    /// Arrivals whose cross term `|Σα|² − Σ|α|²` is non-zero: where the tape and the tower part.
    pub interfering_arrivals: usize,
    pub annihilating_pairs: usize,
    pub cancelled_fibers: usize,
    pub flat_boundaries: usize,
    pub curved_boundaries: usize,
    /// The emitted successors at grain 1, in full.
    pub emissions: Vec<EmittedSuccessor>,
    /// The highest grain the iterated hand-up reached, and why it stopped.
    pub grain_reached: u32,
    pub grain_stop: String,
    /// The source aperture's outside: constituents not used as a route source.
    pub sources_outside_aperture: usize,
    /// The depth routes were actually enumerated to, after the declared route budget cut it.
    pub effective_route_depth: usize,
    /// The greatest incident degree in the contact graph. It is what forces the cut above, and it
    /// is a material reading: a prose hub and an expression node are orders of magnitude apart.
    pub greatest_incident_degree: usize,
    /// Arrival fibers wider than the declared interference budget, counted rather than scanned.
    /// `IncidenceComplex::interfere`'s annihilation scan is quadratic in the arrivals it is given.
    pub arrivals_outside_interference_budget: usize,
}

/// One emitted successor, as text with its residual — never a count standing in for it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EmittedSuccessor {
    pub grain: u32,
    pub causal_rank: u32,
    pub surface: String,
    pub holonomy: String,
    pub flat: bool,
    pub chain_gauge: i8,
    pub internal_contacts: usize,
    pub carried_multiplicity: u64,
    pub departed: Vec<String>,
    pub exposed: Vec<String>,
}

/// Take the whole reading on one founded complex under one declared chart.
///
/// `source_aperture` bounds how many constituents are used as route sources, and the population it
/// excluded is returned in [`ConductReading::sources_outside_aperture`]. `route_depth` bounds a
/// route's length, and `route_budget` cuts that depth where the material's own greatest incident
/// degree would make enumeration unbounded — reported, never silent. `closure_budget` bounds the
/// iterated hand-up by **counted work** — `compounds² + compounds · contacts` — because
/// `next_grain` is quadratic in closed boundaries and linear in contacts, and a wall is a
/// measurement rather than a surprise.
#[allow(clippy::too_many_arguments)]
pub fn read_conduct(
    kind: MaterialKind,
    complex: &IncidenceComplex,
    chart: PhaseChart,
    source_aperture: usize,
    route_depth: usize,
    route_budget: u128,
    interference_arrivals: usize,
    closure_budget: u128,
) -> Result<ConductReading, MaterialIncidenceError> {
    let mut incident = vec![0usize; complex.sites().len()];
    for bond in complex.bonds() {
        incident[bond.from] += 1;
        incident[bond.to] += 1;
    }
    for (before, _) in complex.dependencies() {
        incident[*before] += 1;
    }
    let greatest_incident_degree = incident.iter().copied().max().unwrap_or(0);
    // The conservative bound on a simple walk of length `d` from any source.
    let mut depth = route_depth;
    while depth > 1 {
        let bound = (greatest_incident_degree.max(1) as u128).saturating_pow(depth as u32);
        if bound <= route_budget {
            break;
        }
        depth -= 1;
    }

    let sources = complex.sites().len().min(source_aperture);
    let mut refused_sources = 0usize;
    let mut arrivals_outside = 0usize;
    let mut routes = 0usize;
    let mut plural = 0usize;
    let mut interfering = 0usize;
    let mut annihilating = 0usize;
    let mut cancelled = 0usize;
    let zero = Rat::from_integer(BigInt::from(0));
    // Every route carries an exact composition of rational rotations, so the route POPULATION is
    // the cost — not the depth by itself. It is bounded by a declared budget and the sources it
    // did not reach are returned as its outside.
    for source in 0..sources {
        if routes as u128 > route_budget {
            refused_sources += sources - source;
            break;
        }
        // Per-source predicted work, so one hub cannot swallow the whole budget while a hundred
        // narrow constituents go unread.
        let predicted = (incident[source].max(1) as u128).saturating_mul(
            (greatest_incident_degree.max(1) as u128)
                .saturating_pow(depth.saturating_sub(1) as u32),
        );
        if predicted > route_budget {
            refused_sources += 1;
            continue;
        }
        let found = complex
            .routes_from(source, depth, chart)
            .map_err(MaterialIncidenceError::Complex)?;
        routes += found.len();
        // `IncidenceComplex::interfere`'s annihilation scan is quadratic in the arrivals it is
        // handed, so the arrivals are grouped here and a fiber wider than the declared budget is
        // counted rather than scanned. That population is `arrivals_outside`.
        let mut by_target = BTreeMap::<usize, Vec<_>>::new();
        for route in found {
            by_target.entry(route.target).or_default().push(route);
        }
        for (target, arriving) in by_target {
            if arriving.len() > interference_arrivals {
                arrivals_outside += 1;
                continue;
            }
            let interference = complex.interfere(&arriving, target, 0);
            if interference.routes.len() > 1 {
                plural += 1;
            }
            if interference.cross_term != zero {
                interfering += 1;
            }
            annihilating += interference.annihilating_pairs.len();
            if interference.cancelled {
                cancelled += 1;
            }
        }
    }

    // `IncidenceComplex::hand_up` scans every contact once per constituent on every closed
    // boundary, so its cost is `Σ_c |cycle(c)| · (contacts + ⪯ edges)`. Counted, not timed.
    let contacts = complex.bonds().len() as u128;
    let closure_work = complex
        .compounds()
        .iter()
        .map(|compound| compound.sites.len() as u128)
        .sum::<u128>()
        .saturating_mul(contacts.saturating_add(complex.dependencies().len() as u128));
    let (emissions, flat, curved, grain_reached, grain_stop) = if closure_work > closure_budget {
        (
            Vec::new(),
            0,
            0,
            0,
            format!(
                "hand-up refused: counted work {closure_work} exceeds the declared budget \
                 {closure_budget} (Σ cycle length · contacts, over {} closed boundaries and \
                 {contacts} contacts)",
                complex.compounds().len()
            ),
        )
    } else {
        let handed = complex
            .hand_up(chart)
            .map_err(MaterialIncidenceError::Complex)?;
        let flat = handed
            .iter()
            .filter(|emission| emission.terrain_is_flat())
            .count();
        let curved = handed.len() - flat;
        let emitted = handed
            .iter()
            .map(|emission| EmittedSuccessor {
                grain: emission.grain,
                causal_rank: emission.causal_rank,
                surface: emission.surface.clone(),
                holonomy: emission.holonomy_text(),
                flat: emission.terrain_is_flat(),
                chain_gauge: emission.chain_gauge,
                internal_contacts: emission.residual.internal_contacts,
                carried_multiplicity: emission.residual.carried_multiplicity,
                departed: emission.residual.departed_contacts.clone(),
                exposed: emission
                    .residual
                    .exposed
                    .iter()
                    .map(|(surface, polarity)| format!("{} {surface}", polarity.name()))
                    .collect(),
            })
            .collect::<Vec<_>>();
        let (grain, stop) = iterate_hand_up(complex, chart, closure_budget);
        (emitted, flat, curved, grain, stop)
    };

    Ok(ConductReading {
        kind,
        constituents: complex.sites().len(),
        contacts: complex.bonds().len(),
        dependency_edges: complex.dependencies().len(),
        closed_boundaries: complex.compounds().len(),
        ingress: complex.ingress().len(),
        exposed: complex.exposed().len(),
        self_contacts_refused: complex.self_contacts_refused(),
        greatest_multiplicity: complex
            .bonds()
            .iter()
            .map(|bond| bond.multiplicity)
            .max()
            .unwrap_or(0),
        greatest_causal_rank: complex
            .sites()
            .iter()
            .map(|site| site.causal_rank)
            .max()
            .unwrap_or(0),
        routes,
        plural_arrivals: plural,
        interfering_arrivals: interfering,
        annihilating_pairs: annihilating,
        cancelled_fibers: cancelled,
        flat_boundaries: flat,
        curved_boundaries: curved,
        emissions,
        grain_reached,
        grain_stop,
        sources_outside_aperture: complex.sites().len().saturating_sub(sources) + refused_sources,
        effective_route_depth: depth,
        greatest_incident_degree,
        arrivals_outside_interference_budget: arrivals_outside,
    })
}

fn iterate_hand_up(
    complex: &IncidenceComplex,
    chart: PhaseChart,
    closure_budget: u128,
) -> (u32, String) {
    let mut carried = complex.clone();
    let mut population = carried.compounds().len();
    loop {
        // `IncidenceComplex::next_grain` compares every ordered pair of closed boundaries and, for
        // each, scans every contact of the complex below. That is `compounds² · contacts`, and it
        // is the sharpest cost in the whole path.
        let compounds = carried.compounds().len() as u128;
        let contacts = carried.bonds().len() as u128;
        let work = compounds.saturating_mul(compounds).saturating_mul(contacts);
        if work > closure_budget {
            return (
                carried.grain(),
                format!(
                    "the hand-up stops at grain {}: `next_grain` costs compounds²·contacts = \
                     {compounds}²·{contacts} = {work}, above the declared budget {closure_budget}",
                    carried.grain()
                ),
            );
        }
        match carried.next_grain(chart) {
            Ok((_, next)) => {
                let emitted = next.compounds().len();
                if emitted == 0 {
                    return (
                        next.grain(),
                        format!(
                            "grain {} closed nothing: {} constituents, {} contacts, no independent \
                             cycle",
                            next.grain(),
                            next.sites().len(),
                            next.bonds().len()
                        ),
                    );
                }
                if emitted >= population && next.grain() > 1 {
                    return (
                        next.grain(),
                        format!("the population stopped contracting: {population} → {emitted}"),
                    );
                }
                population = emitted;
                carried = next;
            }
            Err(error) => {
                return (
                    carried.grain(),
                    format!("no complex above grain {}: {error:?}", carried.grain()),
                )
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Lean
// ---------------------------------------------------------------------------------------------

/// Found the Lean atlas from `lean_development`'s own reading.
///
/// `K` is the declaration, qualified. `∂` is [`DevelopmentReading::declared_recruitment_qualified`]
/// — the resolved term-position join, which refuses an ambiguous landing rather than choosing one
/// — plus the tactic-position join returned as a separate species. `⪯` is dependency height, which
/// is definition-before-use read off the recruitment relation and never off a line.
///
/// Nothing here re-reads Lean. The reader is `holonic_engine::lean_development`.
pub fn lean_atlas(
    recruitment: &BTreeMap<String, BTreeSet<String>>,
    conduct: &BTreeMap<String, BTreeSet<String>>,
    declaration_order: &[String],
    open_joins: u64,
    containers: u64,
) -> Result<MaterialAtlas, MaterialIncidenceError> {
    let mut index = BTreeMap::<&str, usize>::new();
    let mut constituents = Vec::new();
    let mut storage = Vec::new();
    for (at, name) in declaration_order.iter().enumerate() {
        if index.contains_key(name.as_str()) {
            continue;
        }
        index.insert(name.as_str(), constituents.len());
        constituents.push(sanitized(name));
        storage.push(at as u64);
    }
    let mut contacts = Vec::new();
    for (species, relation) in [
        (ContactSpecies::Recruits, recruitment),
        (ContactSpecies::Conducts, conduct),
    ] {
        for (head, tails) in relation {
            let Some(from) = index.get(head.as_str()).copied() else {
                continue;
            };
            for tail in tails {
                let Some(to) = index.get(tail.as_str()).copied() else {
                    continue;
                };
                contacts.push(StructuralContact {
                    from,
                    to,
                    owner: from,
                    species,
                });
            }
        }
    }
    MaterialAtlas::new(
        MaterialKind::Lean,
        constituents,
        storage,
        contacts,
        open_joins,
        containers,
    )
}

// ---------------------------------------------------------------------------------------------
// Rust
// ---------------------------------------------------------------------------------------------

/// One Rust item as the atlas carries it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RustItem {
    /// `fn`, `struct`, `enum`, `trait`, `type`, `const`, `static`, `union`, `macro_rules`.
    pub former: String,
    pub name: String,
    /// The module path derived from the source path — provenance and disambiguation.
    pub module: String,
    /// Serialization position: the section's index in the atlas's own source order.
    pub storage_ordinal: u64,
    /// Identifiers the item's own text names.
    pub named: BTreeSet<String>,
}

impl RustItem {
    pub fn qualified(&self) -> String {
        format!("{}:{}::{}", self.former, self.module, self.name)
    }
}

/// Read the items one Rust source section founds, and the identifiers its text names.
///
/// The **sectioning** is not done here: it is `LaboratorySourceAtlas`'s brace-balanced
/// `rust_item_closings`, and the caller hands the section text over. What this adds is the item
/// head and the identifier population, which is the same reading `lean_development` performs for
/// Lean and which nothing performed for Rust.
pub fn rust_items_of_section(module: &str, storage_ordinal: u64, text: &str) -> Vec<RustItem> {
    let mut found = Vec::new();
    let named = rust_identifiers(text);
    for line in text.lines() {
        let trimmed = line.trim_start();
        let mut cursor = trimmed;
        // Strip the visibility and the modifiers the material writes before the former.
        loop {
            let stripped = ["pub ", "async ", "const ", "unsafe ", "extern ", "default "]
                .iter()
                .find_map(|prefix| cursor.strip_prefix(prefix));
            match stripped {
                Some(rest) => cursor = rest.trim_start(),
                None => {
                    if let Some(rest) = cursor.strip_prefix("pub(") {
                        match rest.find(')') {
                            Some(at) => cursor = rest[at + 1..].trim_start(),
                            None => break,
                        }
                    } else if cursor.starts_with('"') {
                        // `extern "C"` — the abi string, then the former.
                        match cursor[1..].find('"') {
                            Some(at) => cursor = cursor[at + 2..].trim_start(),
                            None => break,
                        }
                    } else {
                        break;
                    }
                }
            }
        }
        let Some((former, rest)) = cursor.split_once(char::is_whitespace) else {
            continue;
        };
        if !matches!(
            former,
            "fn" | "struct" | "enum" | "trait" | "type" | "union" | "static" | "macro_rules!"
        ) {
            continue;
        }
        let name = rest
            .trim_start()
            .split(|glyph: char| !(glyph.is_alphanumeric() || glyph == '_'))
            .find(|word| !word.is_empty())
            .unwrap_or_default();
        if name.is_empty() {
            continue;
        }
        found.push(RustItem {
            former: former.trim_end_matches('!').to_owned(),
            name: name.to_owned(),
            module: module.to_owned(),
            storage_ordinal,
            named: named.clone(),
        });
    }
    found
}

/// Every identifier the text names, less the Rust keywords the grammar owns.
pub fn rust_identifiers(text: &str) -> BTreeSet<String> {
    const KEYWORDS: &[&str] = &[
        "as", "async", "await", "break", "const", "continue", "crate", "dyn", "else", "enum",
        "extern", "false", "fn", "for", "if", "impl", "in", "let", "loop", "match", "mod", "move",
        "mut", "pub", "ref", "return", "self", "Self", "static", "struct", "super", "trait",
        "true", "type", "union", "unsafe", "use", "where", "while", "usize", "isize", "u8", "u16",
        "u32", "u64", "u128", "i8", "i16", "i32", "i64", "i128", "bool", "char", "str", "String",
        "Vec", "Option", "Some", "None", "Result", "Ok", "Err", "Box",
    ];
    let keywords = KEYWORDS.iter().copied().collect::<BTreeSet<_>>();
    let mut found = BTreeSet::new();
    let mut word = String::new();
    for glyph in text.chars() {
        if glyph.is_alphanumeric() || glyph == '_' {
            word.push(glyph);
            continue;
        }
        if !word.is_empty() && !keywords.contains(word.as_str()) && word.len() > 1 {
            found.insert(std::mem::take(&mut word));
        } else {
            word.clear();
        }
    }
    if !word.is_empty() && !keywords.contains(word.as_str()) && word.len() > 1 {
        found.insert(word);
    }
    found
}

/// Found the Rust atlas: an item is a constituent, and `∂` is the call and type incidence.
///
/// The join is on the item's **short name**, and a name declared by more than one item is `OPEN` —
/// no edge, counted. That is `lean_development::declared_recruitment`'s own measured discipline,
/// and its reason transfers exactly: this repository declares `fn new` in hundreds of places, and
/// a short-name join would land almost all of them on the wrong item.
pub fn rust_atlas(
    items: &[RustItem],
    containers: u64,
) -> Result<MaterialAtlas, MaterialIncidenceError> {
    let mut by_short = BTreeMap::<&str, Vec<usize>>::new();
    for (at, item) in items.iter().enumerate() {
        by_short.entry(item.name.as_str()).or_default().push(at);
    }
    let constituents = items
        .iter()
        .map(|item| sanitized(&item.qualified()))
        .collect::<Vec<_>>();
    let storage = items
        .iter()
        .map(|item| item.storage_ordinal)
        .collect::<Vec<_>>();

    let mut contacts = Vec::new();
    let mut open_joins = 0u64;
    for (from, item) in items.iter().enumerate() {
        let mut reached = BTreeSet::new();
        for symbol in &item.named {
            match by_short.get(symbol.as_str()) {
                None => {}
                Some(landing) if landing.len() == 1 => {
                    let to = landing[0];
                    if to != from {
                        reached.insert(to);
                    }
                }
                Some(_) => open_joins += 1,
            }
        }
        for to in reached {
            contacts.push(StructuralContact {
                from,
                to,
                owner: from,
                species: ContactSpecies::Calls,
            });
        }
    }
    MaterialAtlas::new(
        MaterialKind::Rust,
        constituents,
        storage,
        contacts,
        open_joins,
        containers,
    )
}

// ---------------------------------------------------------------------------------------------
// Arithmetic
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum BinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Power,
}

impl BinaryOp {
    pub const fn glyph(self) -> &'static str {
        match self {
            Self::Add => "add",
            Self::Subtract => "sub",
            Self::Multiply => "mul",
            Self::Divide => "div",
            Self::Power => "pow",
        }
    }

    /// A commutative operation has already quotiented its own hand away, so the construction
    /// carries no left-before-right contact. This is read off the algebra, not declared per
    /// expression.
    pub const fn commutative(self) -> bool {
        matches!(self, Self::Add | Self::Multiply)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArithNode {
    Literal(Rat),
    Negate(Box<ArithNode>),
    Binary(BinaryOp, Box<ArithNode>, Box<ArithNode>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArithmeticError {
    DivisionByZero,
    NegativeExponent,
    NonIntegerExponent,
    Parse(String),
}

impl ArithNode {
    /// The denoted value, exact over `BigRational`. **A face** (`TABLET_THE_OPERATIONS` §1): it
    /// forgets the construction, and what it forgets is exhibited by
    /// [`DenotedValueQuotient::separating_words`].
    pub fn denoted_value(&self) -> Result<Rat, ArithmeticError> {
        match self {
            Self::Literal(value) => Ok(value.clone()),
            Self::Negate(inner) => Ok(-inner.denoted_value()?),
            Self::Binary(op, left, right) => {
                let left = left.denoted_value()?;
                let right = right.denoted_value()?;
                Ok(match op {
                    BinaryOp::Add => left + right,
                    BinaryOp::Subtract => left - right,
                    BinaryOp::Multiply => left * right,
                    BinaryOp::Divide => {
                        if right == Rat::from_integer(BigInt::from(0)) {
                            return Err(ArithmeticError::DivisionByZero);
                        }
                        left / right
                    }
                    BinaryOp::Power => {
                        if !right.is_integer() {
                            return Err(ArithmeticError::NonIntegerExponent);
                        }
                        let exponent = right.to_integer();
                        if exponent < BigInt::from(0) {
                            return Err(ArithmeticError::NegativeExponent);
                        }
                        let mut carried = Rat::from_integer(BigInt::from(1));
                        let mut remaining = exponent;
                        while remaining > BigInt::from(0) {
                            carried *= left.clone();
                            remaining -= 1;
                        }
                        carried
                    }
                })
            }
        }
    }

    /// The construction's own node population and operand incidence, as an atlas fragment.
    fn receive(
        &self,
        label: &str,
        path: &str,
        constituents: &mut Vec<String>,
        storage: &mut Vec<u64>,
        contacts: &mut Vec<StructuralContact>,
    ) -> usize {
        let ordinal = constituents.len() as u64;
        // The construction's label is a SUFFIX, not a prefix. `incidence_production`'s
        // `contact_winding` is `popcount(last octet of the source ⊕ first octet of the target)` and
        // `sheet_of` reads the first octet, so a common prefix would give every contact in the
        // family the identical turn — a receipt that could not have come out otherwise
        // (`CLAUDE.md` §8). Measured before this was moved: all 432 closed boundaries returned the
        // same holonomy `(11/61, −60/61)`.
        let surface = match self {
            Self::Literal(value) => {
                if value.is_integer() {
                    format!("{}@{path}#{label}", value.to_integer())
                } else {
                    format!("{}/{}@{path}#{label}", value.numer(), value.denom())
                }
            }
            Self::Negate(_) => format!("neg@{path}#{label}"),
            Self::Binary(op, _, _) => format!("{}@{path}#{label}", op.glyph()),
        };
        let at = constituents.len();
        constituents.push(surface);
        storage.push(ordinal);
        match self {
            Self::Literal(_) => {}
            Self::Negate(inner) => {
                let child =
                    inner.receive(label, &format!("{path}U"), constituents, storage, contacts);
                contacts.push(StructuralContact {
                    from: at,
                    to: child,
                    owner: at,
                    species: ContactSpecies::Operand,
                });
            }
            Self::Binary(op, left, right) => {
                let left_at =
                    left.receive(label, &format!("{path}L"), constituents, storage, contacts);
                let right_at =
                    right.receive(label, &format!("{path}R"), constituents, storage, contacts);
                contacts.push(StructuralContact {
                    from: at,
                    to: left_at,
                    owner: at,
                    species: ContactSpecies::Operand,
                });
                contacts.push(StructuralContact {
                    from: at,
                    to: right_at,
                    owner: at,
                    species: ContactSpecies::Operand,
                });
                if !op.commutative() {
                    // `o_t` as a cell: the hand this operation does not quotient away.
                    contacts.push(StructuralContact {
                        from: left_at,
                        to: right_at,
                        owner: at,
                        species: ContactSpecies::OperandOrder,
                    });
                }
            }
        }
        at
    }
}

/// One construction: its presentation, its tree, and the label that keeps its constituents its own.
#[derive(Clone, Debug)]
pub struct ArithConstruction {
    pub label: String,
    pub presentation: String,
    pub node: ArithNode,
}

/// Found the arithmetic atlas from a family of constructions.
///
/// Each construction is its own component: constituents carry the construction's label, so two
/// occurrences of the numeral `2` in one expression are two constituents and the numeral `2` in
/// two expressions is two more. That is **occurrence identity** kept as a separate relation from
/// denoted-value equality, which is exactly what `canon/THE_HOLOBROCHOS_SPINE.md` §2 retains.
pub fn arithmetic_atlas(
    family: &[ArithConstruction],
) -> Result<MaterialAtlas, MaterialIncidenceError> {
    let mut constituents = Vec::new();
    let mut storage = Vec::new();
    let mut contacts = Vec::new();
    for construction in family {
        construction.node.receive(
            &construction.label,
            ".",
            &mut constituents,
            &mut storage,
            &mut contacts,
        );
    }
    MaterialAtlas::new(
        MaterialKind::Arithmetic,
        constituents,
        storage,
        contacts,
        0,
        family.len() as u64,
    )
}

/// A strict exact parser: integers, `+ - * / ^`, unary minus, parentheses. No float anywhere.
///
/// `expr := term (('+'|'-') term)*`, `term := factor (('*'|'/') factor)*`,
/// `factor := unary ('^' factor)?` — right associative — `unary := '-' unary | atom`,
/// `atom := digits | '(' expr ')'`.
pub fn parse_arithmetic(text: &str) -> Result<ArithNode, ArithmeticError> {
    let glyphs = text
        .chars()
        .filter(|glyph| !glyph.is_whitespace())
        .collect::<Vec<_>>();
    let mut cursor = 0usize;
    let node = parse_expression(&glyphs, &mut cursor)?;
    if cursor != glyphs.len() {
        return Err(ArithmeticError::Parse(format!(
            "{text}: {} glyphs unread",
            glyphs.len() - cursor
        )));
    }
    Ok(node)
}

fn parse_expression(glyphs: &[char], cursor: &mut usize) -> Result<ArithNode, ArithmeticError> {
    let mut carried = parse_term(glyphs, cursor)?;
    while let Some(glyph) = glyphs.get(*cursor).copied() {
        let op = match glyph {
            '+' => BinaryOp::Add,
            '-' => BinaryOp::Subtract,
            _ => break,
        };
        *cursor += 1;
        let right = parse_term(glyphs, cursor)?;
        carried = ArithNode::Binary(op, Box::new(carried), Box::new(right));
    }
    Ok(carried)
}

fn parse_term(glyphs: &[char], cursor: &mut usize) -> Result<ArithNode, ArithmeticError> {
    let mut carried = parse_factor(glyphs, cursor)?;
    while let Some(glyph) = glyphs.get(*cursor).copied() {
        let op = match glyph {
            '*' => BinaryOp::Multiply,
            '/' => BinaryOp::Divide,
            _ => break,
        };
        *cursor += 1;
        let right = parse_factor(glyphs, cursor)?;
        carried = ArithNode::Binary(op, Box::new(carried), Box::new(right));
    }
    Ok(carried)
}

fn parse_factor(glyphs: &[char], cursor: &mut usize) -> Result<ArithNode, ArithmeticError> {
    let base = parse_unary(glyphs, cursor)?;
    if glyphs.get(*cursor).copied() == Some('^') {
        *cursor += 1;
        let exponent = parse_factor(glyphs, cursor)?;
        return Ok(ArithNode::Binary(
            BinaryOp::Power,
            Box::new(base),
            Box::new(exponent),
        ));
    }
    Ok(base)
}

fn parse_unary(glyphs: &[char], cursor: &mut usize) -> Result<ArithNode, ArithmeticError> {
    if glyphs.get(*cursor).copied() == Some('-') {
        *cursor += 1;
        return Ok(ArithNode::Negate(Box::new(parse_unary(glyphs, cursor)?)));
    }
    parse_atom(glyphs, cursor)
}

fn parse_atom(glyphs: &[char], cursor: &mut usize) -> Result<ArithNode, ArithmeticError> {
    match glyphs.get(*cursor).copied() {
        Some('(') => {
            *cursor += 1;
            let inner = parse_expression(glyphs, cursor)?;
            if glyphs.get(*cursor).copied() != Some(')') {
                return Err(ArithmeticError::Parse("unclosed group".to_owned()));
            }
            *cursor += 1;
            Ok(inner)
        }
        Some(glyph) if glyph.is_ascii_digit() => {
            let start = *cursor;
            while glyphs
                .get(*cursor)
                .is_some_and(|glyph| glyph.is_ascii_digit())
            {
                *cursor += 1;
            }
            let digits = glyphs[start..*cursor].iter().collect::<String>();
            let value = digits
                .parse::<BigInt>()
                .map_err(|error| ArithmeticError::Parse(format!("{digits}: {error}")))?;
            Ok(ArithNode::Literal(Rat::from_integer(value)))
        }
        other => Err(ArithmeticError::Parse(format!("unexpected {other:?}"))),
    }
}

/// Build a family from presentations, labelling each by its position so the labels carry no reading.
pub fn arithmetic_family(
    presentations: &[&str],
) -> Result<Vec<ArithConstruction>, ArithmeticError> {
    let mut family = Vec::with_capacity(presentations.len());
    for (at, presentation) in presentations.iter().enumerate() {
        family.push(ArithConstruction {
            label: format!("c{at:02}"),
            presentation: (*presentation).to_owned(),
            node: parse_arithmetic(presentation)?,
        });
    }
    Ok(family)
}

// ---------------------------------------------------------------------------------------------
// The four relations, and the quotient the denoted value is
// ---------------------------------------------------------------------------------------------

/// The construction's face at the **complex** — what the founded incidence returns about it.
///
/// This is the receiver against which the denoted-value quotient is a quotient: two constructions
/// with one value and two of these readings are exactly a collapsed pair.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ConstructionFace {
    pub constituents: usize,
    pub contacts: usize,
    pub closed_boundaries: usize,
    pub depth: u32,
    /// Route surfaces with the construction's own label stripped, so two constructions can be
    /// compared at all. Retaining the label would make every pair trivially separable and the
    /// quotient vacuous.
    pub routes: BTreeSet<String>,
}

/// What the denoted-value receiver collapses, with the word that separates each collapsed pair.
#[derive(Clone, Debug)]
pub struct DenotedValueQuotient {
    /// One block per denoted value: the value, and the constructions that denote it.
    pub blocks: Vec<(Rat, Vec<String>)>,
    /// Collapsed pairs: `(left presentation, right presentation, separating word or the coordinate
    /// that separates them)`. This is the exact loss of the quotient (`H.0016`).
    pub separating_words: Vec<(String, String, String)>,
    /// Pairs the construction receiver could **not** separate: the quotient's own blind spot.
    pub indistinguishable: Vec<(String, String)>,
    /// Presentation equality: distinct presentation strings.
    pub distinct_presentations: usize,
    /// Occurrence identity: the family's own population.
    pub occurrences: usize,
}

/// Take the four relations the retained law keeps apart, on one founded complex.
///
/// - **presentation equality** — the input string
/// - **denoted-value equality** — the exact rational, computed by [`ArithNode::denoted_value`]
/// - **receiver equality** — [`ConstructionFace`], read off the founded complex
/// - **occurrence identity** — the construction's own place in the family
pub fn denoted_value_quotient(
    family: &[ArithConstruction],
    complex: &IncidenceComplex,
    chart: PhaseChart,
    route_depth: usize,
) -> Result<DenotedValueQuotient, MaterialIncidenceError> {
    // Group the complex's sites by which construction's label they carry.
    let mut sites_of = BTreeMap::<String, Vec<usize>>::new();
    for (at, site) in complex.sites().iter().enumerate() {
        if let Some((_, label)) = site.surface.rsplit_once('#') {
            sites_of.entry(label.to_owned()).or_default().push(at);
        }
    }

    let mut faces = BTreeMap::<String, ConstructionFace>::new();
    for construction in family {
        let own = sites_of
            .get(&construction.label)
            .cloned()
            .unwrap_or_default();
        let owned = own.iter().copied().collect::<BTreeSet<_>>();
        let mut routes = BTreeSet::new();
        for source in &own {
            let found = complex
                .routes_from(*source, route_depth, chart)
                .map_err(MaterialIncidenceError::Complex)?;
            for route in &found {
                routes.insert(strip_label(&complex.route_surface(route)));
            }
        }
        let contacts = complex
            .bonds()
            .iter()
            .filter(|bond| owned.contains(&bond.from) && owned.contains(&bond.to))
            .count();
        let closed = complex
            .compounds()
            .iter()
            .filter(|compound| compound.sites.iter().all(|site| owned.contains(site)))
            .count();
        let depth = own
            .iter()
            .map(|at| complex.sites()[*at].causal_rank)
            .max()
            .unwrap_or(0)
            .saturating_sub(
                own.iter()
                    .map(|at| complex.sites()[*at].causal_rank)
                    .min()
                    .unwrap_or(0),
            );
        faces.insert(
            construction.presentation.clone(),
            ConstructionFace {
                constituents: own.len(),
                contacts,
                closed_boundaries: closed,
                depth,
                routes,
            },
        );
    }

    let mut by_value = BTreeMap::<String, (Rat, Vec<String>)>::new();
    for construction in family {
        let value = construction
            .node
            .denoted_value()
            .map_err(MaterialIncidenceError::Arithmetic)?;
        by_value
            .entry(format!("{value}"))
            .or_insert_with(|| (value.clone(), Vec::new()))
            .1
            .push(construction.presentation.clone());
    }

    let mut separating = Vec::new();
    let mut indistinguishable = Vec::new();
    for (_, (_, block)) in &by_value {
        for (at, left) in block.iter().enumerate() {
            for right in block.iter().skip(at + 1) {
                let left_face = &faces[left];
                let right_face = &faces[right];
                match separating_word(left_face, right_face) {
                    Some(word) => separating.push((left.clone(), right.clone(), word)),
                    None => indistinguishable.push((left.clone(), right.clone())),
                }
            }
        }
    }

    Ok(DenotedValueQuotient {
        blocks: by_value.into_values().collect(),
        separating_words: separating,
        indistinguishable,
        distinct_presentations: family
            .iter()
            .map(|construction| construction.presentation.as_str())
            .collect::<BTreeSet<_>>()
            .len(),
        occurrences: family.len(),
    })
}

/// The shortest word the construction receiver uses to tell two constructions apart.
///
/// A route surface present in one and absent from the other is the strongest form, because it is
/// literally a passage one construction affords and the other does not. Where no route separates
/// them, a differing structural coordinate is returned instead, named. Where nothing separates
/// them, `None` — and that is a blind spot the return must carry rather than hide.
fn separating_word(left: &ConstructionFace, right: &ConstructionFace) -> Option<String> {
    let mut candidates = left
        .routes
        .symmetric_difference(&right.routes)
        .cloned()
        .collect::<Vec<_>>();
    candidates.sort_by_key(|word| (word.chars().count(), word.clone()));
    if let Some(word) = candidates.first() {
        let owner = if left.routes.contains(word) {
            "left"
        } else {
            "right"
        };
        return Some(format!("route {word:?} afforded only by the {owner}"));
    }
    if left.closed_boundaries != right.closed_boundaries {
        return Some(format!(
            "closed boundaries {} against {}",
            left.closed_boundaries, right.closed_boundaries
        ));
    }
    if left.constituents != right.constituents {
        return Some(format!(
            "constituents {} against {}",
            left.constituents, right.constituents
        ));
    }
    if left.contacts != right.contacts {
        return Some(format!(
            "contacts {} against {}",
            left.contacts, right.contacts
        ));
    }
    if left.depth != right.depth {
        return Some(format!("depth {} against {}", left.depth, right.depth));
    }
    None
}

/// Drop each constituent's construction label, so two constructions can be compared at all.
/// Retaining it would make every pair trivially separable and the quotient vacuous.
fn strip_label(surface: &str) -> String {
    surface
        .split(' ')
        .map(|word| match word.rsplit_once('#') {
            Some((rest, label))
                if label.starts_with('c')
                    && label.len() > 1
                    && label[1..].chars().all(|glyph| glyph.is_ascii_digit()) =>
            {
                rest
            }
            _ => word,
        })
        .collect::<Vec<_>>()
        .join(" ")
}

// ---------------------------------------------------------------------------------------------
// Prose — the declared control
// ---------------------------------------------------------------------------------------------

/// Found the prose atlas: patches, and §III's byte-serialization adjacency.
///
/// This is the tape chart written as an atlas, so the other three materials have something
/// strictly comparable to be different from. It is not a straw man: §III licenses it as one lawful
/// source chart, and what the ratified law forbids is that it counterfeit the others.
pub fn prose_atlas(
    occurrences: &[(String, String)],
    patch_extent: usize,
) -> Result<MaterialAtlas, MaterialIncidenceError> {
    let mut index = BTreeMap::<String, usize>::new();
    let mut constituents = Vec::new();
    let mut storage = Vec::new();
    let mut contacts = Vec::new();
    let mut seen = BTreeSet::new();
    for (_, text) in occurrences {
        let mut previous: Option<usize> = None;
        for patch in text.split_whitespace().take(patch_extent) {
            let at = match index.get(patch) {
                Some(at) => *at,
                None => {
                    let at = constituents.len();
                    index.insert(patch.to_owned(), at);
                    constituents.push(patch.to_owned());
                    storage.push(at as u64);
                    at
                }
            };
            if let Some(prior) = previous {
                if seen.insert((prior, at)) {
                    contacts.push(StructuralContact {
                        from: prior,
                        to: at,
                        owner: prior,
                        species: ContactSpecies::Adjacency,
                    });
                }
            }
            previous = Some(at);
        }
    }
    MaterialAtlas::new(
        MaterialKind::Prose,
        constituents,
        storage,
        contacts,
        0,
        occurrences.len() as u64,
    )
}

fn sanitized(name: &str) -> String {
    let joined = name.split_whitespace().collect::<Vec<_>>().join("·");
    if joined.is_empty() {
        "·".to_owned()
    } else {
        joined
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn four() -> Vec<ArithConstruction> {
        arithmetic_family(&["4", "2+2", "2*2", "2^2", "6-2", "8/2"]).expect("the family parses")
    }

    #[test]
    fn every_construction_of_four_denotes_four_exactly() {
        for construction in four() {
            assert_eq!(
                construction.node.denoted_value().unwrap(),
                Rat::from_integer(BigInt::from(4)),
                "{} did not denote 4",
                construction.presentation
            );
        }
    }

    #[test]
    fn a_commutative_node_closes_nothing_and_a_non_commutative_node_closes_one_boundary() {
        // The hand is the whole difference: `-`, `/` and `^` emit an operand-order contact and
        // `+`, `*` do not, so the first three close a triangle and the last two are trees.
        for (presentation, expected) in [
            ("2+2", 0usize),
            ("2*2", 0),
            ("2^2", 1),
            ("6-2", 1),
            ("8/2", 1),
        ] {
            let family = arithmetic_family(&[presentation]).unwrap();
            let atlas = arithmetic_atlas(&family).unwrap();
            let complex = atlas.found(RankRepresentative::Least).unwrap();
            assert_eq!(
                complex.compounds().len(),
                expected,
                "{presentation} closed {} boundaries",
                complex.compounds().len()
            );
        }
    }

    #[test]
    fn the_intake_is_faithful_and_the_body_admits_it() {
        let family = four();
        let atlas = arithmetic_atlas(&family).unwrap();
        let complex = atlas.found(RankRepresentative::Least).unwrap();
        let faithfulness = atlas.faithfulness(&complex);
        assert!(
            faithfulness.is_faithful(),
            "the complex did not carry the declared atlas: {faithfulness:?}"
        );
        complex
            .validate_with_body(true)
            .expect("the body admits the material's own atlas");
        complex
            .validate_with_body(false)
            .expect("and admits it in another storage order");
    }

    #[test]
    fn plural_declared_contact_faces_survive_on_one_bond_without_becoming_its_class() {
        let atlas = MaterialAtlas::new(
            MaterialKind::Lean,
            vec!["source".to_owned(), "target".to_owned()],
            vec![0, 1],
            vec![
                StructuralContact {
                    from: 0,
                    to: 1,
                    owner: 0,
                    species: ContactSpecies::Recruits,
                },
                StructuralContact {
                    from: 0,
                    to: 1,
                    owner: 0,
                    species: ContactSpecies::Conducts,
                },
            ],
            0,
            1,
        )
        .unwrap();
        let complex = atlas.found(RankRepresentative::Least).unwrap();
        assert_eq!(
            complex.bonds().len(),
            1,
            "equal endpoints found one contact"
        );
        let faces = complex.bonds()[0]
            .contact_faces
            .iter()
            .map(DeclaredContactFace::name)
            .collect::<BTreeSet<_>>();
        assert_eq!(faces, BTreeSet::from(["conducts", "recruits"]));
        assert_eq!(complex.bonds()[0].multiplicity, 2);
        assert!(atlas.faithfulness(&complex).is_faithful());
    }

    #[test]
    fn the_rank_representative_is_a_gauge_and_moves_nothing() {
        let family = four();
        let atlas = arithmetic_atlas(&family).unwrap();
        let orbit = atlas.rank_gauge_orbit().unwrap();
        assert!(
            orbit.ranks_unmoved,
            "the canonical rank representative moved a rank: {orbit:?}"
        );
        assert_eq!(orbit.least_sites, orbit.greatest_sites);
    }

    #[test]
    fn the_denoted_value_receiver_collapses_what_the_construction_receiver_separates() {
        let family = four();
        let atlas = arithmetic_atlas(&family).unwrap();
        let complex = atlas.found(RankRepresentative::Least).unwrap();
        let quotient =
            denoted_value_quotient(&family, &complex, PhaseChart::WindingAdjacent, 4).unwrap();
        assert_eq!(quotient.blocks.len(), 1, "six constructions, one value");
        assert_eq!(quotient.blocks[0].1.len(), 6);
        // Every pair in the block is collapsed by the value and separated by the construction.
        assert_eq!(
            quotient.separating_words.len() + quotient.indistinguishable.len(),
            15
        );
        assert!(
            !quotient.separating_words.is_empty(),
            "the construction receiver separated nothing"
        );
        // The anti-tautology check, re-founded 2026-08-14 when the transport stopped reading the
        // constituents' octets and started reading their declared contact species.
        //
        // **It used to require the turns themselves to vary, and they did — because `popcount('-')`,
        // `popcount('/')` and `popcount('^')` differ.** That is the operator's SPELLING deciding the
        // geometry, which is the defect the transport repair removes. Read structurally, every
        // closed boundary in arithmetic is the SAME triangle — two operands and one operand-order —
        // so every one returns the same turn, and nesting only makes more identical triangles.
        // Measured: `6-2`, `8/2`, `2^2`, `8/2/1` and `9-2-3` all return `(5/13, -12/13)`.
        //
        // So the check moves to the level where the reading can vary, which is the bond. The
        // species reading must take more than one value on this family, or it is a constant wearing
        // a type; and the loop sums coincide because the loops are isomorphic, which is a statement
        // about arithmetic rather than about the reading.
        let windings = complex
            .bonds()
            .iter()
            .map(|bond| bond.species_winding)
            .collect::<BTreeSet<_>>();
        assert!(
            windings.len() > 1,
            "the species reading returned one winding across the whole family: {windings:?}"
        );
        let turns = complex
            .hand_up(PhaseChart::WindingAdjacent)
            .unwrap()
            .iter()
            .map(crate::incidence_production::Emission::holonomy_text)
            .collect::<BTreeSet<_>>();
        assert_eq!(
            turns.len(),
            1,
            "arithmetic's closed boundaries are all the same triangle, so one turn is the honest \
             return; more than one would mean something other than the structure decided it: \
             {turns:?}"
        );
        // `2+2` and `2*2` remain the same operand-contact species. Preserving that face honestly
        // does not invent an operation class; a consequence intervention is still required.
        let pair = quotient
            .separating_words
            .iter()
            .find(|(left, right, _)| left == "2+2" && right == "2*2");
        assert!(
            pair.is_some(),
            "the isomorphic pair was not separated at all"
        );
    }

    #[test]
    fn a_control_family_of_distinct_values_collapses_nothing() {
        // The falsifier must be able to fail: a family whose values differ has one construction
        // per block and no collapsed pair whatsoever.
        let family = arithmetic_family(&["4", "5", "6", "7"]).unwrap();
        let atlas = arithmetic_atlas(&family).unwrap();
        // Four bare literals are four constituents and no contact at all, which is itself the
        // return: an atom is a constituent with no boundary, so no complex can be founded on it.
        assert_eq!(atlas.constituents().len(), 4);
        assert!(atlas.contacts().is_empty());
        assert!(matches!(
            atlas.found(RankRepresentative::Least),
            Err(MaterialIncidenceError::NoContact)
        ));

        let family = arithmetic_family(&["2^2", "2^3", "2^4", "2^5"]).unwrap();
        let atlas = arithmetic_atlas(&family).unwrap();
        let complex = atlas.found(RankRepresentative::Least).unwrap();
        let quotient =
            denoted_value_quotient(&family, &complex, PhaseChart::WindingAdjacent, 4).unwrap();
        assert_eq!(quotient.blocks.len(), 4);
        assert!(quotient.separating_words.is_empty());
        assert!(quotient.indistinguishable.is_empty());
    }

    #[test]
    fn the_dependency_height_is_not_the_serialization_order() {
        // `2*(1+1)`: the literals sit at height 0, the inner `+` at 1, the `*` at 2 — while the
        // serialization order is a pre-order walk that puts the `*` first.
        let family = arithmetic_family(&["2*(1+1)"]).unwrap();
        let atlas = arithmetic_atlas(&family).unwrap();
        let (heights, _, _) = atlas.heights();
        assert_eq!(heights[0], 2, "the root is the tallest");
        assert!(heights.iter().any(|height| *height == 0));
        assert!(heights.iter().any(|height| *height == 1));
        // The storage ordinal ascends with the walk and the height does not.
        let storage_ascends = heights.windows(2).all(|pair| pair[0] <= pair[1]);
        assert!(!storage_ascends, "height tracked the walk order exactly");
    }

    #[test]
    fn the_prose_atlas_reproduces_the_tape_and_the_structural_atlases_do_not_look_like_it() {
        let text = "the leader founds the channel and the channel carries the leader";
        let prose = prose_atlas(&[("a".to_owned(), text.to_owned())], 64).unwrap();
        let complex = prose.found(RankRepresentative::Least).unwrap();
        assert!(prose.faithfulness(&complex).is_faithful());
        // Prose has a strongly connected core; an expression tree has none above size one.
        let work = prose.intake_work();
        assert!(work.cyclic_contacts > 0, "the tape carried no cycle at all");

        let family = arithmetic_family(&["2^2", "6-2"]).unwrap();
        let arithmetic = arithmetic_atlas(&family).unwrap();
        assert_eq!(arithmetic.intake_work().cyclic_contacts, 0);
    }

    #[test]
    fn a_rust_section_founds_its_item_and_names_what_it_recruits() {
        let text =
            "pub fn founds_a_channel(leader: Leader) -> Channel {\n    return_stroke(leader)\n}";
        let items = rust_items_of_section("holonic_engine::probe", 7, text);
        assert_eq!(items.len(), 1);
        assert_eq!(items[0].name, "founds_a_channel");
        assert_eq!(items[0].former, "fn");
        assert!(items[0].named.contains("return_stroke"));
        assert!(items[0].named.contains("Leader"));
        // The grammar's own words are not recruitment.
        assert!(!items[0].named.contains("pub"));
        assert!(!items[0].named.contains("fn"));
    }

    #[test]
    fn the_rust_join_refuses_an_ambiguous_short_name() {
        let items = vec![
            RustItem {
                former: "fn".to_owned(),
                name: "new".to_owned(),
                module: "a".to_owned(),
                storage_ordinal: 0,
                named: BTreeSet::new(),
            },
            RustItem {
                former: "fn".to_owned(),
                name: "new".to_owned(),
                module: "b".to_owned(),
                storage_ordinal: 1,
                named: BTreeSet::new(),
            },
            RustItem {
                former: "fn".to_owned(),
                name: "caller".to_owned(),
                module: "c".to_owned(),
                storage_ordinal: 2,
                named: BTreeSet::from(["new".to_owned(), "unique_target".to_owned()]),
            },
            RustItem {
                former: "fn".to_owned(),
                name: "unique_target".to_owned(),
                module: "d".to_owned(),
                storage_ordinal: 3,
                named: BTreeSet::new(),
            },
        ];
        let atlas = rust_atlas(&items, 4).unwrap();
        assert_eq!(atlas.intake_work().open_joins, 1, "`new` must stay OPEN");
        assert_eq!(
            atlas.contacts().len(),
            1,
            "only the unique landing is a bond"
        );
    }
}
