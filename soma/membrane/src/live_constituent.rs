//! One sparse graded-cellular constituent carried by live Standing.
//!
//! Source cell identifiers, lineage capabilities, event slots, and material rows never enter this
//! type.  They are transient coordinates used while one borrowed regional event is received.  A
//! committed constituent retains only the local cells which still factor into the construction,
//! their oriented incidence, the receiver-formed pins, the sparse path transports, and the exposed
//! residual which can affect a genuinely later current.

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;
use std::sync::Arc;

use body::channel::WindingQuantum;
use holonic_structure::CountedCrossing;

/// In-flight reading for the co-present seam closure, gated on `EROS_TRACE` and resolved once.
///
/// The closure is a fixpoint loop whose cost was attributed three different ways before anyone
/// measured its rounds. A phase that has not finished still has something to say.
pub(crate) static NO_PROJECTIVE_READ: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static WOUND_COMPARISON: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static HAND_RESIDUAL: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static RODE: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);
pub(crate) static BOTH_NULL: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static ARRIVING_NULL: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
pub(crate) static HELD_NULL: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
/// Of the null comparisons, how many also have zero REACH — i.e. the two places coincide, rather
/// than a place coinciding with the frame tip.
pub(crate) static ZERO_REACH: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);

pub(crate) fn seam_trace(detail: &core::fmt::Arguments<'_>) {
    use std::sync::OnceLock;
    static ENABLED: OnceLock<bool> = OnceLock::new();
    if *ENABLED.get_or_init(|| std::env::var_os("EROS_TRACE").is_some()) {
        eprintln!("eros-trace seam.round                  {detail}");
    }
}
use body::incidence::IncidenceHand;
use body::manifold::{
    cast_position, face_packed_word, packed_face_is_canonical, unpack_face, DirectedEventContact,
    Face, FeltDeed, FACE_WORDS,
};
use body::num::{
    cog_packed_word, packed_cog_is_canonical, packed_rung_is_canonical, read_cog, read_rung,
    rung_packed_word, Cog, Rung, COG_WORDS, RUNG_WORDS,
};
use body::place::Place;
use body::soul::Chi;

use crate::support_family::{
    LiveSupportExpression, LiveSupportFamily, LiveSupportSection, SupportFamilyError,
};

const NATIVE_MAGIC: u32 = 0x4552_4843;
const NATIVE_VERSION: u32 = 11;
const HEADER_WORDS: usize = 11;
const STRUCTURAL_PIN_FIXED_WORDS: usize = 20 + 2 * FACE_WORDS + 6 * COG_WORDS;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LiveConstituentError {
    Geometry,
    Topology,
    Algebra,
    Extent,
    InvalidWire,
    CompressionBoundaryChanged,
}

impl From<SupportFamilyError> for LiveConstituentError {
    fn from(error: SupportFamilyError) -> Self {
        match error {
            SupportFamilyError::Topology => Self::Topology,
            SupportFamilyError::Extent => Self::Extent,
            SupportFamilyError::InvalidWire => Self::InvalidWire,
        }
    }
}

/// Lineage of one exact interface candidate. An inherited capability was supplied by a world
/// membrane. A receiver-caused capability names an ordered chart passage and may retain the exact
/// material fiber at both ends; neither address itself asserts that the passages couple. That
/// relation can enter Standing only when a later exact path comparison closes through Swing.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InterfaceCapabilityOrigin {
    Inherited,
    ReceiverCaused,
}

/// Exact candidate address for one material interface. Equal numeric coordinates, equal reaches,
/// and equal faces do not create this identity. Inherited candidates are declared by a source;
/// receiver-caused candidates are derived from an ordered receiver passage and its optional exact
/// end fiber. The address only narrows possible meetings. The complete transported paths still
/// decide RIDE or OPEN.
///
/// The schema qualifies the world membrane's exact word grammar. The word body is deliberately
/// variable-length: a plural receiver face must not be hashed, sequentially interned, or rebased
/// into one scalar merely to fit the interface carrier. Equal fibers are equal structures in the
/// same declared grammar, independent of the order in which a machine first receives them.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ReceiverFiberIdentity {
    schema: u64,
    words: Arc<[u32]>,
}

impl ReceiverFiberIdentity {
    pub fn new(schema: u64, words: impl Into<Arc<[u32]>>) -> Self {
        Self {
            schema,
            words: words.into(),
        }
    }

    pub const fn schema(&self) -> u64 {
        self.schema
    }

    pub fn words(&self) -> &[u32] {
        &self.words
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InterfaceCapability {
    origin: InterfaceCapabilityOrigin,
    namespace: u64,
    local: u64,
    receiver_fiber: Option<(ReceiverFiberIdentity, ReceiverFiberIdentity)>,
}

impl InterfaceCapability {
    pub const fn new(namespace: u64, local: u64) -> Self {
        Self {
            origin: InterfaceCapabilityOrigin::Inherited,
            namespace,
            local,
            receiver_fiber: None,
        }
    }

    pub(crate) const fn receiver_caused(
        antecedent_receiver: u64,
        consequent_receiver: u64,
    ) -> Self {
        Self {
            origin: InterfaceCapabilityOrigin::ReceiverCaused,
            namespace: antecedent_receiver,
            local: consequent_receiver,
            receiver_fiber: None,
        }
    }

    pub(crate) fn receiver_caused_fiber(
        antecedent_receiver: u64,
        antecedent_fiber: ReceiverFiberIdentity,
        consequent_receiver: u64,
        consequent_fiber: ReceiverFiberIdentity,
    ) -> Self {
        Self {
            origin: InterfaceCapabilityOrigin::ReceiverCaused,
            namespace: antecedent_receiver,
            local: consequent_receiver,
            receiver_fiber: Some((antecedent_fiber, consequent_fiber)),
        }
    }

    pub const fn origin(&self) -> InterfaceCapabilityOrigin {
        self.origin
    }

    pub const fn namespace(&self) -> u64 {
        self.namespace
    }

    pub const fn local(&self) -> u64 {
        self.local
    }

    pub fn receiver_fiber(&self) -> Option<(&ReceiverFiberIdentity, &ReceiverFiberIdentity)> {
        self.receiver_fiber
            .as_ref()
            .map(|(antecedent, consequent)| (antecedent, consequent))
    }
}

/// One direction in a constituent-local frame. Axis zero is the already-live receiver plane;
/// every greater axis was established by an actual FOUND in this constituent or rebased from
/// exact cellular terrain. The number has no meaning outside this one constituent.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LocalAxis(u32);

impl LocalAxis {
    pub const fn new(local: u32) -> Self {
        Self(local)
    }

    pub const fn local(self) -> u32 {
        self.0
    }
}

/// Canonical oriented support for one sparse multivector coefficient.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocalBlade {
    axes: Vec<LocalAxis>,
}

impl LocalBlade {
    pub fn scalar() -> Self {
        Self { axes: Vec::new() }
    }

    pub fn axis(axis: LocalAxis) -> Self {
        Self { axes: vec![axis] }
    }

    pub fn axes(&self) -> &[LocalAxis] {
        &self.axes
    }

    /// Exterior product of two metric-free local basis blades. Distinct units anticommute and a
    /// repeated unit annihilates in this blade fiber. A receiver which actually supplies a
    /// quadratic form may contract this exterior carrier in its own world; Soma does not install
    /// `e_a^2 = +/-1` for every possible receiver. `None` is the exact repeated-axis zero, while
    /// the bool says whether canonical reordering reverses the coefficient.
    fn product(&self, right: &Self) -> Option<(Self, bool)> {
        let mut parity = false;
        for left_axis in &self.axes {
            for right_axis in &right.axes {
                if left_axis > right_axis {
                    parity = !parity;
                }
            }
        }
        let mut axes = Vec::with_capacity(self.axes.len() + right.axes.len());
        let mut left = 0usize;
        let mut right_at = 0usize;
        while left < self.axes.len() || right_at < right.axes.len() {
            match (self.axes.get(left), right.axes.get(right_at)) {
                (Some(a), Some(b)) if a == b => return None,
                (Some(a), Some(b)) if a < b => {
                    axes.push(*a);
                    left += 1;
                }
                (Some(_), Some(b)) => {
                    axes.push(*b);
                    right_at += 1;
                }
                (Some(a), None) => {
                    axes.push(*a);
                    left += 1;
                }
                (None, Some(b)) => {
                    axes.push(*b);
                    right_at += 1;
                }
                (None, None) => break,
            }
        }
        Some((Self { axes }, parity))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransportTerm {
    blade: LocalBlade,
    coefficient: Cog,
}

impl TransportTerm {
    pub fn blade(&self) -> &LocalBlade {
        &self.blade
    }

    pub const fn coefficient(&self) -> Cog {
        self.coefficient
    }
}

/// Sparse multivector carried by one actual path. Terms are canonical by blade and zero
/// coefficients are absent; no unused basis population is materialized.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SparseTransport {
    terms: Vec<TransportTerm>,
}

impl SparseTransport {
    pub fn identity() -> Self {
        Self {
            terms: vec![TransportTerm {
                blade: LocalBlade::scalar(),
                coefficient: Cog::lit(1),
            }],
        }
    }

    pub fn terms(&self) -> &[TransportTerm] {
        &self.terms
    }

    fn factor(chi: Chi, support: LocalAxis) -> Self {
        let mut terms = Vec::with_capacity(2);
        if chi.same.mag != 0 {
            terms.push(TransportTerm {
                blade: LocalBlade::scalar(),
                coefficient: chi.same,
            });
        }
        if chi.other.mag != 0 {
            terms.push(TransportTerm {
                blade: LocalBlade::axis(support),
                coefficient: chi.other,
            });
        }
        Self { terms }
    }

    fn product(&self, right: &Self) -> Self {
        let mut terms: Vec<TransportTerm> = Vec::new();
        for left in &self.terms {
            for right in &right.terms {
                let Some((blade, negative)) = left.blade.product(&right.blade) else {
                    continue;
                };
                let mut coefficient = left.coefficient.mul(right.coefficient);
                if negative {
                    coefficient = coefficient.turned(2);
                }
                if coefficient.mag == 0 {
                    continue;
                }
                match terms.binary_search_by(|term| term.blade.cmp(&blade)) {
                    Ok(at) => {
                        let joined = terms[at].coefficient.add(coefficient);
                        if joined.mag == 0 {
                            terms.remove(at);
                        } else {
                            terms[at].coefficient = joined;
                        }
                    }
                    Err(at) => terms.insert(at, TransportTerm { blade, coefficient }),
                }
            }
        }
        Self { terms }
    }

    fn rebased(&self, axes: &[LocalAxis]) -> Result<Self, LiveConstituentError> {
        let mut terms: Vec<TransportTerm> = Vec::new();
        terms
            .try_reserve_exact(self.terms.len())
            .map_err(|_| LiveConstituentError::Extent)?;
        for term in &self.terms {
            let mut mapped = Vec::new();
            mapped
                .try_reserve_exact(term.blade.axes.len())
                .map_err(|_| LiveConstituentError::Extent)?;
            for axis in &term.blade.axes {
                mapped.push(
                    *axes
                        .get(word_usize(axis.local())?)
                        .ok_or(LiveConstituentError::Algebra)?,
                );
            }
            let mut negative = false;
            for left in 0..mapped.len() {
                for right in left + 1..mapped.len() {
                    if mapped[left] == mapped[right] {
                        mapped.clear();
                        break;
                    }
                    if mapped[left] > mapped[right] {
                        negative = !negative;
                    }
                }
                if mapped.is_empty() && !term.blade.axes.is_empty() {
                    break;
                }
            }
            if mapped.is_empty() && !term.blade.axes.is_empty() {
                continue;
            }
            mapped.sort_unstable();
            let blade = LocalBlade { axes: mapped };
            let coefficient = if negative {
                term.coefficient.turned(2)
            } else {
                term.coefficient
            };
            match terms.binary_search_by(|existing| existing.blade.cmp(&blade)) {
                Ok(at) => {
                    let joined = terms[at].coefficient.add(coefficient);
                    if joined.mag == 0 {
                        terms.remove(at);
                    } else {
                        terms[at].coefficient = joined;
                    }
                }
                Err(at) => terms.insert(at, TransportTerm { blade, coefficient }),
            }
        }
        Ok(Self { terms })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FormedPin {
    position: Place,
    chi: Chi,
    winding: WindingQuantum,
    deed: FeltDeed,
}

/// The uncollapsed transport object at one triangular/parallel-path face. `through` and `direct`
/// are the two complete receiver-relative routes. `chi` is only the present Face carrier's
/// projective residual: it may remain present while a noncommuting comparison stays open, and a
/// horizon may leave the complete comparison real while that projection is absent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParallelPathComparison {
    through: Face,
    direct: Face,
    chi: Option<Chi>,
}

impl ParallelPathComparison {
    pub fn new(through: Face, direct: Face) -> Self {
        Self {
            through,
            direct,
            chi: through.chi_against(&direct),
        }
    }

    pub const fn through(self) -> Face {
        self.through
    }

    pub const fn direct(self) -> Face {
        self.direct
    }

    pub const fn chi(self) -> Option<Chi> {
        self.chi
    }
}

/// Actual shared-interface witness plus the complete pair of paths being compared there.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceWitness {
    capability: InterfaceCapability,
    comparison: ParallelPathComparison,
}

impl InterfaceWitness {
    pub fn capability(&self) -> InterfaceCapability {
        self.capability.clone()
    }

    pub const fn comparison(&self) -> ParallelPathComparison {
        self.comparison
    }
}

impl FormedPin {
    pub const fn position(self) -> Place {
        self.position
    }

    pub const fn chi(self) -> Chi {
        self.chi
    }

    pub const fn winding(self) -> WindingQuantum {
        self.winding
    }

    pub const fn deed(self) -> FeltDeed {
        self.deed
    }
}

/// One actual receiver-relative crossing or exposed-path comparison. Its complete local routes and
/// any projective residual can remain live without a formed deed. A material contact may RIDE or
/// FOUND; a path comparison forms only when it commutes and therefore can only RIDE. The receiver
/// lineage, source endpoints, standing receipt, and event row have already departed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LivePin {
    meeting: Face,
    held: Face,
    held_live: bool,
    interface: Option<InterfaceCapability>,
    projected_residual: Option<Chi>,
    formed: Option<FormedPin>,
}

impl LivePin {
    pub fn from_contact(contact: DirectedEventContact) -> Self {
        let projected_residual = contact.emission.map(|emission| emission.term.chi);
        Self {
            meeting: contact.meeting,
            held: contact.receiver.held,
            held_live: contact.receiver.held_live,
            interface: None,
            projected_residual,
            formed: contact.emission.map(|emission| FormedPin {
                position: emission.position,
                chi: emission.term.chi,
                winding: emission.term.winding,
                deed: emission.deed,
            }),
        }
    }

    /// One actual regional crossing carrying the source's interface capability into the live
    /// boundary. Internal contact pins deliberately have no such capability and cannot later join
    /// merely because their projected geometry happens to agree.
    pub fn from_interface_contact(
        contact: DirectedEventContact,
        interface: InterfaceCapability,
    ) -> Self {
        let mut pin = Self::from_contact(contact);
        pin.interface = Some(interface);
        pin
    }

    pub const fn meeting(&self) -> Face {
        self.meeting
    }

    pub const fn held(&self) -> Face {
        self.held
    }

    pub const fn held_live(&self) -> bool {
        self.held_live
    }

    pub const fn formed(&self) -> Option<FormedPin> {
        self.formed
    }

    pub fn interface(&self) -> Option<InterfaceCapability> {
        self.interface.clone()
    }

    pub const fn comparison(&self) -> ParallelPathComparison {
        ParallelPathComparison {
            through: self.meeting,
            direct: self.held,
            chi: self.projected_residual,
        }
    }

    pub const fn is_open(&self) -> bool {
        self.formed.is_none()
    }

    pub fn is_found(&self) -> bool {
        self.formed
            .is_some_and(|formed| matches!(formed.deed, FeltDeed::FoundThis | FeltDeed::FoundThat))
    }

    /// Projectively rebased position of this actual crossing. This is the consequential local
    /// axis key which can recur after the event's meeting and held-frame coordinates have
    /// changed. It is absent for an open fourth contact; equality here is a receiver-relative
    /// transport class, not equality of source events.
    pub const fn transport_position(&self) -> Option<Place> {
        match self.formed {
            Some(formed) => Some(formed.position),
            None => None,
        }
    }

    pub fn interface_witness(arriving: &Self, held: &Self) -> Option<InterfaceWitness> {
        let capability = arriving.interface.as_ref()?;
        if held.interface.as_ref() != Some(capability) {
            return None;
        }
        Some(InterfaceWitness {
            capability: capability.clone(),
            comparison: ParallelPathComparison::new(arriving.meeting, held.meeting),
        })
    }

    /// Form the cross-event local chart change only through an actual shared interface
    /// capability. The complete paths remain in `ParallelPathComparison`; Chi is one available
    /// projection. A horizon therefore remains an OPEN joined interface rather than disappearing.
    fn rebase_exposed(
        arriving: &Self,
        held: &Self,
        hand_residual: Option<IncidenceHand>,
    ) -> Option<Self> {
        let witness = Self::interface_witness(arriving, held)?;
        let projected_residual = witness.comparison.chi();
        // WHY A SEAM DOES NOT RIDE. Three conditions block it and only one can be repaired by
        // anything upstream; counted so the reading is measured rather than inferred.
        match projected_residual {
            None => {
                // WHICH SIDE IS THE HORIZON. `chi_against` returns None only when a face's arrow has
                // BOTH aim and cross zero — `arms_form` admits ORTHO, so this is not the eyes-only
                // crime. It means the compared face carries no geometry at all.
                let arriving_null =
                    arriving.meeting.arrow.aim.mag == 0 && arriving.meeting.arrow.cross.mag == 0;
                let held_null =
                    held.meeting.arrow.aim.mag == 0 && held.meeting.arrow.cross.mag == 0;
                if arriving.meeting.arrow.reach.mag == 0 {
                    ZERO_REACH.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
                }
                match (arriving_null, held_null) {
                    (true, true) => BOTH_NULL.fetch_add(1, core::sync::atomic::Ordering::Relaxed),
                    (true, false) => {
                        ARRIVING_NULL.fetch_add(1, core::sync::atomic::Ordering::Relaxed)
                    }
                    (false, true) => HELD_NULL.fetch_add(1, core::sync::atomic::Ordering::Relaxed),
                    (false, false) => 0,
                };
                NO_PROJECTIVE_READ.fetch_add(1, core::sync::atomic::Ordering::Relaxed)
            }
            Some(chi) if chi.wound() => {
                WOUND_COMPARISON.fetch_add(1, core::sync::atomic::Ordering::Relaxed)
            }
            Some(_) if hand_residual.is_some() => {
                HAND_RESIDUAL.fetch_add(1, core::sync::atomic::Ordering::Relaxed)
            }
            Some(_) => RODE.fetch_add(1, core::sync::atomic::Ordering::Relaxed),
        };
        // This is a comparison between already-exposed paths, not a fresh material contact.
        // Agreement can RIDE. A wound comparison, an oriented hand residual, or an unavailable
        // projective read remains OPEN with its complete pair; it cannot manufacture a FOUND.
        let formed = projected_residual.and_then(|chi| {
            (!chi.wound() && hand_residual.is_none()).then_some(FormedPin {
                position: cast_position(chi),
                chi,
                winding: WindingQuantum::None,
                deed: FeltDeed::Ride,
            })
        });
        Some(Self {
            meeting: arriving.meeting,
            held: held.meeting,
            held_live: true,
            interface: Some(witness.capability),
            projected_residual,
            formed,
        })
    }

    fn factor(&self, support: LocalAxis) -> SparseTransport {
        self.projected_residual
            .map_or_else(SparseTransport::identity, |chi| {
                SparseTransport::factor(chi, support)
            })
    }

    /// Exact canonical words for transient pin indexing. This is the same representation used by
    /// the durable constituent wire, but it carries no chronology or identity beyond the pin
    /// itself. Regional formation uses it only to recover an already-inserted equal pin without a
    /// linear scan through the growing cell.
    pub(crate) fn exact_words(&self) -> Vec<u32> {
        let fiber_words = self.interface.as_ref().map_or(0, |interface| {
            interface
                .receiver_fiber
                .as_ref()
                .map_or(0, |(left, right)| {
                    left.words.len().saturating_add(right.words.len())
                })
        });
        let mut words = Vec::with_capacity(STRUCTURAL_PIN_FIXED_WORDS.saturating_add(fiber_words));
        words.push(u32::from(self.formed.is_some()));
        for word in 0..FACE_WORDS {
            words.push(face_packed_word(self.meeting, word));
        }
        for word in 0..FACE_WORDS {
            words.push(face_packed_word(self.held, word));
        }
        words.push(u32::from(self.held_live));
        words.push(u32::from(self.interface.is_some()));
        let absent_interface = InterfaceCapability::new(0, 0);
        let interface = self.interface.as_ref().unwrap_or(&absent_interface);
        words.push(interface_origin_word(interface.origin));
        push_u64(&mut words, interface.namespace);
        push_u64(&mut words, interface.local);
        words.push(u32::from(interface.receiver_fiber.is_some()));
        match interface.receiver_fiber.as_ref() {
            Some((antecedent_fiber, consequent_fiber)) => {
                push_receiver_fiber(&mut words, Some(antecedent_fiber));
                push_receiver_fiber(&mut words, Some(consequent_fiber));
            }
            None => {
                push_receiver_fiber(&mut words, None);
                push_receiver_fiber(&mut words, None);
            }
        }
        words.push(u32::from(self.projected_residual.is_some()));
        let projected_residual = self.projected_residual.unwrap_or(Chi {
            other: Cog::ZERO,
            same: Cog::ZERO,
        });
        push_cog(&mut words, projected_residual.other);
        push_cog(&mut words, projected_residual.same);
        let formed = self.formed.unwrap_or(FormedPin {
            position: (Cog::ZERO, Cog::ZERO),
            chi: Chi {
                other: Cog::ZERO,
                same: Cog::ZERO,
            },
            winding: WindingQuantum::None,
            deed: FeltDeed::Dark,
        });
        push_cog(&mut words, formed.position.0);
        push_cog(&mut words, formed.position.1);
        push_cog(&mut words, formed.chi.other);
        push_cog(&mut words, formed.chi.same);
        words.push(winding_word(formed.winding));
        words.push(deed_word(formed.deed));
        debug_assert_eq!(
            words.len(),
            STRUCTURAL_PIN_FIXED_WORDS.saturating_add(fiber_words)
        );
        words
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LiveCell {
    dependency_rank: u32,
    dimension: u32,
    grain: u32,
}

impl LiveCell {
    pub const fn new(dependency_rank: u32, dimension: u32, grain: u32) -> Self {
        Self {
            dependency_rank,
            dimension,
            grain,
        }
    }

    pub const fn dependency_rank(self) -> u32 {
        self.dependency_rank
    }

    pub const fn dimension(self) -> u32 {
        self.dimension
    }

    pub const fn grain(self) -> u32 {
        self.grain
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum LiveIncidenceKind {
    Boundary,
    Dependency,
    Transport,
    RewriteInterface,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LiveIncidence {
    from: u32,
    to: u32,
    kind: LiveIncidenceKind,
    hand: IncidenceHand,
    pin: u32,
}

impl LiveIncidence {
    pub const fn new(
        from: u32,
        to: u32,
        kind: LiveIncidenceKind,
        hand: IncidenceHand,
        pin: u32,
    ) -> Self {
        Self {
            from,
            to,
            kind,
            hand,
            pin,
        }
    }

    pub const fn from(self) -> u32 {
        self.from
    }

    pub const fn to(self) -> u32 {
        self.to
    }

    pub const fn kind(self) -> LiveIncidenceKind {
        self.kind
    }

    pub const fn hand(self) -> IncidenceHand {
        self.hand
    }

    pub const fn pin(self) -> u32 {
        self.pin
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LivePathStep {
    incidence: u32,
    support: LocalAxis,
    winding: WindingQuantum,
}

impl LivePathStep {
    pub const fn new(incidence: u32, support: LocalAxis, winding: WindingQuantum) -> Self {
        Self {
            incidence,
            support,
            winding,
        }
    }

    pub const fn incidence(self) -> u32 {
        self.incidence
    }

    pub const fn support(self) -> LocalAxis {
        self.support
    }

    pub const fn winding(self) -> WindingQuantum {
        self.winding
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LivePath {
    steps: Vec<LivePathStep>,
    transport: SparseTransport,
    this_way: Rung,
    that_way: Rung,
    interior_folded: bool,
}

impl LivePath {
    pub fn from_steps(
        steps: Vec<LivePathStep>,
        incidences: &[LiveIncidence],
        pins: &[LivePin],
    ) -> Result<Self, LiveConstituentError> {
        let (transport, this_way, that_way) = path_emanation(&steps, incidences, pins)?;
        Ok(Self {
            steps,
            transport,
            this_way,
            that_way,
            interior_folded: false,
        })
    }

    /// Replace completed lower interior steps by their already-formed path transport. The retained
    /// steps are precisely the pins still needed by exposed boundary, sharing, open residual, or
    /// cycle topology; `transport` remains the complete ordered product formed before departure.
    pub fn fold_interior(self, steps: Vec<LivePathStep>) -> Self {
        Self {
            interior_folded: self.interior_folded || steps != self.steps,
            steps,
            transport: self.transport,
            this_way: self.this_way,
            that_way: self.that_way,
        }
    }

    pub fn steps(&self) -> &[LivePathStep] {
        &self.steps
    }

    pub const fn transport(&self) -> &SparseTransport {
        &self.transport
    }

    pub const fn interior_folded(&self) -> bool {
        self.interior_folded
    }

    pub const fn this_way(&self) -> Rung {
        self.this_way
    }

    pub const fn that_way(&self) -> Rung {
        self.that_way
    }

    fn rebased(
        &self,
        incidence_offset: u32,
        axes: &[LocalAxis],
    ) -> Result<Self, LiveConstituentError> {
        let mut steps = Vec::new();
        steps
            .try_reserve_exact(self.steps.len())
            .map_err(|_| LiveConstituentError::Extent)?;
        for step in &self.steps {
            steps.push(LivePathStep::new(
                step.incidence
                    .checked_add(incidence_offset)
                    .ok_or(LiveConstituentError::Extent)?,
                *axes
                    .get(word_usize(step.support.local())?)
                    .ok_or(LiveConstituentError::Algebra)?,
                step.winding,
            ));
        }
        Ok(Self {
            steps,
            transport: self.transport.rebased(axes)?,
            this_way: self.this_way,
            that_way: self.that_way,
            interior_folded: self.interior_folded,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiveBoundary {
    hand: IncidenceHand,
    paths: Vec<LivePath>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LiveBoundaryTransition {
    Open,
    Ride,
    Found,
}

#[derive(Clone, Copy)]
struct ExposedArm {
    boundary: usize,
    path: usize,
    step: usize,
    incidence: usize,
    pin: usize,
    hand: IncidenceHand,
}

struct IndexedExposedArms {
    #[cfg(test)]
    ordered: Vec<ExposedArm>,
    #[cfg(test)]
    by_interface: BTreeMap<InterfaceCapability, Vec<ExposedArm>>,
    by_section: Vec<Vec<ExposedArm>>,
    sections_by_interface: BTreeMap<InterfaceCapability, Vec<usize>>,
}

/// Rebuildable, non-causal aperture from a standing boundary capability to the constituents
/// which actually expose it.  The aperture may expose possible temporal contacts; it cannot
/// establish one.  Every candidate still crosses the complete support-cover and
/// [`LivePin::rebase_exposed`] laws before it may affect Standing.
///
/// This structure is deliberately absent from constituent identity and native rest wires.  A
/// remounted machine rebuilds it from the exact standing face.
#[derive(Clone, Debug)]
pub(crate) struct StandingIncidenceAperture {
    by_interface: BTreeMap<InterfaceCapability, Vec<u64>>,
    identity_by_key: BTreeMap<Arc<[u32]>, u64>,
    factors: BTreeMap<u64, StandingApertureFactor>,
    next_identity: u64,
    /// The chronology a candidate must cross this aperture within — **declared by whoever builds
    /// the aperture, never authored here**, and deliberately absent from equality below because a
    /// horizon is a receiver declaration over a standing rather than part of the caused body.
    ///
    /// `u64::MAX` is the inherited setting and admits everything, so nothing moves until a caller
    /// declares one. See [`Self::declare_traversal_horizon`].
    traversal_horizon: u64,
    /// How many propagation hops a front may be informed across — its **vision**. `u32::MAX` is the
    /// inherited setting and bounds nothing.
    vision_horizon: u32,
    #[cfg(test)]
    exhaustive: bool,
}

impl Default for StandingIncidenceAperture {
    fn default() -> Self {
        Self {
            by_interface: BTreeMap::new(),
            identity_by_key: BTreeMap::new(),
            factors: BTreeMap::new(),
            next_identity: 0,
            traversal_horizon: u64::MAX,
            vision_horizon: u32::MAX,
            #[cfg(test)]
            exhaustive: false,
        }
    }
}

impl PartialEq for StandingIncidenceAperture {
    fn eq(&self, other: &Self) -> bool {
        #[cfg(test)]
        if self.exhaustive != other.exhaustive {
            return false;
        }
        self.identity_by_key.len() == other.identity_by_key.len()
            && self.identity_by_key.iter().all(|(key, identity)| {
                let Some(other_identity) = other.identity_by_key.get(key) else {
                    return false;
                };
                let Some(left) = self.factors.get(identity) else {
                    return false;
                };
                let Some(right) = other.factors.get(other_identity) else {
                    return false;
                };
                left.key == right.key
                    && left.multiplicity == right.multiplicity
                    && left.interfaces == right.interfaces
            })
    }
}

impl Eq for StandingIncidenceAperture {}

/// A standing factor the junction dilated past the aperture's declared horizon.
///
/// Retained rather than dropped. A rank is only meaningful against the population that did not
/// connect, and a closure that silently declined half its candidates has deleted the null every
/// reading over it is taken against.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DeferredFactor {
    pub(crate) identity: u64,
    /// The factor's multiplicity — what standing offered.
    pub(crate) offered: usize,
    /// How wide the arriving front was on this factor's interfaces.
    pub(crate) arriving: u64,
    /// `⌈(R+M)²/(4RM)⌉` — what the crossing would have cost.
    pub(crate) service_rounds: u128,
}

/// How far a front has already propagated, and how many co-present fronts are asking.
///
/// **Vision is physical, not declared.** `canon/THE_TRAFFIC_SYSTEM.md` §3b: a unit is informed only
/// about what has reached it. `front_depth` — already carried on every active part and incremented
/// each time a front reaches standing — is exactly that propagation depth, and until 2026-08-15
/// nothing bounded it, so a front could be informed about material arbitrarily far from it.
///
/// `co_present` is the demand side of the traffic law: how many fronts are asking at once.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FrontVision {
    /// How many hops the front has already travelled.
    pub(crate) depth: u32,
    /// The declared horizon on that depth. `u32::MAX` is the inherited setting and bounds nothing.
    pub(crate) horizon: u32,
    /// How many co-present fronts are asking this round.
    pub(crate) co_present: u64,
}

impl FrontVision {
    /// The inherited reading: unbounded depth, one asking front. Nothing moves under it.
    #[cfg(test)]
    pub(crate) const fn unbounded() -> Self {
        Self {
            depth: 0,
            horizon: u32::MAX,
            co_present: 1,
        }
    }

    /// Whether the front may be informed about anything one hop further out.
    pub(crate) const fn admits_another_hop(self) -> bool {
        self.depth < self.horizon
    }
}

/// What an aperture admitted, and what it deferred. Both halves are returned; neither is a count.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub(crate) struct AdmittedCandidates {
    pub(crate) admitted: Vec<usize>,
    pub(crate) deferred: Vec<DeferredFactor>,
}

/// One exact structural standing class behind a compact aperture-local identity. The identity is
/// only a rebuildable address: the complete native key remains the grading authority.
#[derive(Clone, Debug, PartialEq, Eq)]
struct StandingApertureFactor {
    key: Arc<[u32]>,
    multiplicity: usize,
    interfaces: Arc<[InterfaceCapability]>,
}

/// Exact ordered access required by the local Swing closure. Production Standing implements this
/// through its persistent structural tree; borrowed slices implement it for bounded construction
/// and parity tests. The closure never requires a materialized successor-wide vector.
pub(crate) trait StandingConstituentAccess {
    fn standing_len(&self) -> usize;
    fn standing_get(&self, ordinal: usize) -> Option<&LiveConstituent>;
    fn standing_key_at(&self, ordinal: usize) -> Result<Arc<[u32]>, LiveConstituentError>;
    fn standing_key_range(&self, key: &[u32]) -> Result<Range<usize>, LiveConstituentError>;
}

impl StandingConstituentAccess for [LiveConstituent] {
    fn standing_len(&self) -> usize {
        self.len()
    }

    fn standing_get(&self, ordinal: usize) -> Option<&LiveConstituent> {
        self.get(ordinal)
    }

    fn standing_key_at(&self, ordinal: usize) -> Result<Arc<[u32]>, LiveConstituentError> {
        Ok(self
            .get(ordinal)
            .ok_or(LiveConstituentError::Topology)?
            .native_words()?
            .into())
    }

    fn standing_key_range(&self, key: &[u32]) -> Result<Range<usize>, LiveConstituentError> {
        standing_slice_key_range(self, key)
    }
}

impl StandingConstituentAccess for Vec<LiveConstituent> {
    fn standing_len(&self) -> usize {
        self.as_slice().standing_len()
    }

    fn standing_get(&self, ordinal: usize) -> Option<&LiveConstituent> {
        self.as_slice().standing_get(ordinal)
    }

    fn standing_key_at(&self, ordinal: usize) -> Result<Arc<[u32]>, LiveConstituentError> {
        self.as_slice().standing_key_at(ordinal)
    }

    fn standing_key_range(&self, key: &[u32]) -> Result<Range<usize>, LiveConstituentError> {
        self.as_slice().standing_key_range(key)
    }
}

impl StandingIncidenceAperture {
    pub(crate) fn from_standing<S>(standing: &S) -> Result<Self, LiveConstituentError>
    where
        S: StandingConstituentAccess + ?Sized,
    {
        let mut aperture = Self::default();
        for ordinal in 0..standing.standing_len() {
            let body = standing
                .standing_get(ordinal)
                .ok_or(LiveConstituentError::Topology)?;
            aperture.insert_with_key(body, standing.standing_key_at(ordinal)?)?;
        }
        Ok(aperture)
    }

    /// Carry the non-causal aperture across one already-validated atomic standing change. Only
    /// touched factors and their replacements are visited. Exact standing identity, not a vector
    /// address, carries the aperture through canonical storage reordering.
    pub(crate) fn after_replacements<'a, S>(
        &self,
        standing_before: &S,
        replacements: impl IntoIterator<Item = (&'a [usize], &'a LiveConstituent)>,
    ) -> Result<Self, LiveConstituentError>
    where
        S: StandingConstituentAccess + ?Sized,
    {
        let mut after = self.clone();
        for (touched, replacement) in replacements {
            for at in touched {
                after.remove_with_key(
                    standing_before
                        .standing_get(*at)
                        .ok_or(LiveConstituentError::Topology)?,
                    standing_before.standing_key_at(*at)?,
                )?;
            }
            after.insert(replacement)?;
        }
        Ok(after)
    }

    #[cfg(test)]
    fn candidates<S>(
        &self,
        active: &[IndexedExposedArms],
        claimed: &[usize],
        standing: &S,
    ) -> Result<Vec<usize>, LiveConstituentError>
    where
        S: StandingConstituentAccess + ?Sized,
    {
        Ok(self
            .candidates_for_interfaces(
                active
                    .iter()
                    .flat_map(|arms| arms.by_interface.keys().cloned()),
                claimed,
                standing,
                FrontVision::unbounded(),
            )?
            .admitted)
    }

    fn candidates_for_interfaces<S>(
        &self,
        interfaces: impl IntoIterator<Item = InterfaceCapability>,
        claimed: &[usize],
        standing: &S,
        vision: FrontVision,
    ) -> Result<AdmittedCandidates, LiveConstituentError>
    where
        S: StandingConstituentAccess + ?Sized,
    {
        #[cfg(test)]
        if self.exhaustive {
            return Ok(AdmittedCandidates {
                admitted: (0..standing.standing_len())
                    .filter(|at| claimed.binary_search(at).is_err())
                    .collect(),
                deferred: Vec::new(),
            });
        }

        // How wide the arriving front is on each interface. The incident population of the junction
        // below, and it comes from the material rather than from a declaration.
        let mut arriving_width = BTreeMap::<InterfaceCapability, usize>::new();
        let mut identities = BTreeSet::new();
        for interface in interfaces {
            *arriving_width.entry(interface.clone()).or_insert(0) += 1;
            if let Some(exposed) = self.by_interface.get(&interface) {
                identities.extend(exposed.iter().copied());
            }
        }

        // THE JUNCTION, 2026-08-15. Every standing factor exposing any shared interface used to be
        // admitted WHOLE, at full multiplicity, every round of the closure below — and because each
        // admitted factor exposes further interfaces, the next round pulled more. That cascade is
        // what a three-junction drain costing 12.9 s over a 477-clause standing actually was.
        //
        // A factor is a junction. What arrives carries a width on an interface; what the factor
        // offers is its multiplicity; the crossing costs `⌈(R+M)²/(4RM)⌉` passes, one at a match and
        // more as they separate. What dilates past the declared horizon **defers** — retained by
        // name with its exact cost — and is never dropped.
        //
        // A factor replicated five hundred times meeting a front of two is an impedance mismatch,
        // and admitting it whole is the same defect as a leader star with no aperture. The law is
        // `holonic_structure::CountedCrossing`, shared with the transport carrier that computes it
        // over exact rationals.
        let mut candidates = Vec::new();
        let mut deferred = Vec::new();
        for identity in identities {
            let factor = self
                .factors
                .get(&identity)
                .ok_or(LiveConstituentError::Topology)?;
            let range = standing.standing_key_range(&factor.key)?;
            if range.end - range.start != factor.multiplicity {
                return Err(LiveConstituentError::Topology);
            }
            // CONSTRUCTION 3 — VISION. A front is informed only about what has propagated to it,
            // and `front_depth` is exactly how many hops from the arriving current a part already
            // sits. A front that has already reached its declared depth admits nothing further: it
            // cannot be informed about what is beyond it, which is the traffic law's own clause —
            // *"they physically cannot be informed about vehicles not within their vision."*
            if !vision.admits_another_hop() {
                deferred.push(DeferredFactor {
                    identity,
                    offered: factor.multiplicity,
                    arriving: 0,
                    service_rounds: 0,
                });
                continue;
            }
            // CONSTRUCTION 2 — PREDICTED CONTENTION. How many co-present fronts want this factor,
            // against what it offers. This is `receiver_current`'s congestion law at the seam:
            // demand over capacity, dilating rather than refusing, with the overflow retained.
            let contending = u64::try_from(
                factor
                    .interfaces
                    .iter()
                    .filter(|interface| arriving_width.contains_key(*interface))
                    .count(),
            )
            .map_err(|_| LiveConstituentError::Extent)?;
            if let Some(contention) = CountedCrossing::meet(
                contending.saturating_mul(vision.co_present),
                u64::try_from(factor.multiplicity).map_err(|_| LiveConstituentError::Extent)?,
            ) {
                if !contention.crosses_within(self.traversal_horizon) {
                    deferred.push(DeferredFactor {
                        identity,
                        offered: factor.multiplicity,
                        arriving: contending,
                        service_rounds: contention.service_rounds(),
                    });
                    continue;
                }
            }
            let arriving = u64::try_from(
                factor
                    .interfaces
                    .iter()
                    .filter_map(|interface| arriving_width.get(interface))
                    .copied()
                    .max()
                    .unwrap_or(0),
            )
            .map_err(|_| LiveConstituentError::Extent)?;
            let offered =
                u64::try_from(factor.multiplicity).map_err(|_| LiveConstituentError::Extent)?;
            match CountedCrossing::meet(arriving, offered) {
                Some(crossing) if !crossing.crosses_within(self.traversal_horizon) => {
                    deferred.push(DeferredFactor {
                        identity,
                        offered: factor.multiplicity,
                        arriving,
                        service_rounds: crossing.service_rounds(),
                    });
                    continue;
                }
                // Matched or within the horizon: the current crosses whole.
                Some(_) => {}
                // Nothing arrives on any of this factor's interfaces. There is no traveling
                // section, which is a terminus by type rather than a comparison — and it cannot
                // arise here, because the factor was reached through an interface that something
                // exposed. Kept as a branch so the impossibility is stated rather than assumed.
                None => continue,
            }
            candidates
                .try_reserve(range.end - range.start)
                .map_err(|_| LiveConstituentError::Extent)?;
            candidates.extend(range);
        }
        candidates.sort_unstable();
        candidates.dedup();
        candidates.retain(|at| claimed.binary_search(at).is_err());
        Ok(AdmittedCandidates {
            admitted: candidates,
            deferred,
        })
    }

    /// The chronology declared over this aperture.
    pub(crate) const fn traversal_horizon(&self) -> u64 {
        self.traversal_horizon
    }

    /// How many propagation hops a front may be informed across. `u32::MAX` bounds nothing.
    pub(crate) const fn vision_horizon(&self) -> u32 {
        self.vision_horizon
    }

    /// Declare the front's vision — how far a signal may have propagated and still inform it.
    ///
    /// Strictly additive: the inherited setting is `u32::MAX`, under which nothing moves.
    pub(crate) const fn declare_vision_horizon(&mut self, horizon: u32) {
        self.vision_horizon = horizon;
    }

    /// Declare the chronology a candidate must cross this aperture within.
    ///
    /// The inherited setting is `u64::MAX`, which admits everything — so this is strictly additive
    /// and nothing moves until a caller declares a finite horizon.
    pub(crate) const fn declare_traversal_horizon(&mut self, horizon: u64) {
        self.traversal_horizon = horizon;
    }

    fn insert(&mut self, body: &LiveConstituent) -> Result<(), LiveConstituentError> {
        let key: Arc<[u32]> = body.native_words()?.into();
        self.insert_with_key(body, key)
    }

    fn insert_with_key(
        &mut self,
        body: &LiveConstituent,
        key: Arc<[u32]>,
    ) -> Result<(), LiveConstituentError> {
        if let Some(identity) = self.identity_by_key.get(&key).copied() {
            let factor = self
                .factors
                .get_mut(&identity)
                .ok_or(LiveConstituentError::Topology)?;
            factor.multiplicity = factor
                .multiplicity
                .checked_add(1)
                .ok_or(LiveConstituentError::Extent)?;
            return Ok(());
        }

        // Every admitted constituent has already certified its complete exposed boundary.
        // The aperture needs only those exact capabilities; rebuilding a support-cover factor
        // here would refactor the same body after every local standing replacement.
        let interfaces: Arc<[InterfaceCapability]> = body.exposed_interfaces()?.into();
        let identity = self.next_identity;
        self.next_identity = self
            .next_identity
            .checked_add(1)
            .ok_or(LiveConstituentError::Extent)?;
        for interface in interfaces.iter().cloned() {
            let keys = self.by_interface.entry(interface).or_default();
            match keys.binary_search(&identity) {
                Ok(_) => return Err(LiveConstituentError::Topology),
                Err(at) => keys.insert(at, identity),
            }
        }
        self.identity_by_key.insert(key.clone(), identity);
        self.factors.insert(
            identity,
            StandingApertureFactor {
                key,
                multiplicity: 1,
                interfaces,
            },
        );
        Ok(())
    }

    fn remove_with_key(
        &mut self,
        body: &LiveConstituent,
        key: Arc<[u32]>,
    ) -> Result<(), LiveConstituentError> {
        let identity = *self
            .identity_by_key
            .get(&key)
            .ok_or(LiveConstituentError::Topology)?;
        let factor = self
            .factors
            .get_mut(&identity)
            .ok_or(LiveConstituentError::Topology)?;
        if factor.multiplicity > 1 {
            factor.multiplicity -= 1;
            return Ok(());
        }

        let factor = self
            .factors
            .remove(&identity)
            .ok_or(LiveConstituentError::Topology)?;
        if factor.interfaces.as_ref() != body.exposed_interfaces()?.as_slice()
            || self.identity_by_key.remove(&factor.key) != Some(identity)
        {
            return Err(LiveConstituentError::Topology);
        }
        for interface in factor.interfaces.iter() {
            let keys = self
                .by_interface
                .get_mut(interface)
                .ok_or(LiveConstituentError::Topology)?;
            let at = keys
                .binary_search(&identity)
                .map_err(|_| LiveConstituentError::Topology)?;
            keys.remove(at);
            if keys.is_empty() {
                self.by_interface.remove(interface);
            }
        }
        Ok(())
    }

    #[cfg(test)]
    fn exhaustive() -> Self {
        Self {
            exhaustive: true,
            ..Self::default()
        }
    }
}

fn standing_slice_key_range(
    standing: &[LiveConstituent],
    key: &[u32],
) -> Result<Range<usize>, LiveConstituentError> {
    fn boundary(
        standing: &[LiveConstituent],
        key: &[u32],
        upper: bool,
    ) -> Result<usize, LiveConstituentError> {
        let mut left = 0usize;
        let mut right = standing.len();
        while left < right {
            let middle = left + (right - left) / 2;
            let words = standing[middle].native_words()?;
            let goes_left = if upper {
                words.as_slice() <= key
            } else {
                words.as_slice() < key
            };
            if goes_left {
                left = middle + 1;
            } else {
                right = middle;
            }
        }
        Ok(left)
    }

    let start = boundary(standing, key, false)?;
    let end = boundary(standing, key, true)?;
    if start == end {
        return Err(LiveConstituentError::Topology);
    }
    Ok(start..end)
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct BoundaryPathBehavior {
    transport: SparseTransport,
    this_way: Rung,
    that_way: Rung,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ExposedArmBehavior {
    interface: InterfaceCapability,
    comparison: ParallelPathComparison,
    held_live: bool,
    formed: Option<FormedPin>,
    hand: IncidenceHand,
    from: LiveCell,
    to: LiveCell,
    support: LocalAxis,
}

/// Exact finite family of observations the built-in outgoing compression promises to preserve.
/// It is deliberately limited to what a genuinely later regional contact and the public boundary
/// can use for genuinely later regional contact: constituent scale, local axes, path
/// transports/winding, boundary transition, and every complete exposed interface arm with its
/// situated endpoints. Interior representation details which the emanation intentionally folds
/// are outside this family.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundaryBehavior {
    grain: u32,
    axis_count: u32,
    paths: Vec<(
        IncidenceHand,
        LiveBoundaryTransition,
        Vec<BoundaryPathBehavior>,
    )>,
    exposed: Vec<ExposedArmBehavior>,
    support: LiveSupportFamily,
}

impl BoundaryBehavior {
    pub const fn grain(&self) -> u32 {
        self.grain
    }

    pub const fn axis_count(&self) -> u32 {
        self.axis_count
    }

    pub fn boundary_count(&self) -> usize {
        self.paths.len()
    }

    pub fn exposed_arm_count(&self) -> usize {
        self.exposed.len()
    }

    pub const fn support_family(&self) -> &LiveSupportFamily {
        &self.support
    }

    pub fn support_sections(&self) -> Vec<LiveSupportSection> {
        self.support
            .explicit_sections()
            .expect("validated boundary behavior has finite active support roots")
    }
}

/// Ephemeral proof object produced at the same call that emits a compressed successor. Equality
/// is structural over [`BoundaryBehavior`], not a digest or scalar score. The count delta is
/// testimony about departed interior only and has no causal role.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompressionCertificate {
    behavior: BoundaryBehavior,
    before_cells: usize,
    after_cells: usize,
    before_incidences: usize,
    after_incidences: usize,
}

impl CompressionCertificate {
    pub const fn behavior(&self) -> &BoundaryBehavior {
        &self.behavior
    }

    pub const fn before_cells(&self) -> usize {
        self.before_cells
    }

    pub const fn after_cells(&self) -> usize {
        self.after_cells
    }

    pub const fn before_incidences(&self) -> usize {
        self.before_incidences
    }

    pub const fn after_incidences(&self) -> usize {
        self.after_incidences
    }
}

#[cfg(test)]
#[allow(dead_code)]
#[derive(Clone)]
struct RegionalSeam {
    prior: usize,
    prior_arm: ExposedArm,
    arriving_arm: ExposedArm,
    pin: LivePin,
}

struct ConstituentPartMap {
    cell_offset: u32,
    pin_offset: u32,
    boundary_offset: u32,
    axes: Vec<LocalAxis>,
}

/// Event-transient identity of one source occurrence shared by several regional cofaces. This key
/// is consumed while the one contemporary occurrence population is assembled; committed
/// Standing carries the sharing directly as common cell ordinals and never retains the key.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct SharedOccurrenceKey {
    species: u8,
    owner: u64,
    local: u64,
}

impl SharedOccurrenceKey {
    pub(crate) const fn new(species: u8, owner: u64, local: u64) -> Self {
        Self {
            species,
            owner,
            local,
        }
    }
}

/// One connected component of the complete arriving regional population after every presently
/// afforded co-present and temporal seam has closed. `members` addresses only the borrowed
/// arriving population; `touched` addresses immutable Standing-before. Both disappear at commit.
pub(crate) struct PopulationClosure {
    members: Vec<usize>,
    touched: Vec<usize>,
    replacement: LiveConstituent,
    section_lineages: Vec<BTreeSet<PopulationSectionOrigin>>,
    front_depth: u32,
}

impl PopulationClosure {
    pub(crate) fn members(&self) -> &[usize] {
        &self.members
    }

    pub(crate) fn touched(&self) -> &[usize] {
        &self.touched
    }

    pub(crate) const fn replacement(&self) -> &LiveConstituent {
        &self.replacement
    }

    pub(crate) fn section_lineages(&self) -> &[BTreeSet<PopulationSectionOrigin>] {
        &self.section_lineages
    }

    /// Number of successive standing-local fronts crossed after the arriving population. Depth
    /// zero means no prior standing constituent was reached. This is immediate propagation
    /// testimony only; it never enters standing identity or persistence.
    pub(crate) const fn front_depth(&self) -> u32 {
        self.front_depth
    }
}

/// Event-transient address of one declared incoming support section. It exists only so immediate
/// radiation can report which exact local support returned OPEN, RIDE, or FOUND after the complete
/// co-present population closed. It never enters Standing or native persistence.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct PopulationSectionOrigin {
    member: usize,
    section: usize,
}

impl PopulationSectionOrigin {
    pub(crate) const fn new(member: usize, section: usize) -> Self {
        Self { member, section }
    }
}

#[derive(Clone)]
struct ActivePopulationPart {
    members: Vec<usize>,
    touched: Vec<usize>,
    body: LiveConstituent,
    section_lineages: Vec<BTreeSet<PopulationSectionOrigin>>,
    front_depth: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PopulationPartOrigin {
    Active(usize),
    Standing(usize),
}

#[derive(Clone)]
struct PopulationPart {
    origin: PopulationPartOrigin,
    body: LiveConstituent,
    section_lineages: Vec<BTreeSet<PopulationSectionOrigin>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct PopulationSectionLink {
    group: usize,
    left: usize,
    right: usize,
}

#[derive(Clone)]
struct PopulationSeam {
    left: usize,
    right: usize,
    left_arm: ExposedArm,
    right_arm: ExposedArm,
    pin: LivePin,
    section_links: Vec<PopulationSectionLink>,
}

struct TemporalSectionCandidate {
    standing: usize,
    held_section: usize,
    matches: Vec<(ExposedArm, ExposedArm, LivePin)>,
    arriving_boundaries: Vec<usize>,
}

impl LiveBoundary {
    pub fn new(hand: IncidenceHand, paths: Vec<LivePath>) -> Self {
        Self { hand, paths }
    }

    pub const fn hand(&self) -> IncidenceHand {
        self.hand
    }

    pub fn paths(&self) -> &[LivePath] {
        &self.paths
    }
}

/// One completed higher-grain live constituent. Its point face, if requested by an observer, is
/// only a projection of this body and is deliberately absent from the causal representation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiveConstituent {
    grain: u32,
    axis_count: u32,
    cells: Vec<LiveCell>,
    incidences: Vec<LiveIncidence>,
    pins: Vec<LivePin>,
    boundaries: Vec<LiveBoundary>,
    exposed: Vec<u32>,
    support: LiveSupportFamily,
}

impl LiveConstituent {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        grain: u32,
        axis_count: u32,
        cells: Vec<LiveCell>,
        incidences: Vec<LiveIncidence>,
        pins: Vec<LivePin>,
        boundaries: Vec<LiveBoundary>,
        exposed: Vec<u32>,
    ) -> Result<Self, LiveConstituentError> {
        let mut support_sections = Vec::new();
        support_sections
            .try_reserve_exact(boundaries.len())
            .map_err(|_| LiveConstituentError::Extent)?;
        for at in 0..boundaries.len() {
            support_sections.push(LiveSupportSection::new(vec![usize_u32(at)?]));
        }
        Self::with_support_sections(
            grain,
            axis_count,
            cells,
            incidences,
            pins,
            boundaries,
            exposed,
            support_sections,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn with_support_sections(
        grain: u32,
        axis_count: u32,
        cells: Vec<LiveCell>,
        incidences: Vec<LiveIncidence>,
        pins: Vec<LivePin>,
        boundaries: Vec<LiveBoundary>,
        exposed: Vec<u32>,
        support_sections: Vec<LiveSupportSection>,
    ) -> Result<Self, LiveConstituentError> {
        let support = LiveSupportFamily::from_sections(support_sections)?;
        Self::with_support_family(
            grain, axis_count, cells, incidences, pins, boundaries, exposed, support,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn with_support_family(
        grain: u32,
        axis_count: u32,
        cells: Vec<LiveCell>,
        incidences: Vec<LiveIncidence>,
        pins: Vec<LivePin>,
        boundaries: Vec<LiveBoundary>,
        exposed: Vec<u32>,
        support: LiveSupportFamily,
    ) -> Result<Self, LiveConstituentError> {
        let constituent = Self {
            grain,
            axis_count,
            cells,
            incidences,
            pins,
            boundaries,
            exposed,
            support,
        };
        constituent.validate()?;
        Ok(constituent)
    }

    pub const fn grain(&self) -> u32 {
        self.grain
    }

    pub const fn axis_count(&self) -> u32 {
        self.axis_count
    }

    pub fn cells(&self) -> &[LiveCell] {
        &self.cells
    }

    pub fn incidences(&self) -> &[LiveIncidence] {
        &self.incidences
    }

    pub fn pins(&self) -> &[LivePin] {
        &self.pins
    }

    pub fn boundaries(&self) -> &[LiveBoundary] {
        &self.boundaries
    }

    /// Higher-grain deed of one completed boundary. Open fourth contacts remain OPEN; otherwise
    /// any surviving oriented founding passage makes the boundary FOUND, and a boundary with no
    /// founding passage RIDEs. This is derived from complete path emanations, never a scalar chi
    /// threshold or world-authored label.
    pub fn boundary_transition(&self, at: usize) -> Option<LiveBoundaryTransition> {
        let boundary = self.boundaries.get(at)?;
        let mut found = false;
        for path in boundary.paths() {
            found |= path.this_way.mag != 0 || path.that_way.mag != 0;
            for step in path.steps() {
                let incidence = self.incidences.get(step.incidence as usize)?;
                let pin = self.pins.get(incidence.pin as usize)?;
                if pin.is_open() {
                    return Some(LiveBoundaryTransition::Open);
                }
            }
        }
        Some(if found {
            LiveBoundaryTransition::Found
        } else {
            LiveBoundaryTransition::Ride
        })
    }

    /// Return the complete transition of one declared support section. A section remains OPEN if
    /// any of its boundary factors is open, FOUND if no factor is open and at least one founds a
    /// new oriented passage, and otherwise RIDEs. This is the smallest exact radiation face of a
    /// higher regional cell; callers must not substitute a transition observed elsewhere in the
    /// co-present component.
    pub fn support_section_transition(&self, at: usize) -> Option<LiveBoundaryTransition> {
        let transitions = self.support_section_boundary_transitions(at)?;
        let mut found = false;
        for transition in transitions {
            match transition {
                LiveBoundaryTransition::Open => return Some(LiveBoundaryTransition::Open),
                LiveBoundaryTransition::Found => found = true,
                LiveBoundaryTransition::Ride => {}
            }
        }
        Some(if found {
            LiveBoundaryTransition::Found
        } else {
            LiveBoundaryTransition::Ride
        })
    }

    /// Preserve every boundary-factor return inside one declared support section. Unlike the
    /// quotient above, this plural receipt can testify that one local route RIDEs while another
    /// remains FOUND or OPEN.
    pub fn support_section_boundary_transitions(
        &self,
        at: usize,
    ) -> Option<Vec<LiveBoundaryTransition>> {
        self.support
            .factor_boundaries(at)
            .ok()?
            .into_iter()
            .map(|boundary| self.boundary_transition(usize::try_from(boundary).ok()?))
            .collect()
    }

    pub fn exposed(&self) -> &[u32] {
        &self.exposed
    }

    pub const fn support_family(&self) -> &LiveSupportFamily {
        &self.support
    }

    /// Bounded observer materialization of the active factor roots. Production closure and
    /// persistence use [`Self::support_family`] and never call this expansion.
    pub fn support_sections(&self) -> Vec<LiveSupportSection> {
        self.support
            .explicit_sections()
            .expect("a validated constituent has a materializable finite support boundary")
    }

    pub fn support_factor_count(&self) -> usize {
        self.support.factor_count()
    }

    pub fn support_factor_boundaries(&self, at: usize) -> Option<Vec<u32>> {
        self.support.factor_boundaries(at).ok()
    }

    pub fn support_factor_boundary_sets(&self) -> Vec<Vec<u32>> {
        self.support
            .factor_boundary_sets()
            .expect("a validated constituent has exact active factor boundaries")
    }

    pub fn contains_pin(&self, pin: &LivePin) -> bool {
        self.pins.contains(pin)
    }

    /// Whether this constituent still carries the founding overlap for one projectively rebased
    /// axis. The complete historical meeting need not repeat; the exact transported position is
    /// the invariant which lets a later local chart import the same support.
    pub fn contains_founded_axis(&self, position: Place) -> bool {
        self.pins
            .iter()
            .any(|pin| pin.is_found() && pin.transport_position() == Some(position))
    }

    /// Assemble several co-present regional cofaces over their one source occurrence population.
    /// Shared keys identify only actual cells in this event; equal unkeyed cells remain plural.
    /// No new apex or seam is invented by assembly. The returned constituent carries overlap as
    /// common cell ordinals and retains each supplied coface as a distinct support section.
    pub(crate) fn union_shared_event_cofaces(
        cofaces: &[(&LiveConstituent, &[Option<SharedOccurrenceKey>])],
    ) -> Result<Self, LiveConstituentError> {
        if cofaces.is_empty()
            || cofaces
                .iter()
                .any(|(body, origins)| origins.len() != body.cells.len())
        {
            return Err(LiveConstituentError::Topology);
        }

        let mut cells = Vec::new();
        let mut incidences = Vec::new();
        let mut pins = Vec::new();
        let mut boundaries = Vec::new();
        let mut exposed = Vec::new();
        let mut support_expressions = Vec::new();
        let mut shared_cells: BTreeMap<SharedOccurrenceKey, u32> = BTreeMap::new();
        let mut next_axis = 0u32;
        let mut grain = 0u32;

        for (body, origins) in cofaces {
            body.validate()?;
            grain = grain.max(body.grain);
            let mut axes = Vec::new();
            axes.try_reserve_exact(word_usize(body.axis_count)?)
                .map_err(|_| LiveConstituentError::Extent)?;
            for _ in 0..body.axis_count {
                axes.push(LocalAxis::new(next_axis));
                next_axis = next_axis
                    .checked_add(1)
                    .ok_or(LiveConstituentError::Extent)?;
            }

            let mut cell_map = Vec::new();
            cell_map
                .try_reserve_exact(body.cells.len())
                .map_err(|_| LiveConstituentError::Extent)?;
            for (cell, origin) in body.cells.iter().copied().zip(*origins) {
                let rebased = if let Some(origin) = origin {
                    if let Some(existing) = shared_cells.get(origin).copied() {
                        if cells[word_usize(existing)?] != cell {
                            return Err(LiveConstituentError::Topology);
                        }
                        existing
                    } else {
                        let at = usize_u32(cells.len())?;
                        cells.push(cell);
                        shared_cells.insert(*origin, at);
                        at
                    }
                } else {
                    let at = usize_u32(cells.len())?;
                    cells.push(cell);
                    at
                };
                cell_map.push(rebased);
            }

            let incidence_offset = usize_u32(incidences.len())?;
            let pin_offset = usize_u32(pins.len())?;
            let boundary_offset = usize_u32(boundaries.len())?;
            pins.extend_from_slice(&body.pins);
            incidences
                .try_reserve_exact(body.incidences.len())
                .map_err(|_| LiveConstituentError::Extent)?;
            for incidence in &body.incidences {
                incidences.push(LiveIncidence::new(
                    cell_map[word_usize(incidence.from)?],
                    cell_map[word_usize(incidence.to)?],
                    incidence.kind,
                    incidence.hand,
                    incidence
                        .pin
                        .checked_add(pin_offset)
                        .ok_or(LiveConstituentError::Extent)?,
                ));
            }
            for boundary in &body.boundaries {
                let mut paths = Vec::new();
                paths
                    .try_reserve_exact(boundary.paths.len())
                    .map_err(|_| LiveConstituentError::Extent)?;
                for path in &boundary.paths {
                    paths.push(path.rebased(incidence_offset, &axes)?);
                }
                boundaries.push(LiveBoundary::new(boundary.hand, paths));
            }
            for pin in &body.exposed {
                exposed.push(
                    pin.checked_add(pin_offset)
                        .ok_or(LiveConstituentError::Extent)?,
                );
            }
            support_expressions.extend(body.support.rebased(boundary_offset)?.root_expressions()?);
        }
        exposed.sort_unstable();
        exposed.dedup();
        let support = LiveSupportFamily::from_expressions(support_expressions)?;
        Self::with_support_family(
            grain, next_axis, cells, incidences, pins, boundaries, exposed, support,
        )
    }

    /// Close one arriving germ through the same support-indexed population law used for plural
    /// events. This single-member convenience cannot bypass contextual section admission.
    #[allow(dead_code)]
    pub(crate) fn close_against(
        &self,
        standing: &[LiveConstituent],
    ) -> Result<(Vec<usize>, Self), LiveConstituentError> {
        let mut closure = Self::close_population_against(std::slice::from_ref(self), standing)?;
        if closure.len() != 1 {
            return Err(LiveConstituentError::Topology);
        }
        let closure = closure.remove(0);
        Ok((closure.touched, closure.replacement))
    }

    /// Historical whole-parent foil retained only by the local regression module. Production
    /// closure above cannot call it.
    #[cfg(test)]
    #[allow(dead_code)]
    fn close_against_whole_parent_foil(
        &self,
        standing: &[LiveConstituent],
    ) -> Result<(Vec<usize>, Self), LiveConstituentError> {
        let arriving_arms = self.indexed_exposed_arms()?;
        if arriving_arms.ordered.is_empty() || standing.is_empty() {
            return Ok((Vec::new(), self.clone()));
        }

        let mut seams = Vec::new();
        for (prior_at, prior) in standing.iter().enumerate() {
            let prior_arms = prior.indexed_exposed_arms()?;
            for arriving_arm in &arriving_arms.ordered {
                let arriving_pin = &self.pins[arriving_arm.pin];
                let interface = arriving_pin
                    .interface
                    .as_ref()
                    .ok_or(LiveConstituentError::Topology)?;
                let Some(matching_prior) = prior_arms.by_interface.get(interface) else {
                    continue;
                };
                for prior_arm in matching_prior {
                    let prior_pin = &prior.pins[prior_arm.pin];
                    // A prior arm is temporally outgoing and the germ arm incoming. Equal declared
                    // hands therefore cancel at a flat seam; disagreement leaves an oriented
                    // residual. The complete rotor rebase may independently wind and FOUND.
                    let hand_residual =
                        (arriving_arm.hand != prior_arm.hand).then_some(arriving_arm.hand);
                    if let Some(pin) =
                        LivePin::rebase_exposed(arriving_pin, prior_pin, hand_residual)
                    {
                        seams
                            .try_reserve(1)
                            .map_err(|_| LiveConstituentError::Extent)?;
                        seams.push(RegionalSeam {
                            prior: prior_at,
                            prior_arm: *prior_arm,
                            arriving_arm: *arriving_arm,
                            pin,
                        });
                    }
                }
            }
        }
        if seams.is_empty() {
            return Ok((Vec::new(), self.clone()));
        }

        seams.sort_unstable_by_key(|seam| {
            (
                seam.prior,
                seam.prior_arm.boundary,
                seam.prior_arm.path,
                seam.prior_arm.step,
                seam.arriving_arm.boundary,
                seam.arriving_arm.path,
                seam.arriving_arm.step,
            )
        });
        let mut touched: Vec<usize> = seams.iter().map(|seam| seam.prior).collect();
        touched.dedup();

        let mut cells = Vec::new();
        let mut incidences = Vec::new();
        let mut pins = Vec::new();
        let mut boundaries = Vec::new();
        let mut exposed = Vec::new();

        let current_axes = (0..self.axis_count).map(LocalAxis::new).collect();
        let current_map = append_constituent_part(
            self,
            current_axes,
            &mut cells,
            &mut incidences,
            &mut pins,
            &mut boundaries,
            &mut exposed,
        )?;
        let mut next_axis = self.axis_count;
        let mut prior_maps: Vec<Option<ConstituentPartMap>> = Vec::new();
        prior_maps
            .try_reserve_exact(standing.len())
            .map_err(|_| LiveConstituentError::Extent)?;
        prior_maps.resize_with(standing.len(), || None);
        for prior_at in &touched {
            let prior = &standing[*prior_at];
            let shares_receiver_plane = seams
                .iter()
                .any(|seam| seam.prior == *prior_at && !seam.pin.is_found());
            let mut axes = Vec::new();
            axes.try_reserve_exact(word_usize(prior.axis_count)?)
                .map_err(|_| LiveConstituentError::Extent)?;
            for old in 0..prior.axis_count {
                if old == 0 && shares_receiver_plane {
                    axes.push(LocalAxis::new(0));
                } else {
                    axes.push(LocalAxis::new(next_axis));
                    next_axis = next_axis
                        .checked_add(1)
                        .ok_or(LiveConstituentError::Extent)?;
                }
            }
            prior_maps[*prior_at] = Some(append_constituent_part(
                prior,
                axes,
                &mut cells,
                &mut incidences,
                &mut pins,
                &mut boundaries,
                &mut exposed,
            )?);
        }

        let apex_rank = cells
            .iter()
            .map(|cell| cell.dependency_rank)
            .max()
            .unwrap_or(0)
            .checked_add(1)
            .ok_or(LiveConstituentError::Extent)?;
        let apex_dimension = cells
            .iter()
            .map(|cell| cell.dimension)
            .max()
            .unwrap_or(0)
            .checked_add(1)
            .ok_or(LiveConstituentError::Extent)?;
        let grain = touched
            .iter()
            .map(|at| standing[*at].grain)
            .fold(self.grain, u32::max)
            .checked_add(1)
            .ok_or(LiveConstituentError::Extent)?;
        cells
            .try_reserve(1)
            .map_err(|_| LiveConstituentError::Extent)?;
        cells.push(LiveCell::new(apex_rank, apex_dimension, grain));

        let mut consumed = Vec::new();
        consumed
            .try_reserve_exact(seams.len().saturating_mul(2))
            .map_err(|_| LiveConstituentError::Extent)?;
        for seam in seams {
            let prior = &standing[seam.prior];
            let prior_map = prior_maps[seam.prior]
                .as_ref()
                .ok_or(LiveConstituentError::Topology)?;
            let prior_incidence = prior.incidences[seam.prior_arm.incidence];
            let arriving_incidence = self.incidences[seam.arriving_arm.incidence];

            let prior_pin = prior_map
                .pin_offset
                .checked_add(usize_u32(seam.prior_arm.pin)?)
                .ok_or(LiveConstituentError::Extent)?;
            let arriving_pin = current_map
                .pin_offset
                .checked_add(usize_u32(seam.arriving_arm.pin)?)
                .ok_or(LiveConstituentError::Extent)?;
            consumed.push(prior_pin);
            consumed.push(arriving_pin);

            let support = if seam.pin.is_found() {
                let imported_plane = prior_map.axes[0];
                if imported_plane.local() == 0 {
                    let axis = LocalAxis::new(next_axis);
                    next_axis = next_axis
                        .checked_add(1)
                        .ok_or(LiveConstituentError::Extent)?;
                    axis
                } else {
                    imported_plane
                }
            } else {
                let step = self.boundaries[seam.arriving_arm.boundary].paths
                    [seam.arriving_arm.path]
                    .steps[seam.arriving_arm.step];
                current_map.axes[word_usize(step.support.local())?]
            };

            let pin_at = usize_u32(pins.len())?;
            pins.try_reserve(1)
                .map_err(|_| LiveConstituentError::Extent)?;
            pins.push(seam.pin.clone());
            let incidence_at = usize_u32(incidences.len())?;
            let from = prior_map
                .cell_offset
                .checked_add(prior_incidence.to)
                .ok_or(LiveConstituentError::Extent)?;
            let to = current_map
                .cell_offset
                .checked_add(arriving_incidence.from)
                .ok_or(LiveConstituentError::Extent)?;
            incidences
                .try_reserve(1)
                .map_err(|_| LiveConstituentError::Extent)?;
            incidences.push(LiveIncidence::new(
                from,
                to,
                LiveIncidenceKind::Transport,
                seam.arriving_arm.hand,
                pin_at,
            ));
            let winding = seam
                .pin
                .formed
                .map_or(WindingQuantum::None, |formed| formed.winding);
            let path = LivePath::from_steps(
                vec![LivePathStep::new(incidence_at, support, winding)],
                &incidences,
                &pins,
            )?;
            boundaries
                .try_reserve(1)
                .map_err(|_| LiveConstituentError::Extent)?;
            boundaries.push(LiveBoundary::new(seam.arriving_arm.hand, vec![path]));
            if seam.pin.is_found() || seam.pin.is_open() {
                exposed.push(pin_at);
            }
        }

        consumed.sort_unstable();
        consumed.dedup();
        exposed.retain(|pin| consumed.binary_search(pin).is_err());
        exposed.sort_unstable();
        exposed.dedup();
        Self::new(
            grain, next_axis, cells, incidences, pins, boundaries, exposed,
        )
        .and_then(Self::compressed)
        .map(|replacement| (touched, replacement))
    }

    /// Close the complete bounded regional population as one contemporary field. Unlike repeated
    /// `close_against` calls, this operation never lets two arriving regions clone or sequentially
    /// overwrite the same Standing factor. All exact seams are discovered from one immutable
    /// frontier, connected components compose jointly, and newly exposed founding arms feed the
    /// next unpublished frontier until the finite population reaches a fixed point.
    pub(crate) fn close_population_against(
        arriving: &[LiveConstituent],
        standing: &[LiveConstituent],
    ) -> Result<Vec<PopulationClosure>, LiveConstituentError> {
        let aperture = StandingIncidenceAperture::from_standing(standing)?;
        Self::close_population_against_with_aperture(arriving, standing, &aperture)
    }

    /// Production population closure through the standing face's rebuildable incidence aperture.
    /// The aperture restricts work to the currently reachable local star. It never supplies a
    /// seam, a deed, or a successor: the same exact contact law grades every exposed candidate.
    pub(crate) fn close_population_against_with_aperture<S>(
        arriving: &[LiveConstituent],
        standing: &S,
        aperture: &StandingIncidenceAperture,
    ) -> Result<Vec<PopulationClosure>, LiveConstituentError>
    where
        S: StandingConstituentAccess + ?Sized,
    {
        let section_lineages = arriving
            .iter()
            .enumerate()
            .map(|(member, body)| {
                (0..body.support.factor_count())
                    .map(|section| BTreeSet::from([PopulationSectionOrigin::new(member, section)]))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        Self::close_population_against_with_aperture_and_section_lineages(
            arriving,
            standing,
            aperture,
            &section_lineages,
        )
    }

    pub(crate) fn close_population_against_with_aperture_and_section_lineages<S>(
        arriving: &[LiveConstituent],
        standing: &S,
        aperture: &StandingIncidenceAperture,
        section_lineages: &[Vec<BTreeSet<PopulationSectionOrigin>>],
    ) -> Result<Vec<PopulationClosure>, LiveConstituentError>
    where
        S: StandingConstituentAccess + ?Sized,
    {
        if section_lineages.len() != arriving.len()
            || arriving
                .iter()
                .zip(section_lineages)
                .any(|(body, lineages)| {
                    body.support.factor_count() != lineages.len()
                        || lineages.iter().any(BTreeSet::is_empty)
                })
        {
            return Err(LiveConstituentError::Topology);
        }
        let mut active = Vec::new();
        active
            .try_reserve_exact(arriving.len())
            .map_err(|_| LiveConstituentError::Extent)?;
        for (at, body) in arriving.iter().enumerate() {
            let body = body.support_cover_factor()?;
            active.push(ActivePopulationPart {
                members: vec![at],
                touched: Vec::new(),
                body,
                section_lineages: section_lineages[at].clone(),
                front_depth: 0,
            });
        }

        let mut closure_round = 0usize;
        let closure_began = std::time::Instant::now();
        loop {
            closure_round += 1;
            let mut claimed = Vec::new();
            for part in &active {
                claimed.extend_from_slice(&part.touched);
            }
            claimed.sort_unstable();
            claimed.dedup();
            if claimed.iter().any(|at| *at >= standing.standing_len()) {
                return Err(LiveConstituentError::Topology);
            }

            canonicalize_active_population(&mut active)?;
            let active_interfaces = active
                .iter()
                .map(|part| part.body.exposed_interfaces())
                .collect::<Result<Vec<_>, _>>()?;
            let copresent_pairs = copresent_interface_pairs(&active_interfaces);
            // The front's own propagation depth and its co-present demand, both read off the
            // active population rather than declared here.
            let vision = FrontVision {
                depth: active
                    .iter()
                    .map(|part| part.front_depth)
                    .max()
                    .unwrap_or(0),
                horizon: aperture.vision_horizon(),
                co_present: u64::try_from(active.len()).unwrap_or(u64::MAX),
            };
            let admitted = aperture.candidates_for_interfaces(
                active_interfaces.iter().flatten().cloned(),
                &claimed,
                standing,
                vision,
            )?;
            let candidates = admitted.admitted;
            seam_trace(&format_args!(
                "{closure_round:>4} active {:>5} candidates {:>6} deferred {:>5} copresent_pairs {:>7} standing {:>6} at {} ms",
                active.len(),
                candidates.len(),
                admitted.deferred.len(),
                copresent_pairs.len(),
                standing.standing_len(),
                closure_began.elapsed().as_millis()
            ));
            if candidates.is_empty() && copresent_pairs.is_empty() {
                break;
            }

            let mut parts = Vec::new();
            parts
                .try_reserve_exact(active.len())
                .map_err(|_| LiveConstituentError::Extent)?;
            let mut indexed_arms = Vec::new();
            indexed_arms
                .try_reserve_exact(active.len())
                .map_err(|_| LiveConstituentError::Extent)?;
            for (at, part) in active.iter().enumerate() {
                let body = part.body.clone();
                if body.support.factor_count() != part.section_lineages.len() {
                    return Err(LiveConstituentError::Topology);
                }
                indexed_arms.push(body.indexed_exposed_arms()?);
                parts.push(PopulationPart {
                    origin: PopulationPartOrigin::Active(at),
                    body,
                    section_lineages: part.section_lineages.clone(),
                });
            }
            parts
                .try_reserve(candidates.len())
                .map_err(|_| LiveConstituentError::Extent)?;
            indexed_arms
                .try_reserve(candidates.len())
                .map_err(|_| LiveConstituentError::Extent)?;
            // THE JUNCTION, on the quantity that actually costs: the ARM POPULATION.
            //
            // Measured 2026-08-15: one round of this closure built **80,689 seams from 80,756 arms
            // over four parts** and took 12.9 s, between rounds that took 0 ms at 27 arms.
            // `append_temporal_seams` pairs arms, so it is quadratic in them — and a standing
            // constituent that has accreted eighty thousand exposed arms is a far population that
            // was never condensed. `CLAUDE.md` §11's open item, live: the boundary operator has no
            // compact representative, so every seam construction pays its full density.
            //
            // A front carrying twenty-seven arms meeting a site offering eighty thousand is an
            // impedance mismatch of about 748 service rounds. It defers — retained by name with its
            // exact cost — instead of being composed whole.
            //
            // **The multiplicity was the wrong admittance.** A factor at multiplicity one may still
            // expose eighty thousand arms; what a site offers the arriving current is its ARMS.
            //
            // # Two bounds on this reading, both measured and neither hidden
            //
            // **The incident admittance here is an AGGREGATE, not a junction.** It sums the arms of
            // every active part, because candidates are admitted once per round rather than per
            // active part. A per-pair junction would be the law applied properly and would need the
            // admission restructured; this is the law applied to the round. It is stated so nobody
            // reads the aggregate as the junction.
            //
            // **And the residual is the front, not the candidates.** Measured after this landed: a
            // round deferring 36 candidates whose widest offer was 11 arms still carried a front of
            // **105,754 arms** and built 80,664 seams. A body that has composed enormously and
            // retained every residual arm is a far population that was never condensed into a
            // compact representative — which is `CLAUDE.md` §11's named missing organ, live and
            // costing, not a defect of this admission. Deferring candidates cannot reach it; only
            // condensing the front can.
            let arriving_arms = u64::try_from(
                indexed_arms
                    .iter()
                    .map(|arms| arms.by_section.iter().map(Vec::len).sum::<usize>())
                    .sum::<usize>(),
            )
            .map_err(|_| LiveConstituentError::Extent)?;
            let mut deferred_arms = Vec::new();
            for standing_at in candidates {
                let body = standing
                    .standing_get(standing_at)
                    .ok_or(LiveConstituentError::Topology)?
                    .support_cover_factor()?;
                let candidate_arms = body.indexed_exposed_arms()?;
                let offered = u64::try_from(
                    candidate_arms
                        .by_section
                        .iter()
                        .map(Vec::len)
                        .sum::<usize>(),
                )
                .map_err(|_| LiveConstituentError::Extent)?;
                if let Some(crossing) = CountedCrossing::meet(arriving_arms, offered) {
                    if !crossing.crosses_within(aperture.traversal_horizon()) {
                        deferred_arms.push((standing_at, offered, crossing.service_rounds()));
                        continue;
                    }
                }
                indexed_arms.push(candidate_arms);
                parts.push(PopulationPart {
                    origin: PopulationPartOrigin::Standing(standing_at),
                    section_lineages: vec![BTreeSet::new(); body.support.factor_count()],
                    body,
                });
            }
            if !deferred_arms.is_empty() {
                seam_trace(&format_args!(
                    "  DEFERRED {} sites on arm mismatch; front {} arms; widest offered {}",
                    deferred_arms.len(),
                    arriving_arms,
                    deferred_arms
                        .iter()
                        .map(|(_, offered, _)| *offered)
                        .max()
                        .unwrap_or(0)
                ));
            }

            let mut seams = Vec::new();
            let mut next_section_group = 0usize;
            // One source region has already composed its own declared boundary. Matching two of
            // its residual arms again would invent an incidence and can make a finite field grow
            // without causal progress. Distinct arriving regions are genuinely co-present:
            // opposed induced hands cancel directly, while equal hands leave oriented residual.
            for (left, right) in copresent_pairs {
                append_copresent_seams(
                    &parts,
                    &indexed_arms,
                    left,
                    right,
                    &mut seams,
                    &mut next_section_group,
                )?;
            }
            // Standing is temporally outward while the active arm is inward. Equal declared hands
            // therefore cancel only after that time-parity reversal.
            for active_at in 0..active.len() {
                append_temporal_seams(
                    &parts,
                    &indexed_arms,
                    active_at,
                    active.len()..parts.len(),
                    &mut seams,
                    &mut next_section_group,
                )?;
            }

            seam_trace(&format_args!(
                "  seams {:>7} arms {:>8} parts {:>4} at {} ms",
                seams.len(),
                indexed_arms
                    .iter()
                    .map(|arms| arms.by_section.iter().map(Vec::len).sum::<usize>())
                    .sum::<usize>(),
                parts.len(),
                closure_began.elapsed().as_millis()
            ));
            if seams.is_empty() {
                for (at, part) in active.iter_mut().enumerate() {
                    part.body = parts[at].body.clone();
                }
                break;
            }

            let mut parent: Vec<usize> = (0..parts.len()).collect();
            for seam in &seams {
                union_sets(&mut parent, seam.left, seam.right);
            }
            for at in 0..parent.len() {
                let root = find_set(&mut parent, at);
                parent[at] = root;
            }

            let mut roots = Vec::new();
            for root in parent.iter().take(active.len()).copied() {
                if !roots.contains(&root) {
                    roots.push(root);
                }
            }
            roots.sort_unstable();

            let mut next = Vec::new();
            next.try_reserve_exact(roots.len())
                .map_err(|_| LiveConstituentError::Extent)?;
            for root in roots {
                let part_indices: Vec<usize> = parent
                    .iter()
                    .enumerate()
                    .filter_map(|(at, component)| (*component == root).then_some(at))
                    .collect();
                let component_seams: Vec<PopulationSeam> = seams
                    .iter()
                    .filter(|seam| parent[seam.left] == root && parent[seam.right] == root)
                    .cloned()
                    .collect();

                let mut members = Vec::new();
                let mut touched = Vec::new();
                let mut front_depth = 0_u32;
                let mut reached_standing = false;
                for part_at in &part_indices {
                    match parts[*part_at].origin {
                        PopulationPartOrigin::Active(active_at) => {
                            members.extend_from_slice(&active[active_at].members);
                            touched.extend_from_slice(&active[active_at].touched);
                            front_depth = front_depth.max(active[active_at].front_depth);
                        }
                        PopulationPartOrigin::Standing(standing_at) => {
                            touched.push(standing_at);
                            reached_standing = true;
                        }
                    }
                }
                if reached_standing {
                    front_depth = front_depth
                        .checked_add(1)
                        .ok_or(LiveConstituentError::Extent)?;
                }
                members.sort_unstable();
                members.dedup();
                touched.sort_unstable();
                touched.dedup();

                let (body, section_lineages) = if component_seams.is_empty() {
                    let active_at = part_indices
                        .iter()
                        .find_map(|at| match parts[*at].origin {
                            PopulationPartOrigin::Active(active_at) => Some(active_at),
                            PopulationPartOrigin::Standing(_) => None,
                        })
                        .ok_or(LiveConstituentError::Topology)?;
                    (
                        active[active_at].body.clone(),
                        active[active_at].section_lineages.clone(),
                    )
                } else {
                    compose_population_component(&parts, &part_indices, &component_seams)?
                };
                next.push(ActivePopulationPart {
                    members,
                    touched,
                    body,
                    section_lineages,
                    front_depth,
                });
            }
            next.sort_by(|left, right| left.members.cmp(&right.members));
            active = next;
        }

        let mut closed = Vec::new();
        closed
            .try_reserve_exact(active.len())
            .map_err(|_| LiveConstituentError::Extent)?;
        for mut part in active {
            part.members.sort_unstable();
            part.touched.sort_unstable();
            closed.push(PopulationClosure {
                members: part.members,
                touched: part.touched,
                replacement: part.body,
                section_lineages: part.section_lineages,
                front_depth: part.front_depth,
            });
        }
        Ok(closed)
    }

    pub fn boundary_behavior(&self) -> Result<BoundaryBehavior, LiveConstituentError> {
        self.validate()?;
        let mut paths = Vec::new();
        paths
            .try_reserve_exact(self.boundaries.len())
            .map_err(|_| LiveConstituentError::Extent)?;
        for (at, boundary) in self.boundaries.iter().enumerate() {
            let mut behavior = Vec::new();
            behavior
                .try_reserve_exact(boundary.paths.len())
                .map_err(|_| LiveConstituentError::Extent)?;
            for path in &boundary.paths {
                behavior.push(BoundaryPathBehavior {
                    transport: path.transport.clone(),
                    this_way: path.this_way,
                    that_way: path.that_way,
                });
            }
            paths.push((
                boundary.hand,
                self.boundary_transition(at)
                    .ok_or(LiveConstituentError::Topology)?,
                behavior,
            ));
        }

        let arms = self.exposed_arms()?;
        let mut exposed = Vec::new();
        exposed
            .try_reserve_exact(arms.len())
            .map_err(|_| LiveConstituentError::Extent)?;
        for arm in arms {
            let incidence = self.incidences[arm.incidence];
            let pin = &self.pins[arm.pin];
            exposed.push(ExposedArmBehavior {
                interface: pin
                    .interface
                    .clone()
                    .ok_or(LiveConstituentError::Topology)?,
                comparison: pin.comparison(),
                held_live: pin.held_live,
                formed: pin.formed,
                hand: arm.hand,
                from: self.cells[word_usize(incidence.from)?],
                to: self.cells[word_usize(incidence.to)?],
                support: self.boundaries[arm.boundary].paths[arm.path].steps[arm.step].support,
            });
        }
        Ok(BoundaryBehavior {
            grain: self.grain,
            axis_count: self.axis_count,
            paths,
            exposed,
            support: self.support.clone(),
        })
    }

    /// Emit one source-declared outgoing boundary of this already-formed regional event. The
    /// selected ordinals name complete boundaries, never individual storage rows. Every incidence
    /// used by those boundaries is first retained whole, one actual higher-grain completion cell
    /// is added, and the ordinary exact boundary compressor then folds only interior which cannot
    /// change that selected face.
    ///
    /// This is the event's `q : X -> Q`, not a cleanup pass over Standing. The caller must still
    /// prove that this selected face is the complete exposed boundary of the joint event before it
    /// may replace any prior constituent.
    pub(crate) fn outgoing_boundary_factor(
        &self,
        selected: &[usize],
        grain: u32,
    ) -> Result<Self, LiveConstituentError> {
        self.boundary_factor(selected, grain, false)
    }

    fn boundary_factor(
        &self,
        selected: &[usize],
        grain: u32,
        preserve_exposure: bool,
    ) -> Result<Self, LiveConstituentError> {
        self.validate()?;
        if selected.is_empty()
            || grain < self.grain
            || selected.windows(2).any(|pair| pair[0] >= pair[1])
            || selected.iter().any(|at| *at >= self.boundaries.len())
        {
            return Err(LiveConstituentError::Topology);
        }

        let mut incidence_used = vec![false; self.incidences.len()];
        for boundary_at in selected {
            for path in &self.boundaries[*boundary_at].paths {
                for step in &path.steps {
                    incidence_used[word_usize(step.incidence)?] = true;
                }
            }
        }

        let mut pin_used = vec![false; self.pins.len()];
        let mut cell_used = vec![false; self.cells.len()];
        for (at, incidence) in self.incidences.iter().copied().enumerate() {
            if !incidence_used[at] {
                continue;
            }
            pin_used[word_usize(incidence.pin)?] = true;
            cell_used[word_usize(incidence.from)?] = true;
            cell_used[word_usize(incidence.to)?] = true;
        }

        let mut cell_map = vec![None; self.cells.len()];
        let mut cells = Vec::new();
        for (at, cell) in self.cells.iter().copied().enumerate() {
            if cell_used[at] {
                cell_map[at] = Some(usize_u32(cells.len())?);
                cells.push(cell);
            }
        }
        let apex_rank = cells
            .iter()
            .map(|cell| cell.dependency_rank)
            .max()
            .unwrap_or(0)
            .checked_add(1)
            .ok_or(LiveConstituentError::Extent)?;
        let apex_dimension = cells
            .iter()
            .map(|cell| cell.dimension)
            .max()
            .unwrap_or(0)
            .checked_add(1)
            .ok_or(LiveConstituentError::Extent)?;
        cells
            .try_reserve(1)
            .map_err(|_| LiveConstituentError::Extent)?;
        cells.push(LiveCell::new(apex_rank, apex_dimension, grain));

        let mut pin_map = vec![None; self.pins.len()];
        let mut pins = Vec::new();
        for (at, pin) in self.pins.iter().cloned().enumerate() {
            if pin_used[at] {
                pin_map[at] = Some(usize_u32(pins.len())?);
                pins.push(pin);
            }
        }

        let mut incidence_map = vec![None; self.incidences.len()];
        let mut incidences = Vec::new();
        for (at, incidence) in self.incidences.iter().copied().enumerate() {
            if !incidence_used[at] {
                continue;
            }
            let rebased = usize_u32(incidences.len())?;
            incidence_map[at] = Some(rebased);
            incidences.push(LiveIncidence::new(
                cell_map[word_usize(incidence.from)?].ok_or(LiveConstituentError::Topology)?,
                cell_map[word_usize(incidence.to)?].ok_or(LiveConstituentError::Topology)?,
                incidence.kind,
                incidence.hand,
                pin_map[word_usize(incidence.pin)?].ok_or(LiveConstituentError::Topology)?,
            ));
        }

        let mut boundaries = Vec::new();
        boundaries
            .try_reserve_exact(selected.len())
            .map_err(|_| LiveConstituentError::Extent)?;
        for boundary_at in selected {
            let boundary = &self.boundaries[*boundary_at];
            let mut paths = Vec::new();
            paths
                .try_reserve_exact(boundary.paths.len())
                .map_err(|_| LiveConstituentError::Extent)?;
            for path in &boundary.paths {
                let mut steps = Vec::new();
                steps
                    .try_reserve_exact(path.steps.len())
                    .map_err(|_| LiveConstituentError::Extent)?;
                for step in &path.steps {
                    steps.push(LivePathStep::new(
                        incidence_map[word_usize(step.incidence)?]
                            .ok_or(LiveConstituentError::Topology)?,
                        step.support,
                        step.winding,
                    ));
                }
                paths.push(LivePath {
                    steps,
                    transport: path.transport.clone(),
                    this_way: path.this_way,
                    that_way: path.that_way,
                    interior_folded: path.interior_folded,
                });
            }
            boundaries.push(LiveBoundary::new(boundary.hand, paths));
        }

        // Recompute exposure in the selected boundary rather than copying the old exposure list.
        // Removing one arm can uncover or cancel another; the complete-event check performed by
        // the live machine below will refuse either change unless it is the actual outgoing face.
        let mut exposure = vec![0i64; pins.len()];
        let mut transport_arm = vec![false; pins.len()];
        for boundary in &boundaries {
            for path in &boundary.paths {
                for step in &path.steps {
                    let incidence = incidences[word_usize(step.incidence)?];
                    if incidence.kind != LiveIncidenceKind::Transport {
                        continue;
                    }
                    let pin_at = word_usize(incidence.pin)?;
                    transport_arm[pin_at] = true;
                    exposure[pin_at] = exposure[pin_at]
                        .checked_add(incidence.hand.coefficient())
                        .ok_or(LiveConstituentError::Extent)?;
                }
            }
        }
        let mut exposed = Vec::new();
        if preserve_exposure {
            for old in &self.exposed {
                if let Some(rebased) = pin_map[word_usize(*old)?] {
                    exposed.push(rebased);
                }
            }
        } else {
            for (at, pin) in pins.iter().enumerate() {
                if transport_arm[at] && (exposure[at] != 0 || pin.is_open()) {
                    exposed.push(usize_u32(at)?);
                }
            }
        }

        let mut selected_map = vec![None; self.boundaries.len()];
        for (new, old) in selected.iter().copied().enumerate() {
            *selected_map
                .get_mut(old)
                .ok_or(LiveConstituentError::Topology)? = Some(usize_u32(new)?);
        }
        let support = self
            .support
            .remapped_complete(&selected_map, selected.len())?;

        Self::with_support_family(
            grain,
            self.axis_count,
            cells,
            incidences,
            pins,
            boundaries,
            exposed,
            support,
        )?
        .compressed()
    }

    /// Restrict a carried body to the union of its actual outgoing support sections. Every
    /// section remains distinct and overlapping sections continue to share the same retained
    /// occurrence rows. Closed interior which belongs to no section leaves this active cut.
    fn support_cover_factor(&self) -> Result<Self, LiveConstituentError> {
        let selected = self
            .support
            .all_factor_boundaries()?
            .into_iter()
            .map(word_usize)
            .collect::<Result<Vec<_>, _>>()?;
        self.boundary_factor(&selected, self.grain, true)
    }

    /// Exact equality at the only face which can admit a genuinely later regional contact. This
    /// deliberately ignores closed event interior; the selected factor separately certifies its
    /// own complete boundary paths through [`Self::compress_certified`].
    pub(crate) fn has_same_exposed_boundary(
        &self,
        other: &Self,
    ) -> Result<bool, LiveConstituentError> {
        Ok(self.boundary_behavior()?.exposed == other.boundary_behavior()?.exposed)
    }

    /// Emanate the active face and return the exact contact-boundary preservation witness formed
    /// during that same operation. The certificate is not stored in Standing.
    pub fn compress_certified(
        self,
    ) -> Result<(Self, CompressionCertificate), LiveConstituentError> {
        let before = self.boundary_behavior()?;
        let before_cells = self.cells.len();
        let before_incidences = self.incidences.len();
        let compressed = self.compress_interior()?;
        let after = compressed.boundary_behavior()?;
        if before != after {
            return Err(LiveConstituentError::CompressionBoundaryChanged);
        }
        let certificate = CompressionCertificate {
            behavior: after,
            before_cells,
            after_cells: compressed.cells.len(),
            before_incidences,
            after_incidences: compressed.incidences.len(),
        };
        Ok((compressed, certificate))
    }

    /// Emanate the active face of a completed cellular composition. A completed interior step is
    /// retained in its path transport and may release its pin, incidence, and lower source cells;
    /// exposed, founded, shared, open, and cyclic factors remain explicit.
    fn compressed(self) -> Result<Self, LiveConstituentError> {
        self.compress_certified().map(|(body, _certificate)| body)
    }

    fn compress_interior(self) -> Result<Self, LiveConstituentError> {
        let support = self.support.clone();
        let mut incidence_use = vec![0u32; self.incidences.len()];
        for boundary in &self.boundaries {
            for path in &boundary.paths {
                for step in &path.steps {
                    let at = word_usize(step.incidence)?;
                    incidence_use[at] = incidence_use[at]
                        .checked_add(1)
                        .ok_or(LiveConstituentError::Extent)?;
                }
            }
        }
        let cycle = cellular_cycle_edges(self.cells.len(), &self.incidences, &incidence_use)?;
        let mut is_exposed = vec![false; self.pins.len()];
        for pin in &self.exposed {
            is_exposed[word_usize(*pin)?] = true;
        }
        let mut keep_incidence = vec![false; self.incidences.len()];
        let mut keep_pin = vec![false; self.pins.len()];
        let mut keep_cell: Vec<bool> = self.cells.iter().map(|cell| cell.dimension > 0).collect();
        for (at, incidence) in self.incidences.iter().copied().enumerate() {
            let pin_at = word_usize(incidence.pin)?;
            let consequential = incidence_use[at] > 1
                || cycle[at]
                || is_exposed[pin_at]
                || self.pins[pin_at].is_found()
                || self.pins[pin_at].is_open();
            if !consequential {
                continue;
            }
            keep_incidence[at] = true;
            keep_pin[pin_at] = true;
            keep_cell[word_usize(incidence.from)?] = true;
            keep_cell[word_usize(incidence.to)?] = true;
        }

        let mut cell_map = vec![None; self.cells.len()];
        let mut cells = Vec::new();
        for (at, cell) in self.cells.iter().copied().enumerate() {
            if keep_cell[at] {
                cell_map[at] = Some(usize_u32(cells.len())?);
                cells.push(cell);
            }
        }
        let mut pin_map = vec![None; self.pins.len()];
        let mut pins = Vec::new();
        for (at, pin) in self.pins.iter().cloned().enumerate() {
            if keep_pin[at] {
                pin_map[at] = Some(usize_u32(pins.len())?);
                pins.push(pin);
            }
        }
        let mut incidence_map = vec![None; self.incidences.len()];
        let mut incidences = Vec::new();
        for (at, incidence) in self.incidences.iter().copied().enumerate() {
            if !keep_incidence[at] {
                continue;
            }
            let rebased = usize_u32(incidences.len())?;
            incidence_map[at] = Some(rebased);
            incidences.push(LiveIncidence::new(
                cell_map[word_usize(incidence.from)?].ok_or(LiveConstituentError::Topology)?,
                cell_map[word_usize(incidence.to)?].ok_or(LiveConstituentError::Topology)?,
                incidence.kind,
                incidence.hand,
                pin_map[word_usize(incidence.pin)?].ok_or(LiveConstituentError::Topology)?,
            ));
        }
        let mut boundaries = Vec::new();
        boundaries
            .try_reserve_exact(self.boundaries.len())
            .map_err(|_| LiveConstituentError::Extent)?;
        for boundary in self.boundaries {
            let mut paths = Vec::new();
            paths
                .try_reserve_exact(boundary.paths.len())
                .map_err(|_| LiveConstituentError::Extent)?;
            for path in boundary.paths {
                let mut retained = Vec::new();
                for step in path.steps() {
                    if let Some(incidence) = incidence_map[word_usize(step.incidence)?] {
                        retained.push(LivePathStep::new(incidence, step.support, step.winding));
                    }
                }
                paths.push(path.fold_interior(retained));
            }
            boundaries.push(LiveBoundary::new(boundary.hand, paths));
        }
        let mut exposed = Vec::new();
        for pin in self.exposed {
            exposed.push(pin_map[word_usize(pin)?].ok_or(LiveConstituentError::Topology)?);
        }
        Self::with_support_family(
            self.grain,
            self.axis_count,
            cells,
            incidences,
            pins,
            boundaries,
            exposed,
            support,
        )
    }

    fn exposed_arms(&self) -> Result<Vec<ExposedArm>, LiveConstituentError> {
        let mut exposed_ordinal = vec![None; self.pins.len()];
        for (ordinal, exposed) in self.exposed.iter().copied().enumerate() {
            let pin_at = word_usize(exposed)?;
            let slot = exposed_ordinal
                .get_mut(pin_at)
                .ok_or(LiveConstituentError::Topology)?;
            if slot.replace(ordinal).is_some() {
                return Err(LiveConstituentError::Topology);
            }
        }

        let mut with: Vec<Vec<ExposedArm>> = (0..self.exposed.len()).map(|_| Vec::new()).collect();
        let mut against: Vec<Vec<ExposedArm>> =
            (0..self.exposed.len()).map(|_| Vec::new()).collect();
        for (boundary_at, boundary) in self.boundaries.iter().enumerate() {
            for (path_at, path) in boundary.paths.iter().enumerate() {
                for (step_at, step) in path.steps.iter().enumerate() {
                    let incidence_at = word_usize(step.incidence)?;
                    let incidence = *self
                        .incidences
                        .get(incidence_at)
                        .ok_or(LiveConstituentError::Topology)?;
                    if incidence.kind != LiveIncidenceKind::Transport {
                        continue;
                    }
                    let pin_at = word_usize(incidence.pin)?;
                    let Some(ordinal) = exposed_ordinal
                        .get(pin_at)
                        .ok_or(LiveConstituentError::Topology)?
                    else {
                        continue;
                    };
                    let arm = ExposedArm {
                        boundary: boundary_at,
                        path: path_at,
                        step: step_at,
                        incidence: incidence_at,
                        pin: pin_at,
                        hand: incidence.hand,
                    };
                    match incidence.hand {
                        IncidenceHand::With => with[*ordinal].push(arm),
                        IncidenceHand::Against => against[*ordinal].push(arm),
                    }
                }
            }
        }

        let mut arms = Vec::new();
        for (ordinal, exposed) in self.exposed.iter().copied().enumerate() {
            let pin = &self.pins[word_usize(exposed)?];
            let with = core::mem::take(&mut with[ordinal]);
            let against = core::mem::take(&mut against[ordinal]);
            if with.is_empty() && against.is_empty() {
                return Err(LiveConstituentError::Topology);
            }
            if pin.is_open() {
                arms.extend(with);
                arms.extend(against);
            } else if with.len() > against.len() {
                let residual = with.len() - against.len();
                arms.extend(with.into_iter().take(residual));
            } else {
                let residual = against.len() - with.len();
                arms.extend(against.into_iter().take(residual));
            }
        }
        Ok(arms)
    }

    /// The exact material capabilities present on this active boundary. This is the cheapest
    /// lawful aperture query: it can rule out a local meeting, but it cannot establish one.
    /// Support-section coverage and complete transported paths are still inspected whenever an
    /// interface is actually co-present.
    fn exposed_interfaces(&self) -> Result<Vec<InterfaceCapability>, LiveConstituentError> {
        let mut interfaces = Vec::new();
        interfaces
            .try_reserve_exact(self.exposed.len())
            .map_err(|_| LiveConstituentError::Extent)?;
        for exposed in &self.exposed {
            let interface = self
                .pins
                .get(word_usize(*exposed)?)
                .and_then(|pin| pin.interface.as_ref())
                .ok_or(LiveConstituentError::Topology)?;
            interfaces.push(interface.clone());
        }
        interfaces.sort_unstable();
        interfaces.dedup();
        Ok(interfaces)
    }

    fn indexed_exposed_arms(&self) -> Result<IndexedExposedArms, LiveConstituentError> {
        let ordered = self.exposed_arms()?;
        #[cfg(test)]
        let mut by_interface: BTreeMap<InterfaceCapability, Vec<ExposedArm>> = BTreeMap::new();
        #[cfg(test)]
        for arm in ordered.iter().copied() {
            let interface = self.pins[arm.pin]
                .interface
                .clone()
                .ok_or(LiveConstituentError::Topology)?;
            by_interface.entry(interface).or_default().push(arm);
        }
        let mut sections_by_boundary = vec![Vec::new(); self.boundaries.len()];
        let factor_boundaries = self.support.factor_boundary_sets()?;
        for (section_at, boundaries) in factor_boundaries.iter().enumerate() {
            for boundary in boundaries {
                sections_by_boundary
                    .get_mut(word_usize(*boundary)?)
                    .ok_or(LiveConstituentError::Topology)?
                    .push(section_at);
            }
        }
        let mut by_section = vec![Vec::new(); factor_boundaries.len()];
        for arm in &ordered {
            for section_at in sections_by_boundary
                .get(arm.boundary)
                .ok_or(LiveConstituentError::Topology)?
            {
                by_section[*section_at].push(*arm);
            }
        }
        let mut sections_by_interface = BTreeMap::<InterfaceCapability, Vec<usize>>::new();
        for (section, arms) in by_section.iter().enumerate() {
            let mut interfaces = arms
                .iter()
                .map(|arm| {
                    self.pins[arm.pin]
                        .interface
                        .clone()
                        .ok_or(LiveConstituentError::Topology)
                })
                .collect::<Result<Vec<_>, _>>()?;
            interfaces.sort();
            interfaces.dedup();
            for interface in interfaces {
                sections_by_interface
                    .entry(interface)
                    .or_default()
                    .push(section);
            }
        }
        Ok(IndexedExposedArms {
            #[cfg(test)]
            ordered,
            #[cfg(test)]
            by_interface,
            by_section,
            sections_by_interface,
        })
    }

    pub fn native_words(&self) -> Result<Vec<u32>, LiveConstituentError> {
        self.validate()?;
        let mut words = vec![
            NATIVE_MAGIC,
            NATIVE_VERSION,
            self.grain,
            self.axis_count,
            usize_u32(self.cells.len())?,
            usize_u32(self.incidences.len())?,
            usize_u32(self.pins.len())?,
            usize_u32(self.boundaries.len())?,
            usize_u32(self.exposed.len())?,
            0,
            0,
        ];
        for cell in &self.cells {
            words.push(cell.dependency_rank);
            words.push(cell.dimension);
            words.push(cell.grain);
        }
        for incidence in &self.incidences {
            words.push(incidence.from);
            words.push(incidence.to);
            words.push(incidence.kind as u32);
            words.push(hand_word(incidence.hand));
            words.push(incidence.pin);
        }
        for pin in &self.pins {
            words.extend(pin.exact_words());
        }
        for boundary in &self.boundaries {
            words.push(hand_word(boundary.hand));
            words.push(usize_u32(boundary.paths.len())?);
            for path in &boundary.paths {
                words.push(usize_u32(path.steps.len())?);
                words.push(usize_u32(path.transport.terms.len())?);
                words.push(u32::from(path.interior_folded));
                for word in 0..RUNG_WORDS {
                    words.push(rung_packed_word(path.this_way, word));
                }
                for word in 0..RUNG_WORDS {
                    words.push(rung_packed_word(path.that_way, word));
                }
                for step in &path.steps {
                    words.push(step.incidence);
                    words.push(step.support.local());
                    words.push(winding_word(step.winding));
                }
                for term in &path.transport.terms {
                    words.push(usize_u32(term.blade.axes.len())?);
                    push_cog(&mut words, term.coefficient);
                    words.extend(term.blade.axes.iter().map(|axis| axis.local()));
                }
            }
        }
        words.extend_from_slice(&self.exposed);
        self.support.write_native_words(&mut words)?;
        let payload = words
            .len()
            .checked_sub(HEADER_WORDS)
            .ok_or(LiveConstituentError::Extent)?;
        let payload = u64::try_from(payload).map_err(|_| LiveConstituentError::Extent)?;
        words[9] = payload as u32;
        words[10] = (payload >> 32) as u32;
        Ok(words)
    }

    pub fn from_native_words(words: &[u32]) -> Result<Self, LiveConstituentError> {
        if words.len() < HEADER_WORDS || words[0] != NATIVE_MAGIC || words[1] != NATIVE_VERSION {
            return Err(LiveConstituentError::InvalidWire);
        }
        let payload = words[9] as u64 | ((words[10] as u64) << 32);
        if usize::try_from(payload).ok() != words.len().checked_sub(HEADER_WORDS) {
            return Err(LiveConstituentError::InvalidWire);
        }
        let cells_count = word_usize(words[4])?;
        let incidences_count = word_usize(words[5])?;
        let pins_count = word_usize(words[6])?;
        let boundaries_count = word_usize(words[7])?;
        let exposed_count = word_usize(words[8])?;
        let mut cursor = HEADER_WORDS;
        let mut cells = Vec::with_capacity(cells_count);
        for _ in 0..cells_count {
            cells.push(LiveCell::new(
                take(words, &mut cursor)?,
                take(words, &mut cursor)?,
                take(words, &mut cursor)?,
            ));
        }
        let mut incidences = Vec::with_capacity(incidences_count);
        for _ in 0..incidences_count {
            let from = take(words, &mut cursor)?;
            let to = take(words, &mut cursor)?;
            let kind = match take(words, &mut cursor)? {
                0 => LiveIncidenceKind::Boundary,
                1 => LiveIncidenceKind::Dependency,
                2 => LiveIncidenceKind::Transport,
                3 => LiveIncidenceKind::RewriteInterface,
                _ => return Err(LiveConstituentError::InvalidWire),
            };
            let hand = read_hand(take(words, &mut cursor)?)?;
            let pin = take(words, &mut cursor)?;
            incidences.push(LiveIncidence::new(from, to, kind, hand, pin));
        }
        let mut pins = Vec::with_capacity(pins_count);
        for _ in 0..pins_count {
            let formed_tag = take(words, &mut cursor)?;
            if formed_tag > 1 || cursor.checked_add(STRUCTURAL_PIN_FIXED_WORDS - 1).is_none() {
                return Err(LiveConstituentError::InvalidWire);
            }
            if !packed_face_is_canonical(words, cursor) {
                return Err(LiveConstituentError::InvalidWire);
            }
            let meeting = unpack_face(words, cursor);
            cursor += FACE_WORDS;
            if !packed_face_is_canonical(words, cursor) {
                return Err(LiveConstituentError::InvalidWire);
            }
            let held = unpack_face(words, cursor);
            cursor += FACE_WORDS;
            let held_live = match take(words, &mut cursor)? {
                0 => false,
                1 => true,
                _ => return Err(LiveConstituentError::InvalidWire),
            };
            let interface_tag = take(words, &mut cursor)?;
            if interface_tag > 1 {
                return Err(LiveConstituentError::InvalidWire);
            }
            let interface_origin = read_interface_origin(take(words, &mut cursor)?)?;
            let namespace = take_u64(words, &mut cursor)?;
            let local = take_u64(words, &mut cursor)?;
            let fiber_tag = take(words, &mut cursor)?;
            if fiber_tag > 1 {
                return Err(LiveConstituentError::InvalidWire);
            }
            let antecedent = take_receiver_fiber(words, &mut cursor)?;
            let consequent = take_receiver_fiber(words, &mut cursor)?;
            let receiver_fiber = match fiber_tag {
                0 if antecedent.schema == 0
                    && antecedent.words.is_empty()
                    && consequent.schema == 0
                    && consequent.words.is_empty() =>
                {
                    None
                }
                0 => return Err(LiveConstituentError::InvalidWire),
                1 if interface_origin == InterfaceCapabilityOrigin::ReceiverCaused => {
                    Some((antecedent, consequent))
                }
                1 => return Err(LiveConstituentError::InvalidWire),
                _ => unreachable!(),
            };
            let interface = match interface_tag {
                0 if interface_origin == InterfaceCapabilityOrigin::Inherited
                    && namespace == 0
                    && local == 0 =>
                {
                    if receiver_fiber.is_some() {
                        return Err(LiveConstituentError::InvalidWire);
                    }
                    None
                }
                0 => return Err(LiveConstituentError::InvalidWire),
                1 => Some(InterfaceCapability {
                    origin: interface_origin,
                    namespace,
                    local,
                    receiver_fiber,
                }),
                _ => unreachable!(),
            };
            let residual_tag = take(words, &mut cursor)?;
            if residual_tag > 1 {
                return Err(LiveConstituentError::InvalidWire);
            }
            let other = take_cog(words, &mut cursor)?;
            let same = take_cog(words, &mut cursor)?;
            let projected_residual = match residual_tag {
                0 if other == Cog::ZERO && same == Cog::ZERO => None,
                0 => return Err(LiveConstituentError::InvalidWire),
                1 => Some(Chi { other, same }),
                _ => unreachable!(),
            };
            let position = (take_cog(words, &mut cursor)?, take_cog(words, &mut cursor)?);
            let other = take_cog(words, &mut cursor)?;
            let same = take_cog(words, &mut cursor)?;
            let winding = read_winding(take(words, &mut cursor)?)?;
            let deed = read_deed(take(words, &mut cursor)?)?;
            let formed = if formed_tag == 0 {
                if position != (Cog::ZERO, Cog::ZERO)
                    || other != Cog::ZERO
                    || same != Cog::ZERO
                    || winding != WindingQuantum::None
                    || deed != FeltDeed::Dark
                {
                    return Err(LiveConstituentError::InvalidWire);
                }
                None
            } else {
                Some(FormedPin {
                    position,
                    chi: Chi { other, same },
                    winding,
                    deed,
                })
            };
            if formed.is_some_and(|formed| projected_residual != Some(formed.chi)) {
                return Err(LiveConstituentError::InvalidWire);
            }
            pins.push(LivePin {
                meeting,
                held,
                held_live,
                interface,
                projected_residual,
                formed,
            });
        }
        let mut boundaries = Vec::with_capacity(boundaries_count);
        for _ in 0..boundaries_count {
            let hand = read_hand(take(words, &mut cursor)?)?;
            let paths_count = word_usize(take(words, &mut cursor)?)?;
            let mut paths = Vec::with_capacity(paths_count);
            for _ in 0..paths_count {
                let steps_count = word_usize(take(words, &mut cursor)?)?;
                let terms_count = word_usize(take(words, &mut cursor)?)?;
                let interior_folded = match take(words, &mut cursor)? {
                    0 => false,
                    1 => true,
                    _ => return Err(LiveConstituentError::InvalidWire),
                };
                if !packed_rung_is_canonical(words, cursor) {
                    return Err(LiveConstituentError::InvalidWire);
                }
                let this_way = read_rung(words, cursor);
                cursor += RUNG_WORDS;
                if !packed_rung_is_canonical(words, cursor) {
                    return Err(LiveConstituentError::InvalidWire);
                }
                let that_way = read_rung(words, cursor);
                cursor += RUNG_WORDS;
                let mut steps = Vec::with_capacity(steps_count);
                for _ in 0..steps_count {
                    steps.push(LivePathStep::new(
                        take(words, &mut cursor)?,
                        LocalAxis::new(take(words, &mut cursor)?),
                        read_winding(take(words, &mut cursor)?)?,
                    ));
                }
                let mut terms = Vec::with_capacity(terms_count);
                for _ in 0..terms_count {
                    let axes_count = word_usize(take(words, &mut cursor)?)?;
                    let coefficient = take_cog(words, &mut cursor)?;
                    if coefficient.mag == 0 {
                        return Err(LiveConstituentError::InvalidWire);
                    }
                    let mut axes = Vec::with_capacity(axes_count);
                    for _ in 0..axes_count {
                        axes.push(LocalAxis::new(take(words, &mut cursor)?));
                    }
                    if axes.windows(2).any(|pair| pair[0] >= pair[1]) {
                        return Err(LiveConstituentError::InvalidWire);
                    }
                    terms.push(TransportTerm {
                        blade: LocalBlade { axes },
                        coefficient,
                    });
                }
                if terms.windows(2).any(|pair| pair[0].blade >= pair[1].blade) {
                    return Err(LiveConstituentError::InvalidWire);
                }
                paths.push(LivePath {
                    steps,
                    transport: SparseTransport { terms },
                    this_way,
                    that_way,
                    interior_folded,
                });
            }
            boundaries.push(LiveBoundary { hand, paths });
        }
        let mut exposed = Vec::with_capacity(exposed_count);
        for _ in 0..exposed_count {
            exposed.push(take(words, &mut cursor)?);
        }
        let support = LiveSupportFamily::read_native_words(words, &mut cursor)?;
        if cursor != words.len() {
            return Err(LiveConstituentError::InvalidWire);
        }
        Self::with_support_family(
            words[2], words[3], cells, incidences, pins, boundaries, exposed, support,
        )
        .map_err(|_| LiveConstituentError::InvalidWire)
    }

    fn validate(&self) -> Result<(), LiveConstituentError> {
        if self.grain == 0
            || self.axis_count == 0
            || self.cells.is_empty()
            || self.boundaries.is_empty()
            || self
                .boundaries
                .iter()
                .any(|boundary| boundary.paths.is_empty())
        {
            return Err(LiveConstituentError::Topology);
        }
        if self.pins.iter().any(|pin| {
            pin.formed
                .is_some_and(|formed| pin.projected_residual != Some(formed.chi))
        }) {
            return Err(LiveConstituentError::Algebra);
        }
        for incidence in &self.incidences {
            let from_at = word_usize(incidence.from)?;
            let to_at = word_usize(incidence.to)?;
            if from_at >= self.cells.len()
                || to_at >= self.cells.len()
                || word_usize(incidence.pin)? >= self.pins.len()
            {
                return Err(LiveConstituentError::Topology);
            }
            let from = self.cells[from_at];
            let to = self.cells[to_at];
            let situated = match incidence.kind {
                LiveIncidenceKind::Boundary => {
                    from.dependency_rank == to.dependency_rank
                        && from.dimension.checked_add(1) == Some(to.dimension)
                }
                LiveIncidenceKind::Dependency => from.dependency_rank < to.dependency_rank,
                LiveIncidenceKind::RewriteInterface => {
                    from.dependency_rank < to.dependency_rank && from.dimension == to.dimension
                }
                LiveIncidenceKind::Transport => true,
            };
            if !situated {
                return Err(LiveConstituentError::Topology);
            }
        }
        for boundary in &self.boundaries {
            for path in &boundary.paths {
                if path.steps.iter().any(|step| {
                    word_usize(step.incidence)
                        .ok()
                        .is_none_or(|at| at >= self.incidences.len())
                        || step.support.local() >= self.axis_count
                }) {
                    return Err(LiveConstituentError::Topology);
                }
                if !path.interior_folded {
                    let (transport, this_way, that_way) =
                        path_emanation(&path.steps, &self.incidences, &self.pins)?;
                    if transport != path.transport
                        || this_way != path.this_way
                        || that_way != path.that_way
                    {
                        return Err(LiveConstituentError::Algebra);
                    }
                }
                if path.transport.terms.iter().any(|term| {
                    term.blade
                        .axes
                        .iter()
                        .any(|axis| axis.local() >= self.axis_count)
                }) {
                    return Err(LiveConstituentError::Algebra);
                }
            }
        }
        if self.exposed.windows(2).any(|pair| pair[0] >= pair[1])
            || self
                .exposed
                .iter()
                .any(|pin| word_usize(*pin).ok().is_none_or(|at| at >= self.pins.len()))
            || self.exposed.iter().any(|pin| {
                word_usize(*pin)
                    .ok()
                    .and_then(|at| self.pins.get(at))
                    .is_none_or(|pin| pin.interface.is_none())
            })
        {
            return Err(LiveConstituentError::Topology);
        }
        self.support
            .validate_for_boundaries(self.boundaries.len())?;
        Ok(())
    }
}

fn find_set(parent: &mut [usize], at: usize) -> usize {
    if parent[at] != at {
        let root = find_set(parent, parent[at]);
        parent[at] = root;
    }
    parent[at]
}

/// Rebuildable aperture over the currently co-present front. It returns only active pairs which
/// share an exact exposed capability. This is necessary incidence, not a contact decision:
/// complete support coverage, hands, and transported paths are still graded below.
fn copresent_interface_pairs(
    active_interfaces: &[Vec<InterfaceCapability>],
) -> BTreeSet<(usize, usize)> {
    let mut incidence = BTreeMap::<InterfaceCapability, Vec<usize>>::new();
    for (active_at, interfaces) in active_interfaces.iter().enumerate() {
        for interface in interfaces {
            incidence
                .entry(interface.clone())
                .or_default()
                .push(active_at);
        }
    }
    let mut pairs = BTreeSet::new();
    for members in incidence.values() {
        for (left_at, left) in members.iter().copied().enumerate() {
            for right in members.iter().copied().skip(left_at + 1) {
                pairs.insert((left, right));
            }
        }
    }
    pairs
}

fn canonicalize_active_population(
    active: &mut Vec<ActivePopulationPart>,
) -> Result<(), LiveConstituentError> {
    let mut keyed = Vec::new();
    keyed
        .try_reserve_exact(active.len())
        .map_err(|_| LiveConstituentError::Extent)?;
    for mut part in active.drain(..) {
        part.members.sort_unstable();
        part.touched.sort_unstable();
        keyed.push((part.body.native_words()?, part.members.clone(), part));
    }
    keyed.sort_by(|left, right| (&left.0, &left.1).cmp(&(&right.0, &right.1)));
    active.extend(keyed.into_iter().map(|(_, _, part)| part));
    Ok(())
}

fn union_sets(parent: &mut [usize], left: usize, right: usize) {
    let left = find_set(parent, left);
    let right = find_set(parent, right);
    if left == right {
        return;
    }
    if left < right {
        parent[right] = left;
    } else {
        parent[left] = right;
    }
}

fn append_copresent_seams(
    parts: &[PopulationPart],
    indexed_arms: &[IndexedExposedArms],
    left: usize,
    right: usize,
    seams: &mut Vec<PopulationSeam>,
    next_section_group: &mut usize,
) -> Result<(), LiveConstituentError> {
    let left_body = &parts[left].body;
    let right_body = &parts[right].body;
    for (left_section, left_arms) in indexed_arms[left].by_section.iter().enumerate() {
        if left_arms.is_empty() {
            continue;
        }
        let mut right_sections = Vec::new();
        for left_arm in left_arms {
            let interface = left_body.pins[left_arm.pin]
                .interface
                .as_ref()
                .ok_or(LiveConstituentError::Topology)?;
            if let Some(sections) = indexed_arms[right].sections_by_interface.get(interface) {
                right_sections.extend_from_slice(sections);
            }
        }
        right_sections.sort_unstable();
        right_sections.dedup();
        for right_section in right_sections {
            let right_arms = indexed_arms[right]
                .by_section
                .get(right_section)
                .ok_or(LiveConstituentError::Topology)?;
            if right_arms.is_empty() {
                continue;
            }
            let mut matches = Vec::new();
            for left_arm in left_arms.iter().copied() {
                let left_pin = &left_body.pins[left_arm.pin];
                let interface = left_pin
                    .interface
                    .as_ref()
                    .ok_or(LiveConstituentError::Topology)?;
                for right_arm in right_arms.iter().copied() {
                    let right_pin = &right_body.pins[right_arm.pin];
                    if right_pin.interface.as_ref() != Some(interface) {
                        continue;
                    }
                    // Co-present induced hands cancel when opposed. Equal hands remain as one
                    // oriented boundary residual in the newly completed joint chart.
                    let hand_residual = (left_arm.hand == right_arm.hand).then_some(right_arm.hand);
                    if let Some(pin) = LivePin::rebase_exposed(right_pin, left_pin, hand_residual) {
                        matches.push((left_arm, right_arm, pin));
                    }
                }
            }
            if !section_boundaries_are_covered(left_arms, &matches, true)
                || !section_boundaries_are_covered(right_arms, &matches, false)
            {
                continue;
            }
            let group = *next_section_group;
            *next_section_group = next_section_group
                .checked_add(1)
                .ok_or(LiveConstituentError::Extent)?;
            for (left_arm, right_arm, pin) in matches {
                push_population_seam(
                    seams,
                    left,
                    right,
                    left_arm,
                    right_arm,
                    pin,
                    PopulationSectionLink {
                        group,
                        left: left_section,
                        right: right_section,
                    },
                )?;
            }
        }
    }
    Ok(())
}

fn append_temporal_seams(
    parts: &[PopulationPart],
    indexed_arms: &[IndexedExposedArms],
    active: usize,
    standing: std::ops::Range<usize>,
    seams: &mut Vec<PopulationSeam>,
    next_section_group: &mut usize,
) -> Result<(), LiveConstituentError> {
    let arriving_body = &parts[active].body;
    for (arriving_section, arriving_arms) in indexed_arms[active].by_section.iter().enumerate() {
        if arriving_arms.is_empty() {
            continue;
        }
        let mut required = arriving_arms
            .iter()
            .map(|arm| arm.boundary)
            .collect::<Vec<_>>();
        required.sort_unstable();
        required.dedup();

        let mut candidates = Vec::new();
        for standing_at in standing.clone() {
            let held_body = &parts[standing_at].body;
            let mut held_sections = Vec::new();
            for arriving_arm in arriving_arms {
                let interface = arriving_body.pins[arriving_arm.pin]
                    .interface
                    .as_ref()
                    .ok_or(LiveConstituentError::Topology)?;
                if let Some(sections) = indexed_arms[standing_at]
                    .sections_by_interface
                    .get(interface)
                {
                    held_sections.extend_from_slice(sections);
                }
            }
            held_sections.sort_unstable();
            held_sections.dedup();
            for held_section in held_sections {
                let held_arms = indexed_arms[standing_at]
                    .by_section
                    .get(held_section)
                    .ok_or(LiveConstituentError::Topology)?;
                if held_arms.is_empty() {
                    continue;
                }
                let mut matches = Vec::new();
                for arriving_arm in arriving_arms.iter().copied() {
                    let arriving_pin = &arriving_body.pins[arriving_arm.pin];
                    let interface = arriving_pin
                        .interface
                        .as_ref()
                        .ok_or(LiveConstituentError::Topology)?;
                    for held_arm in held_arms.iter().copied() {
                        let held_pin = &held_body.pins[held_arm.pin];
                        if held_pin.interface.as_ref() != Some(interface) {
                            continue;
                        }
                        let hand_residual =
                            (arriving_arm.hand != held_arm.hand).then_some(arriving_arm.hand);
                        if let Some(pin) =
                            LivePin::rebase_exposed(arriving_pin, held_pin, hand_residual)
                        {
                            matches.push((held_arm, arriving_arm, pin));
                        }
                    }
                }
                if matches.is_empty() {
                    continue;
                }
                let mut arriving_boundaries = matches
                    .iter()
                    .map(|(_, arriving, _)| arriving.boundary)
                    .collect::<Vec<_>>();
                arriving_boundaries.sort_unstable();
                arriving_boundaries.dedup();
                candidates.push(TemporalSectionCandidate {
                    standing: standing_at,
                    held_section,
                    matches,
                    arriving_boundaries,
                });
            }
        }

        // A VALENCE LAW WAS TRIED HERE ON 2026-08-15 AND REFUTED BY THE SUITE. Kept as a note
        // because the refutation is the finding.
        //
        // `matches` is the complete bipartite product of compatible arms, and the hypothesis was
        // that an arm bonds once, so the product should have been a matching. The suite refused it:
        // `only_the_declared_interface_admits_a_seam_across_projection_and_grain` closes ONE
        // arriving arm against two standing bodies and asserts `touched == vec![0, 1]`, and
        // `shared_cofaces_condition_the_support_fan_and_recur_after_rest` is named for the same
        // geometry. **An arm is a face, and a face may be shared by several cofaces.** Constraining
        // it to one bond deletes the support fan.
        //
        // So the amplification is NOT the seam count. Measured: 40,381 member arms produced 80,664
        // seams — about two per arm, which a shared coface admits — while the composed body exposed
        // **80,685** arms, tracking the SEAM count. Composition doubles the arm population, and the
        // doubling is in the exposure rule below, not here.
        let covers = minimal_temporal_covers(&required, &candidates)?;
        for cover in covers {
            let group = *next_section_group;
            *next_section_group = group.checked_add(1).ok_or(LiveConstituentError::Extent)?;
            for candidate_at in cover {
                let candidate = candidates
                    .get(candidate_at)
                    .ok_or(LiveConstituentError::Topology)?;
                for (held_arm, arriving_arm, pin) in &candidate.matches {
                    push_population_seam(
                        seams,
                        candidate.standing,
                        active,
                        *held_arm,
                        *arriving_arm,
                        pin.clone(),
                        PopulationSectionLink {
                            group,
                            left: candidate.held_section,
                            right: arriving_section,
                        },
                    )?;
                }
            }
        }
    }
    Ok(())
}

fn minimal_temporal_covers(
    required: &[usize],
    candidates: &[TemporalSectionCandidate],
) -> Result<Vec<Vec<usize>>, LiveConstituentError> {
    fn is_subset(left: &[usize], right: &[usize]) -> bool {
        left.iter().all(|item| right.binary_search(item).is_ok())
    }

    fn visit(
        required: &[usize],
        candidates: &[TemporalSectionCandidate],
        selected: &mut Vec<usize>,
        covered: &mut Vec<usize>,
        complete: &mut Vec<Vec<usize>>,
    ) -> Result<(), LiveConstituentError> {
        let Some(next) = required
            .iter()
            .copied()
            .find(|boundary| covered.binary_search(boundary).is_err())
        else {
            let mut canonical = selected.clone();
            canonical.sort_unstable();
            canonical.dedup();
            if complete
                .iter()
                .any(|existing| is_subset(existing, &canonical))
            {
                return Ok(());
            }
            complete.retain(|existing| !is_subset(&canonical, existing));
            complete
                .try_reserve(1)
                .map_err(|_| LiveConstituentError::Extent)?;
            complete.push(canonical);
            return Ok(());
        };

        for (candidate_at, candidate) in candidates.iter().enumerate() {
            if candidate.arriving_boundaries.binary_search(&next).is_err()
                || selected.binary_search(&candidate_at).is_ok()
            {
                continue;
            }
            let selected_at = selected
                .binary_search(&candidate_at)
                .unwrap_or_else(|at| at);
            selected.insert(selected_at, candidate_at);
            let previous = covered.clone();
            covered.extend_from_slice(&candidate.arriving_boundaries);
            covered.sort_unstable();
            covered.dedup();
            visit(required, candidates, selected, covered, complete)?;
            *covered = previous;
            selected.remove(selected_at);
        }
        Ok(())
    }

    let mut complete = Vec::new();
    visit(
        required,
        candidates,
        &mut Vec::new(),
        &mut Vec::new(),
        &mut complete,
    )?;
    complete.sort();
    complete.dedup();
    Ok(complete)
}

fn section_boundaries_are_covered(
    required: &[ExposedArm],
    matches: &[(ExposedArm, ExposedArm, LivePin)],
    required_is_left: bool,
) -> bool {
    required.iter().all(|required_arm| {
        matches.iter().any(|(left, right, _)| {
            let matched = if required_is_left { left } else { right };
            matched.boundary == required_arm.boundary
        })
    })
}

#[allow(clippy::too_many_arguments)]
fn push_population_seam(
    seams: &mut Vec<PopulationSeam>,
    left: usize,
    right: usize,
    left_arm: ExposedArm,
    right_arm: ExposedArm,
    pin: LivePin,
    link: PopulationSectionLink,
) -> Result<(), LiveConstituentError> {
    if let Some(seam) = seams.iter_mut().find(|seam| {
        seam.left == left
            && seam.right == right
            && seam.left_arm.boundary == left_arm.boundary
            && seam.left_arm.path == left_arm.path
            && seam.left_arm.step == left_arm.step
            && seam.right_arm.boundary == right_arm.boundary
            && seam.right_arm.path == right_arm.path
            && seam.right_arm.step == right_arm.step
            && seam.pin == pin
    }) {
        match seam.section_links.binary_search(&link) {
            Ok(_) => {}
            Err(at) => seam.section_links.insert(at, link),
        }
        return Ok(());
    }
    seams
        .try_reserve(1)
        .map_err(|_| LiveConstituentError::Extent)?;
    seams.push(PopulationSeam {
        left,
        right,
        left_arm,
        right_arm,
        pin,
        section_links: vec![link],
    });
    Ok(())
}

fn compose_population_component(
    parts: &[PopulationPart],
    component: &[usize],
    seams: &[PopulationSeam],
) -> Result<(LiveConstituent, Vec<BTreeSet<PopulationSectionOrigin>>), LiveConstituentError> {
    let mut ordered = Vec::new();
    ordered
        .try_reserve_exact(component.len())
        .map_err(|_| LiveConstituentError::Extent)?;
    for at in component.iter().copied() {
        let species = match parts[at].origin {
            PopulationPartOrigin::Active(_) => 0u8,
            PopulationPartOrigin::Standing(_) => 1u8,
        };
        ordered.push((species, parts[at].body.native_words()?, at));
    }
    ordered.sort_by(|left, right| (left.0, &left.1, left.2).cmp(&(right.0, &right.1, right.2)));

    let mut plane_parent: Vec<usize> = (0..parts.len()).collect();
    for seam in seams {
        if !seam.pin.is_found() {
            union_sets(&mut plane_parent, seam.left, seam.right);
        }
    }
    for at in component.iter().copied() {
        plane_parent[at] = find_set(&mut plane_parent, at);
    }

    let first_active = ordered
        .iter()
        .find(|row| row.0 == 0)
        .map(|row| row.2)
        .ok_or(LiveConstituentError::Topology)?;
    let receiver_plane = plane_parent[first_active];
    let mut plane_axes: Vec<Option<LocalAxis>> = vec![None; parts.len()];
    plane_axes[receiver_plane] = Some(LocalAxis::new(0));
    let mut next_axis = 1u32;
    let mut axes_for_part: Vec<Option<Vec<LocalAxis>>> = vec![None; parts.len()];
    for (_, _, part_at) in &ordered {
        let body = &parts[*part_at].body;
        let plane = plane_parent[*part_at];
        let local_plane = match plane_axes[plane] {
            Some(axis) => axis,
            None => {
                let axis = LocalAxis::new(next_axis);
                next_axis = next_axis
                    .checked_add(1)
                    .ok_or(LiveConstituentError::Extent)?;
                plane_axes[plane] = Some(axis);
                axis
            }
        };
        let mut axes = Vec::new();
        axes.try_reserve_exact(word_usize(body.axis_count)?)
            .map_err(|_| LiveConstituentError::Extent)?;
        axes.push(local_plane);
        for _ in 1..body.axis_count {
            axes.push(LocalAxis::new(next_axis));
            next_axis = next_axis
                .checked_add(1)
                .ok_or(LiveConstituentError::Extent)?;
        }
        axes_for_part[*part_at] = Some(axes);
    }

    let mut cells = Vec::new();
    let mut incidences = Vec::new();
    let mut pins = Vec::new();
    let mut boundaries = Vec::new();
    let mut exposed = Vec::new();
    let mut maps: Vec<Option<ConstituentPartMap>> = Vec::new();
    maps.resize_with(parts.len(), || None);
    for (_, _, part_at) in &ordered {
        maps[*part_at] = Some(append_constituent_part(
            &parts[*part_at].body,
            axes_for_part[*part_at]
                .take()
                .ok_or(LiveConstituentError::Algebra)?,
            &mut cells,
            &mut incidences,
            &mut pins,
            &mut boundaries,
            &mut exposed,
        )?);
    }

    let apex_rank = cells
        .iter()
        .map(|cell| cell.dependency_rank)
        .max()
        .unwrap_or(0)
        .checked_add(1)
        .ok_or(LiveConstituentError::Extent)?;
    let apex_dimension = cells
        .iter()
        .map(|cell| cell.dimension)
        .max()
        .unwrap_or(0)
        .checked_add(1)
        .ok_or(LiveConstituentError::Extent)?;
    let grain = component
        .iter()
        .map(|at| parts[*at].body.grain)
        .max()
        .ok_or(LiveConstituentError::Topology)?
        .checked_add(1)
        .ok_or(LiveConstituentError::Extent)?;
    cells
        .try_reserve(1)
        .map_err(|_| LiveConstituentError::Extent)?;
    cells.push(LiveCell::new(apex_rank, apex_dimension, grain));

    let mut consumed = Vec::new();
    let (mut found_pins, mut open_pins) = (0usize, 0usize);
    let mut joined_sections: BTreeMap<usize, (Vec<(usize, usize)>, Vec<u32>)> = BTreeMap::new();
    let factor_expressions = parts
        .iter()
        .map(|part| part.body.support.root_expressions())
        .collect::<Result<Vec<_>, _>>()?;
    let mut participating_sections: Vec<Vec<bool>> = factor_expressions
        .iter()
        .map(|expressions| vec![false; expressions.len()])
        .collect();
    consumed
        .try_reserve_exact(seams.len().saturating_mul(2))
        .map_err(|_| LiveConstituentError::Extent)?;
    for seam in seams {
        let left_body = &parts[seam.left].body;
        let right_body = &parts[seam.right].body;
        let left_map = maps[seam.left]
            .as_ref()
            .ok_or(LiveConstituentError::Topology)?;
        let right_map = maps[seam.right]
            .as_ref()
            .ok_or(LiveConstituentError::Topology)?;
        let left_incidence = left_body.incidences[seam.left_arm.incidence];
        let right_incidence = right_body.incidences[seam.right_arm.incidence];
        let left_pin = left_map
            .pin_offset
            .checked_add(usize_u32(seam.left_arm.pin)?)
            .ok_or(LiveConstituentError::Extent)?;
        let right_pin = right_map
            .pin_offset
            .checked_add(usize_u32(seam.right_arm.pin)?)
            .ok_or(LiveConstituentError::Extent)?;
        consumed.push(left_pin);
        consumed.push(right_pin);

        let support = if seam.pin.is_found() {
            let imported = left_map.axes[0];
            if imported.local() == 0 {
                let axis = LocalAxis::new(next_axis);
                next_axis = next_axis
                    .checked_add(1)
                    .ok_or(LiveConstituentError::Extent)?;
                axis
            } else {
                imported
            }
        } else {
            let step = right_body.boundaries[seam.right_arm.boundary].paths[seam.right_arm.path]
                .steps[seam.right_arm.step];
            *right_map
                .axes
                .get(word_usize(step.support.local())?)
                .ok_or(LiveConstituentError::Algebra)?
        };

        let pin_at = usize_u32(pins.len())?;
        pins.try_reserve(1)
            .map_err(|_| LiveConstituentError::Extent)?;
        pins.push(seam.pin.clone());
        let incidence_at = usize_u32(incidences.len())?;
        incidences
            .try_reserve(1)
            .map_err(|_| LiveConstituentError::Extent)?;
        incidences.push(LiveIncidence::new(
            left_map
                .cell_offset
                .checked_add(left_incidence.to)
                .ok_or(LiveConstituentError::Extent)?,
            right_map
                .cell_offset
                .checked_add(right_incidence.from)
                .ok_or(LiveConstituentError::Extent)?,
            LiveIncidenceKind::Transport,
            seam.right_arm.hand,
            pin_at,
        ));
        let winding = seam
            .pin
            .formed
            .map_or(WindingQuantum::None, |formed| formed.winding);
        let path = LivePath::from_steps(
            vec![LivePathStep::new(incidence_at, support, winding)],
            &incidences,
            &pins,
        )?;
        let seam_boundary = usize_u32(boundaries.len())?;
        boundaries.push(LiveBoundary::new(seam.right_arm.hand, vec![path]));
        for link in &seam.section_links {
            *participating_sections
                .get_mut(seam.left)
                .and_then(|sections| sections.get_mut(link.left))
                .ok_or(LiveConstituentError::Topology)? = true;
            *participating_sections
                .get_mut(seam.right)
                .and_then(|sections| sections.get_mut(link.right))
                .ok_or(LiveConstituentError::Topology)? = true;
            let joined = joined_sections
                .entry(link.group)
                .or_insert_with(|| (Vec::new(), Vec::new()));
            joined.0.push((seam.left, link.left));
            joined.0.push((seam.right, link.right));
            joined.1.push(seam_boundary);
        }
        if seam.pin.is_found() {
            found_pins += 1;
        }
        if seam.pin.is_open() {
            open_pins += 1;
        }
        // NOT EXPOSING INTERIOR SEAMS WAS TRIED ON 2026-08-15 AND THE SUITE REFUTED IT — the
        // third refutation of construction 1, and the sharpest.
        //
        // Every seam reaching this function is interior by construction (the caller filters
        // `component_seams` to both-endpoints-in-component), so it looked like `∂∂ = 0`: a region
        // should not publish its own interior as boundary. Restricting the exposure to FOUND seams
        // broke three tests, and their names are the law:
        // `opposed_copresent_leaders_close_while_equal_hands_remain_open_residual`,
        // `a_later_exact_boundary_rides_the_opening_without_rewriting_its_earlier_scope`, and
        // `regional_exposed_well_rebases_triangles_and_open_foil_changes_the_later_probe`.
        //
        // **An OPEN bond is not interior. It is unresolved — and an unresolved bond is still a port,
        // because a later arrival rides exactly that opening.** The region genuinely advertises its
        // unresolved bonds; that is what makes it able to keep relating.
        //
        // So the port doubling is not a defect of this rule. It is a consequence of **how many seams
        // stay open**, which is the null-face finding: nothing rides, so nothing closes, so
        // everything is exposed. Construction 1's real content is upstream — give the faces geometry
        // so a seam can ride and close.
        if seam.pin.is_found() || seam.pin.is_open() {
            exposed.push(pin_at);
        }
    }
    consumed.sort_unstable();
    consumed.dedup();
    exposed.retain(|pin| consumed.binary_search(pin).is_err());
    exposed.sort_unstable();
    exposed.dedup();

    let mut carried_factors =
        BTreeMap::<LiveSupportExpression, BTreeSet<PopulationSectionOrigin>>::new();
    for part_at in component {
        let map = maps[*part_at]
            .as_ref()
            .ok_or(LiveConstituentError::Topology)?;
        for (section_at, expression) in factor_expressions[*part_at].iter().enumerate() {
            if participating_sections[*part_at][section_at] {
                continue;
            }
            carried_factors
                .entry(expression.rebased(map.boundary_offset)?)
                .or_default()
                .extend(
                    parts[*part_at]
                        .section_lineages
                        .get(section_at)
                        .ok_or(LiveConstituentError::Topology)?
                        .iter()
                        .copied(),
                );
        }
    }
    for (_, (mut section_nodes, mut seam_boundaries)) in joined_sections {
        section_nodes.sort_unstable();
        section_nodes.dedup();
        let mut causes = Vec::new();
        let mut lineage = BTreeSet::new();
        for (part_at, section_at) in section_nodes {
            let map = maps[part_at]
                .as_ref()
                .ok_or(LiveConstituentError::Topology)?;
            causes.push(
                factor_expressions
                    .get(part_at)
                    .and_then(|expressions| expressions.get(section_at))
                    .ok_or(LiveConstituentError::Topology)?
                    .rebased(map.boundary_offset)?,
            );
            lineage.extend(
                parts[part_at]
                    .section_lineages
                    .get(section_at)
                    .ok_or(LiveConstituentError::Topology)?
                    .iter()
                    .copied(),
            );
        }
        seam_boundaries.sort_unstable();
        seam_boundaries.dedup();
        carried_factors
            .entry(LiveSupportExpression::join(causes, seam_boundaries)?)
            .or_default()
            .extend(lineage);
    }
    let support = LiveSupportFamily::from_expressions(carried_factors.keys().cloned().collect())?;

    let body = LiveConstituent::with_support_family(
        grain, next_axis, cells, incidences, pins, boundaries, exposed, support,
    )?
    .compressed()?;
    {
        // Does composition conserve arms? A seam consumes two, so the composite's exposed arm
        // population should be at most the members' total minus twice the seams. Measured rather
        // than assumed.
        let member_arms: usize = component
            .iter()
            .copied()
            .filter_map(|at| parts[at].body.indexed_exposed_arms().ok())
            .map(|arms| arms.by_section.iter().map(Vec::len).sum::<usize>())
            .sum();
        let composed_arms = body
            .indexed_exposed_arms()
            .map(|arms| arms.by_section.iter().map(Vec::len).sum::<usize>())
            .unwrap_or(0);
        seam_trace(&format_args!(
            "  COMPOSE members {} member_arms {} seams {} found {} open {} -> composed_arms {} | rode {} no_read {} wound {} hand {} | both_null {} arriving_null {} held_null {} zero_reach {} | pole_on_from {} pole_on_to {} pole_distinct {} sweep_idle {} relata_coincide {} basis_identity {} distinct_place_words {} | CENSUS places {} triples {} triangle {} area {} collinear {} would_found {} arrow_horizon {} | dark {} f_cell {} f_cplx {} folded {} k_moved {} k_still {} | grain1 {} deeper {} after_live {} after_dead {} | held_live_any {} ARMED {} held_not_live {} no_emission {} ride {} found {} | BPRIME supplied {} chi_forms {} chi_none {} wound {} flat {}",
            component.len(),
            member_arms,
            seams.len(),
            found_pins,
            open_pins,
            composed_arms,
            RODE.load(core::sync::atomic::Ordering::Relaxed),
            NO_PROJECTIVE_READ.load(core::sync::atomic::Ordering::Relaxed),
            WOUND_COMPARISON.load(core::sync::atomic::Ordering::Relaxed),
            HAND_RESIDUAL.load(core::sync::atomic::Ordering::Relaxed),
            BOTH_NULL.load(core::sync::atomic::Ordering::Relaxed),
            ARRIVING_NULL.load(core::sync::atomic::Ordering::Relaxed),
            HELD_NULL.load(core::sync::atomic::Ordering::Relaxed),
            ZERO_REACH.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::POLE_ON_FROM.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::POLE_ON_TO.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::POLE_DISTINCT.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::POLE_SWEEP_IDLE.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::RELATA_COINCIDE.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::BASIS_IDENTITY.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::DISTINCT_PLACES
                .get()
                .and_then(|m| m.lock().ok().map(|s| s.len()))
                .unwrap_or(0),
            crate::live_current::CENSUS_PLACES
                .get()
                .and_then(|m| m.lock().ok().map(|s| s.len()))
                .unwrap_or(0),
            crate::live_current::CENSUS_TRIPLES
                .get()
                .and_then(|m| m.lock().ok().map(|s| s.len()))
                .unwrap_or(0),
            crate::live_current::TRIANGLE.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::TRIANGLE_WITH_AREA.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::TRIANGLE_COLLINEAR.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::WOULD_FOUND.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::ARROW_AT_HORIZON.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::EVENT_WHOLLY_DARK.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::FOUNDER_CELL.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::FOUNDER_COMPLEX.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::FOUNDER_FOLDED.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::CHANNEL_MOVED.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::CHANNEL_STILL.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::GRAIN_ONE.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::GRAIN_DEEPER.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::HELD_LIVE_AFTER_FOUNDER.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::HELD_DEAD_AFTER_FOUNDER.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::HELD_LIVE_ANY.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::ARMED.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::ARMED_HELD_NOT_LIVE.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::ARMED_NO_EMISSION.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::ARMED_RIDE.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::ARMED_FOUND.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::BPRIME_HELD_SUPPLIED.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::BPRIME_CHI_FORMS.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::BPRIME_CHI_NONE.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::BPRIME_WOUND.load(core::sync::atomic::Ordering::Relaxed),
            crate::live_current::BPRIME_FLAT.load(core::sync::atomic::Ordering::Relaxed)
        ));
    }
    let section_lineages = body
        .support
        .root_expressions()?
        .into_iter()
        .map(|expression| {
            carried_factors
                .remove(&expression)
                .ok_or(LiveConstituentError::Topology)
        })
        .collect::<Result<Vec<_>, _>>()?;
    if !carried_factors.is_empty() || body.support.factor_count() != section_lineages.len() {
        return Err(LiveConstituentError::Topology);
    }
    Ok((body, section_lineages))
}

#[allow(clippy::too_many_arguments)]
fn append_constituent_part(
    constituent: &LiveConstituent,
    axes: Vec<LocalAxis>,
    cells: &mut Vec<LiveCell>,
    incidences: &mut Vec<LiveIncidence>,
    pins: &mut Vec<LivePin>,
    boundaries: &mut Vec<LiveBoundary>,
    exposed: &mut Vec<u32>,
) -> Result<ConstituentPartMap, LiveConstituentError> {
    if axes.len() != word_usize(constituent.axis_count)? {
        return Err(LiveConstituentError::Algebra);
    }
    let cell_offset = usize_u32(cells.len())?;
    let incidence_offset = usize_u32(incidences.len())?;
    let pin_offset = usize_u32(pins.len())?;
    let boundary_offset = usize_u32(boundaries.len())?;
    cells
        .try_reserve_exact(constituent.cells.len())
        .map_err(|_| LiveConstituentError::Extent)?;
    cells.extend_from_slice(&constituent.cells);
    pins.try_reserve_exact(constituent.pins.len())
        .map_err(|_| LiveConstituentError::Extent)?;
    pins.extend_from_slice(&constituent.pins);
    incidences
        .try_reserve_exact(constituent.incidences.len())
        .map_err(|_| LiveConstituentError::Extent)?;
    for incidence in &constituent.incidences {
        incidences.push(LiveIncidence::new(
            incidence
                .from
                .checked_add(cell_offset)
                .ok_or(LiveConstituentError::Extent)?,
            incidence
                .to
                .checked_add(cell_offset)
                .ok_or(LiveConstituentError::Extent)?,
            incidence.kind,
            incidence.hand,
            incidence
                .pin
                .checked_add(pin_offset)
                .ok_or(LiveConstituentError::Extent)?,
        ));
    }
    boundaries
        .try_reserve_exact(constituent.boundaries.len())
        .map_err(|_| LiveConstituentError::Extent)?;
    for boundary in &constituent.boundaries {
        let mut paths = Vec::new();
        paths
            .try_reserve_exact(boundary.paths.len())
            .map_err(|_| LiveConstituentError::Extent)?;
        for path in &boundary.paths {
            paths.push(path.rebased(incidence_offset, &axes)?);
        }
        boundaries.push(LiveBoundary::new(boundary.hand, paths));
    }
    exposed
        .try_reserve_exact(constituent.exposed.len())
        .map_err(|_| LiveConstituentError::Extent)?;
    for pin in &constituent.exposed {
        exposed.push(
            pin.checked_add(pin_offset)
                .ok_or(LiveConstituentError::Extent)?,
        );
    }
    Ok(ConstituentPartMap {
        cell_offset,
        pin_offset,
        boundary_offset,
        axes,
    })
}

pub(crate) fn cellular_cycle_edges(
    cells: usize,
    incidences: &[LiveIncidence],
    incidence_use: &[u32],
) -> Result<Vec<bool>, LiveConstituentError> {
    let mut adjacency = Vec::new();
    adjacency
        .try_reserve_exact(cells)
        .map_err(|_| LiveConstituentError::Extent)?;
    adjacency.resize_with(cells, Vec::new);
    let mut cycle = vec![false; incidences.len()];
    for (edge, incidence) in incidences.iter().copied().enumerate() {
        if incidence_use.get(edge).copied().unwrap_or(0) == 0 {
            continue;
        }
        let from = word_usize(incidence.from)?;
        let to = word_usize(incidence.to)?;
        if from == to {
            cycle[edge] = true;
            continue;
        }
        adjacency[from]
            .try_reserve(1)
            .map_err(|_| LiveConstituentError::Extent)?;
        adjacency[to]
            .try_reserve(1)
            .map_err(|_| LiveConstituentError::Extent)?;
        adjacency[from].push((to, edge));
        adjacency[to].push((from, edge));
    }

    fn visit(
        node: usize,
        parent_edge: Option<usize>,
        adjacency: &[Vec<(usize, usize)>],
        discovered: &mut [usize],
        low: &mut [usize],
        next: &mut usize,
        bridge: &mut [bool],
    ) {
        *next += 1;
        discovered[node] = *next;
        low[node] = *next;
        for &(other, edge) in &adjacency[node] {
            if Some(edge) == parent_edge {
                continue;
            }
            if discovered[other] == 0 {
                visit(other, Some(edge), adjacency, discovered, low, next, bridge);
                low[node] = low[node].min(low[other]);
                if low[other] > discovered[node] {
                    bridge[edge] = true;
                }
            } else {
                low[node] = low[node].min(discovered[other]);
            }
        }
    }

    let mut discovered = vec![0usize; cells];
    let mut low = vec![0usize; cells];
    let mut bridge = vec![false; incidences.len()];
    let mut next = 0usize;
    for node in 0..cells {
        if discovered[node] == 0 && !adjacency[node].is_empty() {
            visit(
                node,
                None,
                &adjacency,
                &mut discovered,
                &mut low,
                &mut next,
                &mut bridge,
            );
        }
    }
    for edge in 0..incidences.len() {
        if incidence_use.get(edge).copied().unwrap_or(0) != 0 && !bridge[edge] {
            cycle[edge] = true;
        }
    }
    Ok(cycle)
}

fn path_emanation(
    steps: &[LivePathStep],
    incidences: &[LiveIncidence],
    pins: &[LivePin],
) -> Result<(SparseTransport, Rung, Rung), LiveConstituentError> {
    let mut transport = SparseTransport::identity();
    let mut this_way = Rung::ZERO;
    let mut that_way = Rung::ZERO;
    for step in steps {
        let incidence = incidences
            .get(word_usize(step.incidence)?)
            .ok_or(LiveConstituentError::Topology)?;
        let pin = pins
            .get(word_usize(incidence.pin)?)
            .ok_or(LiveConstituentError::Topology)?;
        transport = transport.product(&pin.factor(step.support));
        if step.winding != WindingQuantum::None
            && pin
                .formed
                .is_none_or(|formed| formed.winding != step.winding)
        {
            return Err(LiveConstituentError::Algebra);
        }
        match step.winding {
            WindingQuantum::None => {}
            WindingQuantum::ThisWay => this_way = this_way.add(Rung::of(1)),
            WindingQuantum::ThatWay => that_way = that_way.add(Rung::of(1)),
        }
    }
    Ok((transport, this_way, that_way))
}

fn usize_u32(value: usize) -> Result<u32, LiveConstituentError> {
    u32::try_from(value).map_err(|_| LiveConstituentError::Extent)
}

fn word_usize(value: u32) -> Result<usize, LiveConstituentError> {
    usize::try_from(value).map_err(|_| LiveConstituentError::Extent)
}

fn take(words: &[u32], cursor: &mut usize) -> Result<u32, LiveConstituentError> {
    let value = *words
        .get(*cursor)
        .ok_or(LiveConstituentError::InvalidWire)?;
    *cursor = cursor.checked_add(1).ok_or(LiveConstituentError::Extent)?;
    Ok(value)
}

fn push_u64(words: &mut Vec<u32>, value: u64) {
    words.push(value as u32);
    words.push((value >> 32) as u32);
}

fn take_u64(words: &[u32], cursor: &mut usize) -> Result<u64, LiveConstituentError> {
    let lo = take(words, cursor)? as u64;
    let hi = take(words, cursor)? as u64;
    Ok(lo | (hi << 32))
}

fn push_receiver_fiber(words: &mut Vec<u32>, fiber: Option<&ReceiverFiberIdentity>) {
    let (schema, body) = fiber.map_or((0, &[][..]), |fiber| (fiber.schema, &*fiber.words));
    push_u64(words, schema);
    push_u64(words, body.len() as u64);
    words.extend_from_slice(body);
}

fn take_receiver_fiber(
    words: &[u32],
    cursor: &mut usize,
) -> Result<ReceiverFiberIdentity, LiveConstituentError> {
    let schema = take_u64(words, cursor)?;
    let extent =
        usize::try_from(take_u64(words, cursor)?).map_err(|_| LiveConstituentError::Extent)?;
    let end = cursor
        .checked_add(extent)
        .ok_or(LiveConstituentError::Extent)?;
    let body = words
        .get(*cursor..end)
        .ok_or(LiveConstituentError::InvalidWire)?;
    *cursor = end;
    Ok(ReceiverFiberIdentity::new(schema, Arc::<[u32]>::from(body)))
}

fn push_cog(words: &mut Vec<u32>, cog: Cog) {
    words.extend((0..COG_WORDS).map(|word| cog_packed_word(cog, word)));
}

fn take_cog(words: &[u32], cursor: &mut usize) -> Result<Cog, LiveConstituentError> {
    if !packed_cog_is_canonical(words, *cursor) {
        return Err(LiveConstituentError::InvalidWire);
    }
    let cog = read_cog(words, *cursor);
    *cursor = cursor
        .checked_add(COG_WORDS)
        .ok_or(LiveConstituentError::Extent)?;
    Ok(cog)
}

fn hand_word(hand: IncidenceHand) -> u32 {
    match hand {
        IncidenceHand::Against => 0,
        IncidenceHand::With => 1,
    }
}

fn read_hand(word: u32) -> Result<IncidenceHand, LiveConstituentError> {
    match word {
        0 => Ok(IncidenceHand::Against),
        1 => Ok(IncidenceHand::With),
        _ => Err(LiveConstituentError::InvalidWire),
    }
}

fn interface_origin_word(origin: InterfaceCapabilityOrigin) -> u32 {
    match origin {
        InterfaceCapabilityOrigin::Inherited => 0,
        InterfaceCapabilityOrigin::ReceiverCaused => 1,
    }
}

fn read_interface_origin(word: u32) -> Result<InterfaceCapabilityOrigin, LiveConstituentError> {
    match word {
        0 => Ok(InterfaceCapabilityOrigin::Inherited),
        1 => Ok(InterfaceCapabilityOrigin::ReceiverCaused),
        _ => Err(LiveConstituentError::InvalidWire),
    }
}

fn winding_word(winding: WindingQuantum) -> u32 {
    winding as u32
}

fn read_winding(word: u32) -> Result<WindingQuantum, LiveConstituentError> {
    match word {
        0 => Ok(WindingQuantum::None),
        1 => Ok(WindingQuantum::ThisWay),
        2 => Ok(WindingQuantum::ThatWay),
        _ => Err(LiveConstituentError::InvalidWire),
    }
}

fn deed_word(deed: FeltDeed) -> u32 {
    match deed {
        FeltDeed::Ride => 0,
        FeltDeed::FoundThis => 1,
        FeltDeed::FoundThat => 2,
        FeltDeed::Dark => 3,
    }
}

fn read_deed(word: u32) -> Result<FeltDeed, LiveConstituentError> {
    match word {
        0 => Ok(FeltDeed::Ride),
        1 => Ok(FeltDeed::FoundThis),
        2 => Ok(FeltDeed::FoundThat),
        3 => Ok(FeltDeed::Dark),
        _ => Err(LiveConstituentError::InvalidWire),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use body::arrow::Arrow;

    fn exposed_pin(reach: i64) -> LivePin {
        let meeting = Face {
            arrow: Arrow {
                reach: Cog::lit(reach),
                aim: Cog::lit(3),
                cross: Cog::ZERO,
            },
        };
        let held = Face {
            arrow: Arrow {
                reach: Cog::lit(11),
                aim: Cog::lit(2),
                cross: Cog::ZERO,
            },
        };
        let chi = meeting.chi_against(&held).unwrap();
        LivePin {
            meeting,
            held,
            held_live: true,
            interface: Some(InterfaceCapability::new(1, reach as u64)),
            projected_residual: Some(chi),
            formed: Some(FormedPin {
                position: cast_position(chi),
                chi,
                winding: WindingQuantum::None,
                deed: FeltDeed::Ride,
            }),
        }
    }

    fn one_exposed_arm(pin: LivePin, cell_grain: u32) -> LiveConstituent {
        one_exposed_arm_with_hand(pin, cell_grain, IncidenceHand::With)
    }

    fn one_exposed_arm_with_hand(
        pin: LivePin,
        cell_grain: u32,
        hand: IncidenceHand,
    ) -> LiveConstituent {
        let incidences = vec![LiveIncidence::new(
            0,
            1,
            LiveIncidenceKind::Transport,
            hand,
            0,
        )];
        let pins = vec![pin];
        let path = LivePath::from_steps(
            vec![LivePathStep::new(
                0,
                LocalAxis::new(0),
                WindingQuantum::None,
            )],
            &incidences,
            &pins,
        )
        .unwrap();
        LiveConstituent::new(
            2,
            1,
            vec![
                LiveCell::new(0, 0, cell_grain),
                LiveCell::new(0, 0, cell_grain),
                LiveCell::new(1, 1, 2),
            ],
            incidences,
            pins,
            vec![LiveBoundary::new(hand, vec![path])],
            vec![0],
        )
        .unwrap()
    }

    fn capacitive_hyperedge(reaches: &[i64]) -> LiveConstituent {
        assert!(!reaches.is_empty());
        let pins = reaches.iter().copied().map(exposed_pin).collect::<Vec<_>>();
        let incidences = (0..pins.len())
            .map(|pin| {
                LiveIncidence::new(
                    0,
                    1,
                    LiveIncidenceKind::Transport,
                    IncidenceHand::With,
                    pin as u32,
                )
            })
            .collect::<Vec<_>>();
        let boundaries = (0..pins.len())
            .map(|at| {
                let path = LivePath::from_steps(
                    vec![LivePathStep::new(
                        at as u32,
                        LocalAxis::new(at as u32),
                        WindingQuantum::None,
                    )],
                    &incidences,
                    &pins,
                )
                .unwrap();
                LiveBoundary::new(IncidenceHand::With, vec![path])
            })
            .collect::<Vec<_>>();
        LiveConstituent::new(
            2,
            reaches.len() as u32,
            vec![
                LiveCell::new(0, 0, 0),
                LiveCell::new(0, 0, 0),
                LiveCell::new(1, 1, 2),
            ],
            incidences,
            pins,
            boundaries,
            (0..reaches.len() as u32).collect(),
        )
        .unwrap()
    }

    #[test]
    fn local_blades_are_exterior_until_a_receiver_supplies_a_metric() {
        let a = LocalBlade::axis(LocalAxis::new(1));
        let b = LocalBlade::axis(LocalAxis::new(2));

        assert_eq!(a.product(&a), None);
        assert_eq!(
            a.product(&b),
            Some((
                LocalBlade {
                    axes: vec![LocalAxis::new(1), LocalAxis::new(2)]
                },
                false
            ))
        );
        assert_eq!(
            b.product(&a),
            Some((
                LocalBlade {
                    axes: vec![LocalAxis::new(1), LocalAxis::new(2)]
                },
                true
            ))
        );
    }

    #[test]
    fn repeated_support_annihilates_only_its_two_blade_term() {
        let support = LocalAxis::new(1);
        let factor = SparseTransport::factor(
            Chi {
                other: Cog::lit(1),
                same: Cog::lit(1),
            },
            support,
        );
        let product = factor.product(&factor);

        assert_eq!(product.terms.len(), 2);
        assert_eq!(product.terms[0].blade, LocalBlade::scalar());
        assert_eq!(product.terms[0].coefficient, Cog::lit(1));
        assert_eq!(product.terms[1].blade, LocalBlade::axis(support));
        assert_eq!(product.terms[1].coefficient, Cog::lit(2));
    }

    #[test]
    fn compression_emits_an_exact_later_contact_boundary_certificate() {
        let pin = exposed_pin(7);
        let incidences = vec![LiveIncidence::new(
            0,
            1,
            LiveIncidenceKind::Transport,
            IncidenceHand::With,
            0,
        )];
        let path = LivePath::from_steps(
            vec![LivePathStep::new(
                0,
                LocalAxis::new(0),
                WindingQuantum::None,
            )],
            &incidences,
            &[pin.clone()],
        )
        .unwrap();
        let before = LiveConstituent::new(
            2,
            1,
            vec![
                LiveCell::new(0, 0, 0),
                LiveCell::new(0, 0, 0),
                LiveCell::new(1, 1, 2),
            ],
            incidences,
            vec![pin],
            vec![LiveBoundary::new(IncidenceHand::With, vec![path])],
            Vec::new(),
        )
        .unwrap();
        let behavior = before.boundary_behavior().unwrap();
        let (after, certificate) = before.compress_certified().unwrap();

        assert_eq!(certificate.behavior(), &behavior);
        assert_eq!(after.boundary_behavior().unwrap(), behavior);
        assert_eq!(
            (certificate.before_cells(), certificate.after_cells()),
            (3, 1)
        );
        assert_eq!(
            (
                certificate.before_incidences(),
                certificate.after_incidences()
            ),
            (1, 0)
        );
        assert!(after.boundaries()[0].paths()[0].interior_folded());
        assert!(after.boundaries()[0].paths()[0].steps().is_empty());
        assert!(!after.boundaries()[0].paths()[0]
            .transport()
            .terms()
            .is_empty());
    }

    #[test]
    fn declared_outgoing_boundary_releases_the_other_formed_face() {
        let pins = vec![exposed_pin(7), exposed_pin(13)];
        let incidences = vec![
            LiveIncidence::new(0, 1, LiveIncidenceKind::Transport, IncidenceHand::With, 0),
            LiveIncidence::new(
                2,
                3,
                LiveIncidenceKind::Transport,
                IncidenceHand::Against,
                1,
            ),
        ];
        let paths = [
            LivePath::from_steps(
                vec![LivePathStep::new(
                    0,
                    LocalAxis::new(0),
                    WindingQuantum::None,
                )],
                &incidences,
                &pins,
            )
            .unwrap(),
            LivePath::from_steps(
                vec![LivePathStep::new(
                    1,
                    LocalAxis::new(0),
                    WindingQuantum::None,
                )],
                &incidences,
                &pins,
            )
            .unwrap(),
        ];
        let body = LiveConstituent::new(
            2,
            1,
            vec![
                LiveCell::new(0, 0, 0),
                LiveCell::new(0, 0, 0),
                LiveCell::new(0, 0, 0),
                LiveCell::new(0, 0, 0),
            ],
            incidences,
            pins,
            vec![
                LiveBoundary::new(IncidenceHand::With, vec![paths[0].clone()]),
                LiveBoundary::new(IncidenceHand::Against, vec![paths[1].clone()]),
            ],
            vec![0, 1],
        )
        .unwrap();

        let factor = body.outgoing_boundary_factor(&[1], 3).unwrap();
        assert_eq!(factor.grain(), 3);
        assert_eq!(factor.boundaries().len(), 1);
        assert_eq!(factor.exposed().len(), 1);
        assert_eq!(
            factor.pins()[factor.exposed()[0] as usize].interface(),
            Some(InterfaceCapability::new(1, 13))
        );
        assert!(!factor
            .pins()
            .iter()
            .any(|pin| { pin.interface() == Some(InterfaceCapability::new(1, 7)) }));
        assert!(!factor.has_same_exposed_boundary(&body).unwrap());
    }

    #[test]
    fn outgoing_factor_is_accepted_only_after_the_other_boundary_closes() {
        let context = exposed_pin(7);
        let output = exposed_pin(13);
        let incidences = vec![
            LiveIncidence::new(0, 1, LiveIncidenceKind::Transport, IncidenceHand::With, 0),
            LiveIncidence::new(
                2,
                3,
                LiveIncidenceKind::Transport,
                IncidenceHand::Against,
                1,
            ),
        ];
        let pins = vec![context.clone(), output];
        let arriving = LiveConstituent::new(
            2,
            1,
            vec![
                LiveCell::new(0, 0, 0),
                LiveCell::new(0, 0, 0),
                LiveCell::new(0, 0, 0),
                LiveCell::new(0, 0, 0),
            ],
            incidences.clone(),
            pins.clone(),
            vec![
                LiveBoundary::new(
                    IncidenceHand::With,
                    vec![LivePath::from_steps(
                        vec![LivePathStep::new(
                            0,
                            LocalAxis::new(0),
                            WindingQuantum::None,
                        )],
                        &incidences,
                        &pins,
                    )
                    .unwrap()],
                ),
                LiveBoundary::new(
                    IncidenceHand::Against,
                    vec![LivePath::from_steps(
                        vec![LivePathStep::new(
                            1,
                            LocalAxis::new(0),
                            WindingQuantum::None,
                        )],
                        &incidences,
                        &pins,
                    )
                    .unwrap()],
                ),
            ],
            vec![0, 1],
        )
        .unwrap();
        let prior = one_exposed_arm(context, 0);
        let (touched, completed) = arriving.close_against(&[prior]).unwrap();
        assert_eq!(touched, vec![0]);

        let output_factor = arriving
            .outgoing_boundary_factor(&[1], completed.grain())
            .unwrap();
        assert!(output_factor.has_same_exposed_boundary(&completed).unwrap());

        let unclosed_context = arriving
            .outgoing_boundary_factor(&[0], completed.grain())
            .unwrap();
        assert!(!unclosed_context
            .has_same_exposed_boundary(&completed)
            .unwrap());
    }

    #[test]
    fn a_front_is_informed_only_within_its_vision_and_the_excluded_are_retained() {
        // CONSTRUCTION 3 — vision, and both arms must fire or the bound proves nothing.
        //
        // A front that has not reached its declared depth is informed; one that has is not, and what
        // it could not be informed about is RETAINED rather than dropped. That is the traffic law's
        // clause — a unit physically cannot be informed about what is not within its vision — and
        // the population it could not see is the null its reading is taken against.
        let inside = FrontVision {
            depth: 2,
            horizon: 4,
            co_present: 1,
        };
        assert!(inside.admits_another_hop());

        let at_the_edge = FrontVision {
            depth: 4,
            horizon: 4,
            co_present: 1,
        };
        assert!(!at_the_edge.admits_another_hop());

        // The inherited setting bounds nothing, so a machine that never declares a vision behaves
        // exactly as before.
        assert!(FrontVision::unbounded().admits_another_hop());
    }

    #[test]
    fn co_present_demand_dilates_a_contended_factor_and_a_quiet_one_crosses() {
        // CONSTRUCTION 2 — predicted contention at the seam, through the same junction law the
        // transport carrier uses: demand over capacity.
        //
        // One front asking a factor of multiplicity one is matched and crosses in a single round.
        let quiet = CountedCrossing::meet(1, 1).expect("positive");
        assert_eq!(quiet.service_rounds(), 1);
        assert!(quiet.crosses_within(8));

        // Sixty co-present fronts asking the same single-multiplicity factor is a mismatch, and it
        // dilates past a declared horizon of eight rather than admitting all sixty whole.
        let contended = CountedCrossing::meet(60, 1).expect("positive");
        assert!(contended.service_rounds() > 8);
        assert!(!contended.crosses_within(8));

        // And the dilation is a function of the RATIO, so it is invariant under a common rescaling
        // — a count in this position could not be.
        assert_eq!(
            CountedCrossing::meet(60, 1)
                .expect("positive")
                .service_rounds(),
            CountedCrossing::meet(600, 10)
                .expect("positive")
                .service_rounds()
        );
    }

    #[test]
    fn only_the_declared_interface_admits_a_seam_across_projection_and_grain() {
        let prior = one_exposed_arm(exposed_pin(7), 0);
        let equal_place_other_well = one_exposed_arm(exposed_pin(13), 0);
        let equal_well_other_grain = one_exposed_arm(exposed_pin(7), 1);
        assert_eq!(
            prior.pins()[0].transport_position(),
            equal_place_other_well.pins()[0].transport_position()
        );

        let (touched, unchanged) = equal_place_other_well
            .close_against(std::slice::from_ref(&prior))
            .unwrap();
        assert!(touched.is_empty());
        assert_eq!(unchanged, equal_place_other_well);

        let (touched, replacement) = equal_well_other_grain
            .close_against(std::slice::from_ref(&prior))
            .unwrap();
        assert_eq!(touched, vec![0]);
        assert_eq!(replacement.grain(), 3);

        let compatible = one_exposed_arm(exposed_pin(7), 0);
        let (touched, replacement) = compatible
            .close_against(std::slice::from_ref(&prior))
            .unwrap();
        assert_eq!(touched, vec![0]);
        assert_eq!(replacement.grain(), 3);

        let mut sibling = prior.clone();
        sibling.pins[0].held.arrow.reach = Cog::lit(17);
        let compatible = one_exposed_arm(exposed_pin(7), 0);
        let (touched, replacement) = compatible.close_against(&[prior, sibling]).unwrap();
        assert_eq!(touched, vec![0, 1]);
        assert_eq!(replacement.grain(), 3);
    }

    #[test]
    fn opposed_copresent_leaders_close_while_equal_hands_remain_open_residual() {
        let with = one_exposed_arm_with_hand(exposed_pin(7), 0, IncidenceHand::With);
        let against = one_exposed_arm_with_hand(exposed_pin(7), 0, IncidenceHand::Against);
        let opposed =
            LiveConstituent::close_population_against(&[with.clone(), against], &[]).unwrap();
        assert_eq!(opposed.len(), 1);
        assert_eq!(opposed[0].members(), &[0, 1]);
        assert!(opposed[0].touched().is_empty());
        assert_eq!(opposed[0].replacement().grain(), 3);
        assert!(opposed[0].replacement().exposed().is_empty());
        let reversed = LiveConstituent::close_population_against(
            &[
                one_exposed_arm_with_hand(exposed_pin(7), 0, IncidenceHand::Against),
                with.clone(),
            ],
            &[],
        )
        .unwrap();
        assert_eq!(opposed[0].replacement(), reversed[0].replacement());

        let equal =
            LiveConstituent::close_population_against(&[with.clone(), with.clone()], &[]).unwrap();
        assert_eq!(equal.len(), 1);
        assert_eq!(equal[0].replacement().grain(), 3);
        assert_eq!(equal[0].replacement().exposed().len(), 1);
        assert!(equal[0]
            .replacement()
            .pins()
            .iter()
            .any(|pin| pin.is_open() && pin.comparison().chi().is_some()));
        assert!(!equal[0]
            .replacement()
            .pins()
            .iter()
            .any(|pin| pin.is_found()));

        let equal_three =
            LiveConstituent::close_population_against(&[with.clone(), with.clone(), with], &[])
                .unwrap();
        assert_eq!(equal_three.len(), 1);
        assert_eq!(equal_three[0].members(), &[0, 1, 2]);
        assert!(equal_three[0]
            .replacement()
            .pins()
            .iter()
            .any(|pin| pin.is_open() && pin.comparison().chi().is_some()));
        assert!(!equal_three[0]
            .replacement()
            .pins()
            .iter()
            .any(|pin| pin.is_found()));
    }

    #[test]
    fn one_leader_crosses_successive_capacitive_hyperedges_without_pairwise_edges() {
        let mut standing = vec![
            capacitive_hyperedge(&[7, 13]),
            capacitive_hyperedge(&[13, 17]),
            capacitive_hyperedge(&[17, 19]),
            capacitive_hyperedge(&[23, 29]),
        ];
        standing.sort_by_key(|body| body.native_words().unwrap());

        let closed = LiveConstituent::close_population_against(
            &[one_exposed_arm(exposed_pin(7), 0)],
            &standing,
        )
        .unwrap();
        assert_eq!(closed.len(), 1);
        assert_eq!(closed[0].touched().len(), 3);
        assert_eq!(closed[0].front_depth(), 3);
        assert!(closed[0]
            .replacement()
            .pins()
            .iter()
            .filter_map(LivePin::interface)
            .any(|interface| interface.local() == 19));
        assert!(!closed[0]
            .replacement()
            .pins()
            .iter()
            .filter_map(LivePin::interface)
            .any(|interface| interface.local() == 23 || interface.local() == 29));
    }

    #[test]
    fn noncommuting_path_comparison_carries_its_residual_without_founding() {
        let held = exposed_pin(7);
        let mut arriving = held.clone();
        arriving.meeting.arrow.aim = Cog::ZERO;
        arriving.meeting.arrow.cross = Cog::lit(3);

        let comparison = LivePin::rebase_exposed(&arriving, &held, None).unwrap();
        let residual = comparison.comparison().chi().unwrap();

        assert!(residual.wound());
        assert!(comparison.is_open());
        assert!(!comparison.is_found());
        assert!(comparison.formed().is_none());
        assert_ne!(
            comparison.factor(LocalAxis::new(0)),
            SparseTransport::identity()
        );

        let commuting = LivePin::rebase_exposed(&held, &held, None).unwrap();
        assert!(!commuting.is_open());
        assert!(!commuting.is_found());
        assert_eq!(commuting.formed().unwrap().deed(), FeltDeed::Ride);
    }

    #[test]
    fn native_rest_rejects_every_superseded_or_unknown_schema() {
        let original = one_exposed_arm(exposed_pin(7), 0);
        let current = original.native_words().unwrap();
        assert_eq!(
            LiveConstituent::from_native_words(&current).unwrap(),
            original
        );
        for version in [5u32, 6, 7, 8, 9, 10, 12, u32::MAX] {
            let mut rejected = current.to_vec();
            rejected[1] = version;
            assert_eq!(
                LiveConstituent::from_native_words(&rejected),
                Err(LiveConstituentError::InvalidWire)
            );
        }
    }

    #[test]
    fn a_later_exact_boundary_rides_the_opening_without_rewriting_its_earlier_scope() {
        let arm = one_exposed_arm(exposed_pin(7), 0);
        let opening = LiveConstituent::close_population_against(&[arm.clone(), arm.clone()], &[])
            .unwrap()
            .remove(0)
            .replacement;
        let open_comparisons: Vec<_> = opening
            .pins()
            .iter()
            .filter(|pin| pin.is_open())
            .map(LivePin::comparison)
            .collect();
        assert_eq!(open_comparisons.len(), 1);
        assert!(open_comparisons[0].chi().is_some());
        assert!(!opening.pins().iter().any(|pin| pin.is_found()));

        let reopened =
            LiveConstituent::from_native_words(&opening.native_words().unwrap()).unwrap();
        assert_eq!(reopened, opening);
        let (touched, later) = arm.close_against(std::slice::from_ref(&reopened)).unwrap();

        assert_eq!(touched, vec![0]);
        assert_eq!(later.grain(), opening.grain() + 1);
        assert!(open_comparisons.iter().all(|comparison| later
            .pins()
            .iter()
            .any(|pin| pin.comparison() == *comparison)));
        assert!(!later.pins().iter().any(|pin| pin.is_found()));
        assert_eq!(
            later.boundary_transition(later.boundaries().len() - 1),
            Some(LiveBoundaryTransition::Ride)
        );
        let carried = &later.boundaries().last().unwrap().paths()[0];
        assert!(carried.interior_folded());
        assert!(carried.steps().is_empty());
        assert!(!carried.transport().terms().is_empty());
    }

    #[test]
    fn plural_arrivals_share_one_temporal_factor_without_cloning_standing() {
        let prior = one_exposed_arm(exposed_pin(7), 0);
        let arrivals = [
            one_exposed_arm(exposed_pin(7), 0),
            one_exposed_arm(exposed_pin(7), 0),
        ];
        let closure = LiveConstituent::close_population_against(&arrivals, &[prior]).unwrap();
        assert_eq!(closure.len(), 1);
        assert_eq!(closure[0].members(), &[0, 1]);
        assert_eq!(closure[0].touched(), &[0]);
        assert_eq!(closure[0].replacement().grain(), 3);
    }

    #[test]
    fn incidence_aperture_exposes_only_the_reached_star_and_cannot_change_closure() {
        let arrivals = [
            one_exposed_arm(exposed_pin(7), 0),
            one_exposed_arm(exposed_pin(7), 0),
        ];
        let mut standing = Vec::new();
        for reach in 100..164 {
            standing.push(one_exposed_arm(exposed_pin(reach), 0));
        }
        standing.push(one_exposed_arm(exposed_pin(7), 0));
        for reach in 200..264 {
            standing.push(one_exposed_arm(exposed_pin(reach), 0));
        }
        standing.sort_unstable_by(|left, right| {
            left.native_words()
                .unwrap()
                .cmp(&right.native_words().unwrap())
        });
        let reached = standing
            .iter()
            .position(|body| {
                body.pins()
                    .iter()
                    .any(|pin| pin.interface() == Some(InterfaceCapability::new(1, 7)))
            })
            .unwrap();

        let aperture = StandingIncidenceAperture::from_standing(&standing).unwrap();
        let active = arrivals
            .iter()
            .map(|body| {
                body.support_cover_factor()
                    .and_then(|factor| factor.indexed_exposed_arms())
            })
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        assert_eq!(
            aperture.candidates(&active, &[], &standing).unwrap(),
            [reached]
        );

        let local = LiveConstituent::close_population_against_with_aperture(
            &arrivals, &standing, &aperture,
        )
        .unwrap();
        let exhaustive = LiveConstituent::close_population_against_with_aperture(
            &arrivals,
            &standing,
            &StandingIncidenceAperture::exhaustive(),
        )
        .unwrap();
        assert_eq!(local.len(), exhaustive.len());
        for (local, exhaustive) in local.iter().zip(&exhaustive) {
            assert_eq!(local.members(), exhaustive.members());
            assert_eq!(local.touched(), exhaustive.touched());
            assert_eq!(local.replacement(), exhaustive.replacement());
        }
    }

    #[test]
    fn touched_identity_updates_the_aperture_without_revisiting_retained_standing() {
        let mut before = vec![
            one_exposed_arm(exposed_pin(7), 0),
            one_exposed_arm(exposed_pin(7), 0),
            one_exposed_arm(exposed_pin(13), 0),
            one_exposed_arm(exposed_pin(100), 0),
        ];
        before.sort_unstable_by(|left, right| {
            left.native_words()
                .unwrap()
                .cmp(&right.native_words().unwrap())
        });
        let first_seven = before
            .iter()
            .position(|body| {
                body.pins()
                    .iter()
                    .any(|pin| pin.interface() == Some(InterfaceCapability::new(1, 7)))
            })
            .unwrap();
        let hundred = before
            .iter()
            .position(|body| {
                body.pins()
                    .iter()
                    .any(|pin| pin.interface() == Some(InterfaceCapability::new(1, 100)))
            })
            .unwrap();
        let mut touched = vec![first_seven, hundred];
        touched.sort_unstable();
        let replacement = one_exposed_arm(exposed_pin(29), 1);

        let aperture = StandingIncidenceAperture::from_standing(&before).unwrap();
        let carried = aperture
            .after_replacements(&before, std::iter::once((touched.as_slice(), &replacement)))
            .unwrap();

        let mut successor = before
            .iter()
            .enumerate()
            .filter(|(at, _)| touched.binary_search(at).is_err())
            .map(|(_, body)| body.clone())
            .collect::<Vec<_>>();
        successor.push(replacement);
        successor.sort_unstable_by(|left, right| {
            left.native_words()
                .unwrap()
                .cmp(&right.native_words().unwrap())
        });
        assert_eq!(
            carried,
            StandingIncidenceAperture::from_standing(&successor).unwrap()
        );
    }
}
