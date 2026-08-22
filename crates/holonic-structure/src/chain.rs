//! A chain of interactions, composed through its links, with both ends open and the unconnected
//! retained.
//!
//! # Why both ends are open
//!
//! Brandon's statement of the object, 2026-08-14: *"if you are referring to only **one** Holonic
//! Interaction, you are referring to a selected scope apart of an infinitely larger causal complex,
//! where even in the 'one' Holonic Interaction it is implicit that you can further derive where the
//! chain came from and where it will go based on potentials."*
//!
//! A chain whose ends are `Option::None` cannot say the difference between *the potential is there
//! and I stopped* and *there is nothing further*. That distinction is the whole of `saturated`
//! versus `untouched` — the two ways an arrival can do nothing, which
//! `IncidenceComplex::admit_later` already distinguishes at the mouth and which seven stages on the
//! agentic path currently collapse into one `Ok(())`.
//!
//! So [`ChainEnd`] has no third case, and [`Chain::disposition`] reads the fate off the type
//! instead of off a hand-written check.
//!
//! # Why the unconnected are retained
//!
//! `H.0466`, `proved-derived`: *"A lightning world must admit plural upward leaders and retain
//! connected and unconnected outcomes instead of manufacturing one ground endpoint."* A rank is only
//! meaningful against the population that did **not** connect, so a carrier that drops the attempts
//! has deleted the null its own reading is taken against.
//!
//! This is also the conservation clause. At a lossless junction the incident current is exactly
//! transmitted plus reflected; nothing is destroyed, so what does not continue the chain must be
//! kept. `omitted = complete − selected = 0` — the structural defect measured on the leader star —
//! is not expressible here: a junction whose admittances do not match reflects, and the reflection
//! has somewhere to go.
//!
//! # Composition
//!
//! [`Composes`] carries the cocycle law. A chain's composed transport is the product along its
//! links; where a directly declared transport disagrees with the composed one, the deviation is
//! **holonomy** and is returned rather than tested.
//!
//! # A remainder arrives by two routes, and until 2026-08-15 only one was read
//!
//! [`Chain::reflect`] retains an attempt a *caller* made and abandoned. [`Composes::remainder`]
//! retains what the *links themselves* sent back while the chain was being crossed. They are the
//! same species — current that did not continue — and they are independent: a chain whose every
//! link reflected can have an empty `unconnected`, and a chain whose composition is clean can still
//! carry an abandoned attempt.
//!
//! [`Chain::is_rebase`] consulted only the first, so it reported a clean pass for a traversal that
//! reflected at every link. It now requires both, and [`Chain::remainder`] returns the transport's
//! own half so the reading is exhibitable rather than a verdict.

use alloc::vec::Vec;

use serde::{Deserialize, Serialize};

use crate::relating::{Composes, Relating};

/// A chain boundary. There is no third case, and neither case is an absence.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ChainEnd<E> {
    /// The potential is there and this chain stopped. What remains is carried, not discarded.
    Continues(E),
    /// There is nothing further, and this is the cause.
    Terminates(E),
}

impl<E> ChainEnd<E> {
    pub const fn is_open(&self) -> bool {
        matches!(self, Self::Continues(_))
    }

    pub const fn testimony(&self) -> &E {
        match self {
            Self::Continues(testimony) | Self::Terminates(testimony) => testimony,
        }
    }
}

/// One attempt that did not continue the chain, retained with what reflected at it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Unconnected<N, E> {
    /// Which hop of the chain the attempt was made from.
    pub at: usize,
    /// The node the attempt reached toward.
    pub attempt: N,
    /// What reflected there rather than crossing.
    pub reflected: E,
}

/// What a traversal did, read off the chain's own shape rather than asserted by its caller.
///
/// This is the mouth's vocabulary. `ArrivalResponse` distinguishes *saturated* — "the arrival got
/// there and nothing was caused" — from *untouched*, "never reached at all", and the two are
/// different facts about the world that a bare success return cannot tell apart.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Disposition {
    /// Nothing conducted and the potential remains. The current never landed.
    Untouched,
    /// Nothing conducted and the chain terminated. It landed and the material caused nothing.
    Saturated,
    /// At least one junction was crossed.
    Reached,
}

/// A chain of interactions. **A partial chain is a value**: a traversal still in flight is this
/// same type with an open tail, so an unfinished run always has something to show.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Chain<N, L, E> {
    nodes: Vec<N>,
    links: Vec<L>,
    head: ChainEnd<E>,
    tail: ChainEnd<E>,
    unconnected: Vec<Unconnected<N, E>>,
}

impl<N, L, E> Chain<N, L, E> {
    /// Found a chain at a source. The tail opens with the potential standing there; nothing has
    /// been crossed yet, so it cannot yet be `Terminates`.
    pub fn founded(source: N, head: ChainEnd<E>, standing: E) -> Self {
        let mut nodes = Vec::new();
        nodes.push(source);
        Self {
            nodes,
            links: Vec::new(),
            head,
            tail: ChainEnd::Continues(standing),
            unconnected: Vec::new(),
        }
    }

    /// Cross a junction: the link carried it and the node is where it arrived. The tail's standing
    /// potential is replaced by what stands at the new tip.
    pub fn carry(&mut self, link: L, node: N, standing: E) {
        self.links.push(link);
        self.nodes.push(node);
        self.tail = ChainEnd::Continues(standing);
    }

    /// Retain an attempt that did not cross. Reflection is not failure and it is not noise; it is
    /// the population the chain's reading is taken against.
    pub fn reflect(&mut self, attempt: N, reflected: E) {
        self.unconnected.push(Unconnected {
            at: self.links.len(),
            attempt,
            reflected,
        });
    }

    /// Close the tail with the cause. Until this is called the chain is partial by type.
    pub fn terminate(&mut self, cause: E) {
        self.tail = ChainEnd::Terminates(cause);
    }

    /// Hops crossed. Deliberately not called `len`: a chain's extent is its junctions, not its
    /// nodes, and the two differ by the source.
    pub fn hops(&self) -> usize {
        self.links.len()
    }

    pub fn nodes(&self) -> &[N] {
        &self.nodes
    }

    pub fn links(&self) -> &[L] {
        &self.links
    }

    pub fn unconnected(&self) -> &[Unconnected<N, E>] {
        &self.unconnected
    }

    pub fn head(&self) -> &ChainEnd<E> {
        &self.head
    }

    pub fn tail(&self) -> &ChainEnd<E> {
        &self.tail
    }

    pub fn source(&self) -> Option<&N> {
        self.nodes.first()
    }

    pub fn tip(&self) -> Option<&N> {
        self.nodes.last()
    }

    /// What this traversal did, from the chain's shape alone.
    pub fn disposition(&self) -> Disposition {
        if !self.links.is_empty() {
            return Disposition::Reached;
        }
        if self.tail.is_open() {
            Disposition::Untouched
        } else {
            Disposition::Saturated
        }
    }
}

impl<N, L, E> Chain<N, L, E>
where
    L: Relating,
    L::Transport: Composes + Clone,
{
    /// The transport composed along every link. An empty chain composes to the identity, which is
    /// the correct reading: nothing crossed, so nothing was rebased.
    pub fn compose(&self) -> L::Transport {
        let mut carried = <L::Transport as Composes>::identity();
        for link in &self.links {
            carried = carried.compose(link.transport());
        }
        carried
    }

    /// The cocycle defect against a directly declared transport: what separates going through from
    /// going straight. Zero is the exact cocycle; anything else is the chain's holonomy.
    pub fn defect_against(&self, direct: &L::Transport) -> <L::Transport as Composes>::Defect {
        <L::Transport as Composes>::defect(direct, &self.compose())
    }

    /// The holonomy of a **closed** chain — its composition read against the identity.
    ///
    /// `None` when the chain does not return to its own source, and that is not a missing
    /// measurement: holonomy is a property of a loop, and an open chain has none. A carrier that
    /// answered `0` here would be reporting closure for a chain that never closed.
    pub fn holonomy(&self) -> Option<<L::Transport as Composes>::Defect>
    where
        N: PartialEq,
    {
        if self.links.is_empty() || self.nodes.first() != self.nodes.last() {
            return None;
        }
        Some(self.defect_against(&<L::Transport as Composes>::identity()))
    }

    /// What this traversal turned back: the **composed** transport's own remainder, together with
    /// the attempts that never crossed.
    ///
    /// Both are the same species — current that did not continue — and they arrive by different
    /// routes. [`Chain::reflect`] retains an attempt a caller made and abandoned;
    /// [`Composes::remainder`] retains what the links themselves sent back while the chain was
    /// being crossed. A reading that consults only the first is a reading of the caller's
    /// bookkeeping.
    pub fn remainder(&self) -> <L::Transport as Composes>::Remainder {
        self.compose().remainder()
    }

    /// Whether this traversal lost nothing — the **rebase** species, remainder zero.
    ///
    /// Two arms, and until 2026-08-15 there was only the first:
    ///
    /// ```text
    ///   no attempt was retained by `reflect`        the caller's bookkeeping
    ///   the composed transport turned nothing back  the links' own testimony
    /// ```
    ///
    /// **The second arm is why this moved into the composing impl.** The old form read
    /// `unconnected.is_empty()` alone, so a chain whose every link reflected returned `true` — it
    /// was reporting that no caller had *told* it about a reflection, and calling that a
    /// zero-remainder rebase. With the returned component inside the transport, a chain cannot
    /// compose to a pure rebase while its links reflect.
    ///
    /// A chain with a retained reflection is a **condensation**: the remainder is certified because
    /// each attempt carries what reflected at it and the composition carries the rest. Dropping
    /// either would make it a **quotient**.
    ///
    /// **Corrected during construction, by a failing test.** An earlier form required the chain's
    /// composition to close against the identity — conflating *this loop returns where it started*
    /// with *this traversal lost nothing*. They are different facts: an adiabatic taper composes to
    /// a large transport and is still a chain of zero-remainder rebases. Loop closure is
    /// [`Chain::holonomy`]; path-independence is [`Chain::defect_against`]; loss is here.
    pub fn is_rebase(&self) -> bool {
        self.unconnected.is_empty() && <L::Transport as Composes>::is_empty(&self.remainder())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::relating::Hand;

    /// The additive chart of a chart transition, used as the test carrier: `carried` composes by
    /// addition, and the defect between two transports is their difference. `exp` would carry it to
    /// the multiplicative chart; the law under test is the same in either, which is the point.
    ///
    /// **It is two-component, since 2026-08-15, and that is the whole test.** A one-component
    /// carrier cannot exercise [`Composes::remainder`] in both arms — every chain built on it
    /// returns an empty remainder, so `is_rebase` would be a check that cannot fail here exactly as
    /// it was in the engine. `returned` is the half that came back, and it composes alongside the
    /// half that continued.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct Additive {
        carried: i64,
        returned: i64,
    }

    impl Additive {
        const fn carrying(carried: i64) -> Self {
            Self {
                carried,
                returned: 0,
            }
        }

        const fn returning(carried: i64, returned: i64) -> Self {
            Self { carried, returned }
        }
    }

    impl Composes for Additive {
        type Defect = Self;
        type Remainder = i64;

        fn identity() -> Self {
            Self::carrying(0)
        }

        fn compose(&self, next: &Self) -> Self {
            Self {
                carried: self.carried + next.carried,
                returned: self.returned + next.returned,
            }
        }

        fn defect(direct: &Self, composed: &Self) -> Self {
            Self {
                carried: direct.carried - composed.carried,
                returned: direct.returned - composed.returned,
            }
        }

        fn closed(defect: &Self) -> bool {
            defect.carried == 0 && defect.returned == 0
        }

        fn remainder(&self) -> i64 {
            self.returned
        }

        fn is_empty(remainder: &i64) -> bool {
            *remainder == 0
        }
    }

    struct Step {
        weight: u64,
        hand: Hand,
        transport: Additive,
    }

    impl Relating for Step {
        type Weight = u64;
        type Transport = Additive;

        fn reach(&self) -> &u64 {
            &self.weight
        }

        fn hand(&self) -> Hand {
            self.hand
        }

        fn transport(&self) -> &Additive {
            &self.transport
        }
    }

    fn step(weight: u64, transport: i64) -> Step {
        Step {
            weight,
            hand: Hand::Cohere,
            transport: Additive::carrying(transport),
        }
    }

    fn reflecting_step(weight: u64, carried: i64, returned: i64) -> Step {
        Step {
            weight,
            hand: Hand::Anti,
            transport: Additive::returning(carried, returned),
        }
    }

    #[test]
    fn a_founded_chain_that_never_crossed_is_untouched_not_saturated() {
        let chain: Chain<&str, Step, &str> =
            Chain::founded("source", ChainEnd::Continues("prior"), "standing");
        assert_eq!(chain.disposition(), Disposition::Untouched);
        assert!(chain.tail().is_open());
    }

    #[test]
    fn a_terminated_chain_that_never_crossed_is_saturated() {
        let mut chain: Chain<&str, Step, &str> =
            Chain::founded("source", ChainEnd::Continues("prior"), "standing");
        chain.terminate("the material caused nothing");
        assert_eq!(chain.disposition(), Disposition::Saturated);
        assert!(!chain.tail().is_open());
        // The two dispositions are different facts and the type keeps them apart. A bare `Ok(())`
        // cannot, which is the defect this carrier exists to make unspellable.
        assert_ne!(Disposition::Saturated, Disposition::Untouched);
    }

    #[test]
    fn the_transport_composes_along_the_chain() {
        let mut chain: Chain<u32, Step, &str> =
            Chain::founded(0, ChainEnd::Terminates("origin"), "s");
        chain.carry(step(1, 3), 1, "s");
        chain.carry(step(1, 4), 2, "s");
        chain.carry(step(1, 5), 3, "s");
        assert_eq!(chain.compose(), Additive::carrying(12));
        assert_eq!(chain.disposition(), Disposition::Reached);
        assert_eq!(chain.hops(), 3);
    }

    #[test]
    fn the_cocycle_law_holds_and_its_failure_is_returned_rather_than_tested() {
        // r(i,j) . r(j,k) = r(i,k): composing through the intermediate agrees with the direct
        // transport, so the defect is zero and the chain is a rebase.
        let mut through: Chain<u32, Step, &str> =
            Chain::founded(0, ChainEnd::Terminates("origin"), "s");
        through.carry(step(1, 3), 1, "s");
        through.carry(step(1, 4), 2, "s");
        assert_eq!(
            through.defect_against(&Additive::carrying(7)),
            Additive::identity()
        );
        assert!(through.is_rebase());

        // A direct transport that disagrees returns the deviation itself, not a verdict.
        assert_eq!(
            through.defect_against(&Additive::carrying(10)),
            Additive::carrying(3)
        );
    }

    /// ★ THE ARM THAT WAS MISSING. A chain whose links themselves turned something back is not a
    /// rebase, and no caller told it so.
    #[test]
    fn a_chain_whose_links_returned_something_is_not_a_rebase_though_nothing_was_reflected_by_hand()
    {
        // Both chains have an EMPTY `unconnected` population, which is the only thing the old
        // `is_rebase` consulted. They must not read the same.
        let mut clean: Chain<u32, Step, &str> =
            Chain::founded(0, ChainEnd::Terminates("origin"), "s");
        clean.carry(step(1, 3), 1, "s");
        clean.carry(step(1, 4), 2, "s");
        assert!(clean.unconnected().is_empty());
        assert_eq!(clean.remainder(), 0);
        assert!(clean.is_rebase());

        let mut returning: Chain<u32, Step, &str> =
            Chain::founded(0, ChainEnd::Terminates("origin"), "s");
        returning.carry(reflecting_step(1, 3, 2), 1, "s");
        returning.carry(reflecting_step(1, 4, -5), 2, "s");
        assert!(returning.unconnected().is_empty());
        // The returned components composed to -3, so the traversal lost something and says what.
        assert_eq!(returning.remainder(), -3);
        assert!(!returning.is_rebase());

        // And the two arms are separable: a chain whose returned components CANCEL is a rebase
        // again, which is the physical statement that the returns interfered to nothing rather than
        // the bookkeeping statement that nobody recorded one.
        let mut cancelling: Chain<u32, Step, &str> =
            Chain::founded(0, ChainEnd::Terminates("origin"), "s");
        cancelling.carry(reflecting_step(1, 3, 2), 1, "s");
        cancelling.carry(reflecting_step(1, 4, -2), 2, "s");
        assert_eq!(cancelling.remainder(), 0);
        assert!(cancelling.is_rebase());
    }

    #[test]
    fn a_reflected_attempt_is_retained_and_refuses_the_rebase_claim() {
        let mut chain: Chain<&str, Step, &str> =
            Chain::founded("source", ChainEnd::Terminates("origin"), "s");
        chain.carry(step(1, 0), "crossed", "s");
        chain.reflect("did not cross", "admittance mismatch");
        // Something reflected, so the remainder is not zero and this is a condensation rather than
        // a rebase. The population that did not connect is ON the chain, not dropped — which is
        // what makes `omitted = complete - selected = 0` unspellable here.
        assert!(!chain.is_rebase());
        assert_eq!(chain.unconnected().len(), 1);
        assert_eq!(chain.unconnected()[0].at, 1);
        assert_eq!(chain.unconnected()[0].reflected, "admittance mismatch");
    }

    #[test]
    fn holonomy_is_none_on_an_open_chain_and_a_defect_on_a_closed_one() {
        // Open: the chain transports something and never returns to its source. It has no holonomy,
        // and `None` says so rather than reporting a closure that did not happen.
        let mut open: Chain<u32, Step, &str> =
            Chain::founded(0, ChainEnd::Terminates("origin"), "s");
        open.carry(step(1, 3), 1, "s");
        open.carry(step(1, 4), 2, "s");
        assert_eq!(open.holonomy(), None);
        // ...and it is still a rebase. Losing nothing and returning to where you started are two
        // different facts; the first form of this carrier conflated them and a test caught it.
        assert!(open.is_rebase());

        // Closed and flat: around the loop and back to the identity.
        let mut flat: Chain<u32, Step, &str> =
            Chain::founded(0, ChainEnd::Terminates("origin"), "s");
        flat.carry(step(1, 5), 1, "s");
        flat.carry(step(1, -5), 0, "s");
        assert_eq!(flat.holonomy(), Some(Additive::identity()));

        // Closed and curved: the loop returns, and what it returns with is the holonomy.
        let mut curved: Chain<u32, Step, &str> =
            Chain::founded(0, ChainEnd::Terminates("origin"), "s");
        curved.carry(step(1, 5), 1, "s");
        curved.carry(step(1, -2), 0, "s");
        assert_eq!(curved.holonomy(), Some(Additive::carrying(-3)));
    }

    #[test]
    fn the_reach_weighs_and_the_hand_gates_separately() {
        let heavy = step(1_000_000, 0);
        let light = step(1, 0);
        // Both weigh; neither decides. The hand is what gates, and it is not derived from the
        // weight — a carrier that let the heavier one decide would have promoted a magnitude into
        // an admission.
        assert_eq!(*heavy.reach(), 1_000_000);
        assert_eq!(*light.reach(), 1);
        assert_eq!(heavy.hand(), light.hand());
    }

    #[test]
    fn the_founding_hand_is_its_own_reverse() {
        assert_eq!(Hand::Cohere.reversed(), Hand::Anti);
        assert_eq!(Hand::Anti.reversed(), Hand::Cohere);
        assert_eq!(Hand::Ortho.reversed(), Hand::Ortho);
        assert!(Hand::Ortho.is_quarter_turn());
        assert!(!Hand::Cohere.is_quarter_turn());
    }
}
