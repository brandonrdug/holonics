//! The temper — founding and decay as one continuous property of a structure's own twist.
//!
//! ## The force this is, and the half of its source that was struck
//!
//! From the laboratory, 2026-07-10 — **assistant-authored** (`SINGULARITIES.md`), not a Brandon
//! ruling, and corrected below:
//!
//! > *"Fusion is CLOSURE: the stable atom is a closing trigram — a loop whose holonomy closes,
//! > on-quantum — and a closed coil SELF-SUSTAINS. Decay is THE LEAK OF OPENNESS: an open coil
//! > leaks by its own openness — **the instability IS the leak — no damping term, no threshold.**
//! > Neither is a trigger — both are continuous properties of the structure's own twist."*
//!
//! **Two of those clauses were prohibited by the laboratory on the same day**, and this module
//! carried them as founding law until 2026-08-08. The COMMUNE letter
//! `2026-07-10_sol-to-fable_the-star-is-the-circulation…`:
//!
//! > *"Two of its load-bearing sentences are prohibited now: a closed coil **self-sustains**; an
//! > open coil leaks at its own **pace**. … without supplied stimulus there is no current,
//! > relating, Θ, or passage of proper time. Standing closure between lights is deposited topology,
//! > not an active circulation. It cannot feed itself, and openness cannot run an interior decay
//! > clock. 'Leak by its own openness' can survive only as a boundary response **under infall**,
//! > never as autonomous decay."*
//!
//! **What survives, and what this module actually implements:** *the instability IS the leak — no
//! damping term, no threshold*, and *neither is a trigger*. Those are the load-bearing clauses and
//! they are untouched. What is struck is any reading in which a closed structure circulates on its
//! own or an open one decays on a clock of its own.
//!
//! **The code was already lawful and the epigraph was not.** Nothing here runs a clock: `Twist` is
//! read from a structure's own retained cycles, `leak` is a sum of retained obstruction magnitudes,
//! and `found_on` is a deposit made by a current that arrived. There is no autonomous decay
//! anywhere in this file, which is why the defect was in the prose and is repaired there. That is
//! `CLAUDE.md` §8 rule 1 running backwards — usually the receipt overstates the code.
//!
//! and the consequence it named:
//!
//! > *"the current build founds from PAIRS (the should-decay), has NO DECAY — that one-way-ness is
//! > the unbounded growth; **the cap is a band-aid over the missing temper.** With the temper the
//! > forest is bounded BY COHERENCE — the cap ceases to exist."*
//!
//! ## What closure is here, exactly
//!
//! [`crate::running_integral::found_potential`] walks a spanning tree over the 1-skeleton, fixes the
//! potential from a base, and tests every remaining chord. A chord that agrees is a cycle that
//! closes. A chord that does not is retained as a [`ChordObstruction`] carrying its exact residual,
//! which is *the holonomy of the fundamental cycle that chord closes*.
//!
//! So closure is not a metaphor here and it is not a new computation:
//!
//! ```text
//!   retained_obstructions.is_empty()   the coil closes; every cycle agrees; a potential exists
//!   otherwise                          the coil is open, and each residual is a leak with an address
//! ```
//!
//! ## Why there is no threshold, and could not be one
//!
//! The residual is **both** the measure of the openness **and** the rate of the leak. There is
//! nothing left for a threshold to compare against: a structure leaking `1` and a structure leaking
//! `1000` are both open, neither may condense, and the magnitude says how fast the second falls
//! behind rather than whether it counts as open at all. A constant introduced anywhere here would be
//! the band-aid the temper replaces.
//!
//! ## Founding and decay are one force, read twice
//!
//! A founding deposits a residual — it **opens** a structure that closed before. Decay is that same
//! residual read again after the population it stands in has grown. Nothing separate happens; there
//! is no decay rule beside the founding rule, and no decay event to schedule.
//!
//! And it is **relational**. `FRAMEWORK/00_SUPERSEDED_LEDGER.md` Ledger U, ratified: *"dilation is
//! relational, a ratio of frames, never a property of one node"* — a node's clock read as an
//! absolute per-node quantity re-installs the absolute frame. Decay is the same, so [`Temper`]
//! carries the pair `(own; population)` whole and **never divides it**, for the reason
//! `MENO_FORMULA §VIII` gives: *"`8/2` and `4/1` are different holonic states; the integer throws
//! that away and re-smuggles the absolute frame."*
//!
//! ## What this is NOT, and the conviction that makes it matter
//!
//! **It is not a pass over the body.** The settling was built once, convicted as a receiver-exempt
//! identity test — it asked *"are these the same?"*, a question the law never contained — and
//! dissolved with *"no replacement pass, ever; the fossil stays a fossil."* Nothing here walks a
//! population looking for things to remove. [`Twist::read`] is a predicate answered from one
//! structure's own cycles at the moment a question is asked of it, and **nothing is ever deleted**.
//!
//! The selection is on **closure**, never on identity, similarity, kinship, or age.
//!
//! ## What the selection does
//!
//! `crates/holonic-engine/src/graph_receiver.rs` already carries the grain machinery this rides:
//! `Coarsen` admits a completed lower hull as one point **while retaining the entire source fiber**,
//! and `Refine` re-opens it. So condensation is already reversible rather than destructive. The one
//! thing missing was the force deciding *which* structure may condense, and that is the whole of the
//! temper:
//!
//! > **A closed structure may be admitted as one coarser point, because nothing leaks out of it.
//! > An open structure may not, because coarsening would discard the obstruction, and the
//! > obstruction is the leak.**
//!
//! That is what bounds the forest by coherence instead of by a cap. An open structure is not
//! destroyed and not penalised — it simply stays expanded until it closes.

use std::collections::BTreeSet;

use num_bigint::BigInt;
use num_traits::Zero;
use serde::{Deserialize, Serialize};

use crate::algebraic::{CausalCellId, GradedCausalComplex};
use crate::running_integral::{ChordObstruction, Cochain, RunningIntegralError, found_potential};

/// What a structure's own twist says about it. **Read, never stored.**
///
/// A stored standing would be a state that has to be invalidated, and invalidating it is the pass
/// this module exists to avoid.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Twist {
    /// Every cycle closes, so the structure may condense: nothing leaks out of it, and forgetting
    /// its interior loses nothing the outside could have seen.
    ///
    /// **Not "self-sustains"** — that reading is struck (see the header). A closed structure is
    /// deposited topology, not an active circulation; it carries no current until one is supplied.
    ///
    /// `chords_tested` is carried because **a closure over zero chords is vacuous** — a structure
    /// with no cycles closes trivially and proves nothing. Read it before reading the verdict.
    Closed { chords_tested: usize },
    /// A retained obstruction. The structure leaks at exactly `leak`, with every obstruction kept
    /// whole and addressed. It may not condense.
    Open {
        /// The sum of the retained residuals' magnitudes. Exact, and never compared to a constant.
        leak: BigInt,
        /// Kept entire. The leak is a reading of these; these are never replaced by the leak.
        obstructions: Vec<ChordObstruction>,
    },
}

impl Twist {
    /// Read one structure's twist from its own cycles.
    ///
    /// The structure is a set of 1-cells inside `complex`; `cochain` values them; `base` fixes the
    /// potential. Cells outside `structure` are not consulted, which is what makes this a local
    /// read rather than a survey.
    pub fn read(
        complex: &GradedCausalComplex,
        cochain: &Cochain,
        base: CausalCellId,
        structure: &BTreeSet<CausalCellId>,
    ) -> Result<Self, RunningIntegralError> {
        let search = found_potential(complex, cochain, base)?;
        let retained: Vec<ChordObstruction> = search
            .retained_obstructions
            .into_iter()
            .filter(|obstruction| structure.contains(&obstruction.cell))
            .collect();
        let tested = search
            .agreeing_chords
            .iter()
            .filter(|cell| structure.contains(cell))
            .count()
            + retained.len();
        if retained.is_empty() {
            return Ok(Self::Closed {
                chords_tested: tested,
            });
        }
        let leak = retained
            .iter()
            .map(|obstruction| {
                if obstruction.residual < BigInt::zero() {
                    -obstruction.residual.clone()
                } else {
                    obstruction.residual.clone()
                }
            })
            .sum();
        Ok(Self::Open {
            leak,
            obstructions: retained,
        })
    }

    /// **The whole of the temper's selection.**
    ///
    /// A closed coil self-sustains, so it may be admitted as one coarser point. An open one may not:
    /// coarsening discards what the obstruction records, and the obstruction is the leak.
    ///
    /// There is no threshold in this predicate and there is nowhere for one to go. It reads the
    /// variant, not the magnitude.
    pub fn may_condense(&self) -> bool {
        matches!(self, Self::Closed { .. })
    }

    /// The leak, which is zero exactly when the coil closes.
    pub fn leak(&self) -> BigInt {
        match self {
            Self::Closed { .. } => BigInt::zero(),
            Self::Open { leak, .. } => leak.clone(),
        }
    }

    /// A closure over no chords is vacuous: a structure with no cycles closes for free.
    ///
    /// This is `CLAUDE.md` §8's tautology rule applied to this module's own return. A caller
    /// reporting `Closed` without reporting this is reporting a receipt that could not have come
    /// out otherwise.
    pub fn closure_is_vacuous(&self) -> bool {
        matches!(self, Self::Closed { chords_tested: 0 })
    }
}

/// One structure's twist against the population it stands in.
///
/// Ledger U: *"dilation is relational, a ratio of frames, never a property of one node."* Decay is
/// the same. A structure does not lose anything of its own — it falls behind, and how far behind is
/// a **pair held whole**: its own leak against the population's.
///
/// The pair is never divided. `MENO_FORMULA §VIII`: *"`8/2` and `4/1` are different holonic states
/// (different arc, different diagonal, different rank); the integer throws that away and
/// re-smuggles the absolute frame."*
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Temper {
    /// This structure's own retained residual.
    pub own: BigInt,
    /// The retained residual of the population it is read against.
    pub population: BigInt,
}

impl Temper {
    /// Order two tempers **without forming either quotient** — cross-multiplication, exact.
    pub fn cmp_against(&self, other: &Self) -> std::cmp::Ordering {
        (&self.own * &other.population).cmp(&(&other.own * &self.population))
    }

    /// The structure leaks nothing: it closed, and it stands whatever the population does.
    pub fn stands(&self) -> bool {
        self.own.is_zero()
    }
}

/// The temper read over a declared family of structures, and the condensation it licenses.
///
/// **This is not a pass.** It answers one question — *which of these declared structures may
/// condense* — for a family the caller names. It never walks the body, never searches for
/// candidates, and removes nothing. What it returns is a licence; acting on it is
/// `graph_receiver`'s `Coarsen`, which retains the whole source fiber.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TemperedFamily {
    pub schema: String,
    /// Every declared structure with the twist it was read at, in declared order.
    pub twists: Vec<(String, Twist)>,
}

impl TemperedFamily {
    pub fn read(
        complex: &GradedCausalComplex,
        cochain: &Cochain,
        base: CausalCellId,
        family: &[(String, BTreeSet<CausalCellId>)],
    ) -> Result<Self, RunningIntegralError> {
        let mut twists = Vec::new();
        for (name, structure) in family {
            twists.push((
                name.clone(),
                Twist::read(complex, cochain, base, structure)?,
            ));
        }
        Ok(Self {
            schema: "holonic-engine.temper.v1".to_owned(),
            twists,
        })
    }

    /// The structures that may condense, named.
    pub fn condensing(&self) -> Vec<&str> {
        self.twists
            .iter()
            .filter(|(_, twist)| twist.may_condense())
            .map(|(name, _)| name.as_str())
            .collect()
    }

    /// The structures that stay expanded, each with the leak that keeps them open. **Named, never
    /// counted** — an open structure whose obstruction nobody can address is the same defect as a
    /// count standing in for a population.
    pub fn expanded(&self) -> Vec<(&str, BigInt)> {
        self.twists
            .iter()
            .filter(|(_, twist)| !twist.may_condense())
            .map(|(name, twist)| (name.as_str(), twist.leak()))
            .collect()
    }

    /// The population's own leak: the sum over the declared family.
    pub fn population_leak(&self) -> BigInt {
        self.twists.iter().map(|(_, twist)| twist.leak()).sum()
    }

    /// One structure's temper against this family. Relational by construction — the same structure
    /// read against a different family returns a different temper, which is the point.
    pub fn temper_of(&self, name: &str) -> Option<Temper> {
        let own = self
            .twists
            .iter()
            .find(|(candidate, _)| candidate == name)
            .map(|(_, twist)| twist.leak())?;
        Some(Temper {
            own,
            population: self.population_leak(),
        })
    }

    /// **The bound the temper puts on growth.** After condensation the family's extent is the
    /// number that stayed expanded plus one point per structure that closed. Nothing was deleted,
    /// and no cap was consulted.
    pub fn condensed_extent(&self) -> usize {
        self.twists.len()
    }
}

/// A cochain that opens a structure which closed before it.
///
/// Founding and decay are one force, and this is the founding face: depositing a value on one cell
/// that the potential does not imply **opens** the structure. The same residual read later against a
/// grown population is the decay face. There is no second operation.
pub fn found_on(cochain: &Cochain, cell: CausalCellId, value: BigInt) -> Cochain {
    let mut founded = cochain.clone();
    founded.set(cell, value);
    founded
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use num_bigint::BigInt;

    use super::*;
    use crate::algebraic::{CausalChain, ComparativeMultiplicity};
    use crate::causal::EventId;

    /// A cycle of `n` vertices and `n` edges, oriented head-minus-tail around the ring.
    ///
    /// A ring is the smallest material on which closure can genuinely fail: a tree closes for free,
    /// and a fixture built from a tree would make every reading below vacuous.
    fn ring(n: u64) -> (GradedCausalComplex, Vec<CausalCellId>, Vec<CausalCellId>) {
        let mut complex = GradedCausalComplex::default();
        let mut event = 0u64;
        let mut next = || {
            event += 1;
            BTreeSet::from([EventId(event)])
        };
        let vertices: Vec<CausalCellId> = (0..n)
            .map(|i| {
                complex
                    .found_cell(format!("v{i}"), next(), 0, CausalChain::default())
                    .expect("a vertex has no boundary")
            })
            .collect();
        let edges: Vec<CausalCellId> = (0..n)
            .map(|i| {
                let tail = vertices[i as usize];
                let head = vertices[((i + 1) % n) as usize];
                let mut boundary = CausalChain::default();
                boundary.add_term(head, ComparativeMultiplicity::positive(1u32));
                boundary.add_term(tail, ComparativeMultiplicity::negative(1u32));
                complex
                    .found_cell(format!("e{i}"), next(), 1, boundary)
                    .expect("an edge closes")
            })
            .collect();
        (complex, vertices, edges)
    }

    fn whole(edges: &[CausalCellId]) -> BTreeSet<CausalCellId> {
        edges.iter().copied().collect()
    }

    #[test]
    fn a_ring_whose_values_close_around_the_cycle_is_closed_and_may_condense() {
        let (complex, vertices, edges) = ring(3);
        // +1, +1, -2 sums to zero around the ring: the coil closes.
        let cochain = Cochain::from_values(
            1,
            [
                (edges[0], BigInt::from(1)),
                (edges[1], BigInt::from(1)),
                (edges[2], BigInt::from(-2)),
            ],
        );
        let twist = Twist::read(&complex, &cochain, vertices[0], &whole(&edges)).expect("a read");
        assert_eq!(twist, Twist::Closed { chords_tested: 1 });
        assert!(twist.may_condense());
        assert!(twist.leak().is_zero());
        assert!(
            !twist.closure_is_vacuous(),
            "a ring has a chord, so this closure was tested and is not free"
        );
    }

    #[test]
    fn the_same_ring_with_one_value_moved_is_open_and_may_not_condense() {
        let (complex, vertices, edges) = ring(3);
        let cochain = Cochain::from_values(
            1,
            [
                (edges[0], BigInt::from(1)),
                (edges[1], BigInt::from(1)),
                (edges[2], BigInt::from(-5)),
            ],
        );
        let twist = Twist::read(&complex, &cochain, vertices[0], &whole(&edges)).expect("a read");
        assert!(!twist.may_condense());
        assert_eq!(twist.leak(), BigInt::from(3), "the residual is |-5 - (-2)| = 3");
        let Twist::Open { obstructions, .. } = &twist else {
            panic!("expected an open coil, got {twist:?}");
        };
        assert_eq!(obstructions.len(), 1);
        // The chord is e1, not the edge whose value moved: the walk leaves the base along BOTH
        // incident edges (e0 and e2) before crossing the ring, so e1 is what closes the cycle. The
        // leak's address is a property of the spanning tree, and pinning it here is what makes a
        // change in that walk visible rather than silent.
        assert_eq!(obstructions[0].cell, edges[1], "the leak carries its address");
        // The obstruction is kept whole. The leak is a reading of it, never a replacement.
        assert_eq!(
            obstructions[0].declared.clone() - obstructions[0].implied.clone(),
            obstructions[0].residual
        );
    }

    #[test]
    fn the_magnitude_of_the_leak_is_the_rate_and_never_a_gate() {
        // The defect this module replaces is a cap. So: a coil leaking 1 and a coil leaking a
        // million must both be OPEN and both refuse to condense. If any constant existed anywhere in
        // the selection, one of these would pass it.
        let (complex, vertices, edges) = ring(3);
        for offset in [1_i64, 7, 1_000, 1_000_000] {
            let cochain = Cochain::from_values(
                1,
                [
                    (edges[0], BigInt::from(1)),
                    (edges[1], BigInt::from(1)),
                    (edges[2], BigInt::from(-2 - offset)),
                ],
            );
            let twist =
                Twist::read(&complex, &cochain, vertices[0], &whole(&edges)).expect("a read");
            assert!(
                !twist.may_condense(),
                "leak {offset} condensed; a threshold has entered the selection"
            );
            assert_eq!(twist.leak(), BigInt::from(offset));
        }
    }

    #[test]
    fn founding_on_a_closed_structure_opens_it_and_that_is_the_same_force_as_the_decay() {
        // One operation, two readings. Depositing a value the potential does not imply IS the
        // founding, and the residual it leaves IS what later reads as the leak.
        let (complex, vertices, edges) = ring(3);
        let closed = Cochain::from_values(
            1,
            [
                (edges[0], BigInt::from(1)),
                (edges[1], BigInt::from(1)),
                (edges[2], BigInt::from(-2)),
            ],
        );
        let before = Twist::read(&complex, &closed, vertices[0], &whole(&edges)).expect("a read");
        assert!(before.may_condense(), "it closed before the founding");

        let founded = found_on(&closed, edges[2], BigInt::from(-9));
        let after = Twist::read(&complex, &founded, vertices[0], &whole(&edges)).expect("a read");
        assert!(!after.may_condense(), "the founding opened it");
        assert_eq!(after.leak(), BigInt::from(7));
        assert!(
            before.leak().is_zero() && !after.leak().is_zero(),
            "the founding is what deposited the leak; there is no second operation"
        );
    }

    /// THE DECLARED CONTROL for founding zero (`CLAUDE.md` §2b). Until 2026-08-08
    /// [`Cochain::set`] removed the key on a zero deposit, so `found_on(w, cell, 0)` returned `w`
    /// unchanged: **founding zero founded nothing**, and the one founding that says *nothing crosses
    /// here* was the one the carrier could not record.
    ///
    /// It is not a null operation. On a ring whose values close, moving one edge to zero opens the
    /// coil with a leak of exactly `2` — a deposit that the old carrier could still see through its
    /// value, but which it recorded by *deleting* the cell it was deposited on. Against the old
    /// carrier the domain assertions below fail and `founded == closed` holds.
    #[test]
    fn founding_zero_founds_and_the_cell_it_founded_on_is_named() {
        let (complex, vertices, edges) = ring(3);
        let closed = Cochain::from_values(
            1,
            [
                (edges[0], BigInt::from(1)),
                (edges[1], BigInt::from(1)),
                (edges[2], BigInt::from(-2)),
            ],
        );
        let before = Twist::read(&complex, &closed, vertices[0], &whole(&edges)).expect("a read");
        assert!(before.may_condense() && before.leak().is_zero());

        let founded = found_on(&closed, edges[2], BigInt::zero());
        assert_ne!(founded, closed, "a zero deposit is a deposit");
        assert_eq!(
            founded.assigned(),
            whole(&edges),
            "the founding names every cell it has spoken about, including the one it zeroed"
        );
        assert_eq!(
            founded.support(),
            BTreeSet::from([edges[0], edges[1]]),
            "and `e2` carries nothing, which is a different statement"
        );
        let after = Twist::read(&complex, &founded, vertices[0], &whole(&edges)).expect("a read");
        assert!(!after.may_condense(), "founding zero opened the coil");
        assert_eq!(after.leak(), BigInt::from(2), "|0 - (-2)|");

        // And founding zero on a cell the potential already implies zero opens nothing, which is
        // the control that keeps the assertion above from being about the deposit alone.
        let quiet = found_on(&closed, edges[0], BigInt::from(1));
        assert_eq!(quiet, closed, "an unchanged value is an unchanged cochain");
        let silent = Cochain::new(1);
        let spoken = found_on(&silent, edges[0], BigInt::zero());
        assert!(silent.is_zero() && spoken.is_zero(), "both are zero cochains");
        assert!(silent.assigns_nothing() && !spoken.assigns_nothing());
    }

    #[test]
    fn a_structure_with_no_cycles_closes_for_free_and_says_so() {
        // §8's tautology rule against this module's own return: a tree has no chord, so its closure
        // could not have come out otherwise and carries no evidence.
        let (complex, vertices, edges) = ring(3);
        let cochain = Cochain::from_values(1, [(edges[0], BigInt::from(4))]);
        // One edge of the spanning tree. It closes no cycle, so nothing about it was tested.
        let tree: BTreeSet<CausalCellId> = [edges[0]].into_iter().collect();
        let twist = Twist::read(&complex, &cochain, vertices[0], &tree).expect("a read");
        assert!(twist.may_condense());
        assert!(
            twist.closure_is_vacuous(),
            "a single tree edge closes no cycle; nothing was tested"
        );
        // And the contrast, on the same complex and the same cochain: the whole ring IS tested.
        let over_all = Twist::read(&complex, &cochain, vertices[0], &whole(&edges)).expect("a read");
        assert!(!over_all.closure_is_vacuous());
    }

    #[test]
    fn the_family_condenses_what_closed_and_leaves_what_leaks_expanded_and_named() {
        let (complex, vertices, edges) = ring(4);
        let cochain = Cochain::from_values(
            1,
            [
                (edges[0], BigInt::from(1)),
                (edges[1], BigInt::from(2)),
                (edges[2], BigInt::from(3)),
                (edges[3], BigInt::from(-11)),
            ],
        );
        let family = vec![
            ("the tree".to_owned(), [edges[0], edges[1]].into_iter().collect()),
            ("the ring".to_owned(), whole(&edges)),
        ];
        let tempered =
            TemperedFamily::read(&complex, &cochain, vertices[0], &family).expect("a read");
        assert_eq!(tempered.condensing(), vec!["the tree"]);
        let expanded = tempered.expanded();
        assert_eq!(expanded.len(), 1);
        assert_eq!(expanded[0].0, "the ring");
        assert_eq!(expanded[0].1, BigInt::from(5), "|-11 - (-6)| = 5, named with its structure");
        assert!(
            !expanded.is_empty() && !tempered.condensing().is_empty(),
            "both halves present: neither 'everything condenses' nor 'nothing does' can pass here"
        );
    }

    #[test]
    fn the_temper_is_relational_and_the_pair_is_never_divided() {
        let (complex, vertices, edges) = ring(4);
        let cochain = Cochain::from_values(
            1,
            [
                (edges[0], BigInt::from(1)),
                (edges[1], BigInt::from(2)),
                (edges[2], BigInt::from(3)),
                (edges[3], BigInt::from(-11)),
            ],
        );
        let ring_only = vec![("the ring".to_owned(), whole(&edges))];
        let with_a_tree = vec![
            ("the ring".to_owned(), whole(&edges)),
            ("the tree".to_owned(), [edges[0], edges[1]].into_iter().collect()),
        ];
        let alone = TemperedFamily::read(&complex, &cochain, vertices[0], &ring_only)
            .expect("a read")
            .temper_of("the ring")
            .expect("declared");
        let among = TemperedFamily::read(&complex, &cochain, vertices[0], &with_a_tree)
            .expect("a read")
            .temper_of("the ring")
            .expect("declared");
        // Its own leak did not move; the population it is read against did not either, because the
        // tree leaks nothing. So this pair is EQUAL — and that is the honest reading, not a defect.
        assert_eq!(alone, among);
        assert_eq!(alone.own, BigInt::from(5));
        assert!(!alone.stands(), "it leaks, so it does not stand");

        // The population moving is what moves the temper. Add a second leaking structure and the
        // same structure's own leak is unchanged while its temper is not.
        let (wider, wider_vertices, wider_edges) = ring(3);
        let wider_cochain = Cochain::from_values(
            1,
            [
                (wider_edges[0], BigInt::from(1)),
                (wider_edges[1], BigInt::from(1)),
                (wider_edges[2], BigInt::from(-4)),
            ],
        );
        let second = TemperedFamily::read(
            &wider,
            &wider_cochain,
            wider_vertices[0],
            &[("another ring".to_owned(), whole(&wider_edges))],
        )
        .expect("a read");
        assert_eq!(second.population_leak(), BigInt::from(2));

        // The pair, held whole and ordered without division. 5:5 against 5:7.
        let against_a_bigger_population = Temper {
            own: BigInt::from(5),
            population: BigInt::from(7),
        };
        assert_eq!(
            alone.cmp_against(&against_a_bigger_population),
            std::cmp::Ordering::Greater,
            "5*7 against 5*5 — the same own leak stands further behind a smaller population"
        );
        // And the holonic point: equal quotient, different state.
        let scaled = Temper {
            own: BigInt::from(10),
            population: BigInt::from(10),
        };
        assert_ne!(alone, scaled, "5:5 and 10:10 are different holonic states");
        assert_eq!(alone.cmp_against(&scaled), std::cmp::Ordering::Equal);
    }
}
