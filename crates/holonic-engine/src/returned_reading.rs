//! The movement between two readings, returned to the production that caused it, as material.
//!
//! ## The measured defect this closes
//!
//! A census of the library modules on 2026-08-08 returned that `holonic-engine`,
//! `holonic-structure`, `relational-geometry` and `holonic-language` carry **no cycles at module
//! granularity**: nothing an engine module emits re-enters any module upstream of it. Two instances
//! were verified by hand and both are here.
//!
//! - [`crate::derivation_atlas::invariant_movement`] and [`crate::derivation_atlas::route_movement`]
//!   were called from exactly one place in the workspace — inside `main` in
//!   `examples/derivation_atlas_reader.rs` — and the result was **printed**.
//!   [`crate::conditioned_derivation`], which produced the derivations being read, consumed no
//!   movement.
//! - [`crate::temper`] and [`crate::derivation_integral`] were built as two halves of one return
//!   path — `accumulation` returns a [`Cochain`], `Twist::read` takes one, `found_on` returns one,
//!   `compare_routes` and `statement_lineage` take one — and **neither file referenced the other**.
//!   `temper` had in-degree zero from everything in the workspace.
//!
//! ## The law
//!
//! `canon/THE_HOLOBROCHOS_SPINE.md` §1, quoting Soma's chain law. Summing consecutive event grains
//! cancels every interior `Σ_k` **while retaining it in the causal interior**:
//!
//! ```text
//!   ∂E_k = Σ_{k+1} − Σ_k + Γ_k
//!   q_n − q_m + B·Σ j_k = Σ r_k
//!   ⟨a, ∂Σ⟩ = ⟨da, Σ⟩            the loop returns its carried interior curvature
//! ```
//!
//! and the sentence that governs the grading:
//!
//! > *"circulation `j ≠ 0`, rest, accumulation, leak, and short circuit are **distinct cuts**."*
//!
//! Five cuts, not one pass/fail. A body that emits and never returns is not *failing to close*; it
//! is at a named cut, and which one is a measurement. Before this module the reading's return left
//! the body and nothing retained it while the production it was a reading of did not move by one
//! bit — `r_k ≠ 0`, `q_{k+1} − q_k = 0`, no `j` anywhere. That is **leak**, and it is measured
//! rather than asserted: `examples/the_reading_returns.rs` shows the second production
//! bit-identical to the first before the join.
//!
//! ## What re-enters, and what may not
//!
//! **Only a movement between two readings re-enters.** Not a reading. That is not a stylistic
//! choice: it is what makes the no-op control structural rather than incidental. **Every one of the
//! five contributors below is differenced against the earlier circuit**, so `read_production(X, X)`
//! returns a still carrier, the carried morphology is *equal* to the standing one, and the second
//! production is bit-identical. Nothing has to be checked for that to hold, and
//! `the_reading_of_a_circuit_against_itself_is_still` holds it there.
//!
//! The differencing matters most where it is least obvious. The temper/integral founding is a
//! *second* pair of readings — the same circuit before and after its own retained remainder is
//! deposited back onto the cochain — and that pair returns on any circuit that leaks, including one
//! no production ever touched. Undifferenced, it would make a reading of a still body non-still.
//!
//! ```text
//!   invariant movement       cells at the moved grade in the symmetric difference of the complexes
//!   route movement           statements founded/withdrawn, routes founded/deepened, became plural
//!   temper movement          structures whose twist opened, and structures whose twist closed
//!   remainder movement       chords the certified remainder gained and lost
//!   founding movement        structures the deposited remainder closed here and not there, and
//!                            route pairs whose residual moved here and did not there
//! ```
//!
//! ## The one rule about what a return says
//!
//! A returned artifact carries two fields. **`whole` is prose and is never read as material;
//! `returned` is material and is never prose.** The mechanism that returned an artifact names it —
//! *"the route movement: routes founded to |- …"* — and that name drives the recurrence law below,
//! but it contributes not one word to the morphology. What contributes words is only what the return
//! **addressed**: cell names, vertex names, statement texts, structure names, route names. Every one
//! of those is the material's own writing.
//!
//! Without that rule the analyst's vocabulary enters the body's morphology. It is not hypothetical:
//! rendering *"at grade 1"* would found the stem `at`, which occurs inside `Nat.zero` in the
//! deposit, and the second production would then differ because of a preposition. That is the
//! absolute-frame contaminant `CLAUDE.md` §0 names, one level down.
//!
//! ## How a return conditions a production
//!
//! Through the seam [`crate::conditioned_derivation`] already declares, and through no new one.
//! [`FoundedMorphology::from_founded_words`] is *"the seam a foreign conditioner enters by — a
//! foreign conditioner hands over its founded words each with its own lineage rendered as text, and
//! everything below runs unchanged."*
//!
//! **The reading is a foreign conditioner.** Its returns are wholes of material; [`expose`] reads
//! them by the same codec every other whole goes through; and each return is one **whole** for
//! [`crate::conditioned_derivation::COMMITTING_RECURRENCE`], so a word **two distinct returns
//! named** commits and reaches the derivation path, while a word one return named stays
//! `Provisional` — retained as lineage, off the path. That is the laboratory's
//! `propose_views`/`commit_views` distinction applied to the return path: provisional contact is not
//! continuing cultivation. Nothing is ranked, scored, gated on a magnitude, damped, discounted or
//! decayed; a stem is not weighted by how many returns named it and the population that did not
//! commit is handed back whole by [`ConditionedAgain::provisional_by_return`].
//!
//! `derive` then runs **unchanged**. The second production differs because the morphology it
//! conducts through carries stems the first reading founded, and attribution is carried by the type
//! rather than reconstructed: a [`DerivedPassage`] names its licensing stem, and that stem's
//! `wholes` name the returns that founded it.
//!
//! ## The two directions, and why neither is a filter
//!
//! Adding a stem does not only add passages. [`FoundedMorphology::cover`] retains an occurrence only
//! when **maximal**, so a longer returned stem swallows a shorter standing one and the passages that
//! shorter stem licensed are then *structurally absent*. Both directions are reported, both are
//! attributed, and monotonicity is never claimed. This is the same retained-fiber reopening
//! `StemAblation`'s own `passages_appeared` records, running the other way.
//!
//! ## What is refused
//!
//! `OPEN` may not be resolved by choosing. Where the two readings disagree the complete pair is kept
//! — [`ProductionReading`] carries `before` and `after` whole, and the founding step keeps both the
//! raw cochain and the founded one — and where a returned word has been contacted once and not
//! twice it is neither promoted nor discarded. There is no tie-break anywhere in this module.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;

use crate::algebraic::CausalCellId;
use crate::conditioned_derivation::{
    derive, expose, ConditionedCircuit, ConditionedDerivationRefusal, DerivationQuery,
    DerivedPassage, Exposure, FoundedMorphology, StemStanding,
};
use crate::derivation_atlas::{
    invariant_movement, route_movement, Derivation, InvariantMovement, MovedField, RouteMovement,
};
use crate::derivation_integral::{
    accumulation, potential_over, statement_lineage, AccumulationRule, DerivationIntegralError,
    HolonomyPopulation, NamedChord, NamedPotential,
};
use crate::rebase_invariants::{PivotRule, RebaseInvariants};
use crate::running_integral::Cochain;
use crate::temper::{found_on, TemperedFamily, Twist};

// -------------------------------------------------------------------------------------------------
// The carrier
// -------------------------------------------------------------------------------------------------

/// One artifact a reading returned, named by the mechanism that returned it.
///
/// `whole` is that mechanism's name and is **never read as material** — it is the source identity the
/// recurrence law counts distinct wholes by, and nothing else reads it. `returned` is what the return
/// addressed, in the material's own writing, and is the only field [`ReturnedReading::exposures`]
/// reads.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ReturnedArtifact {
    pub whole: String,
    pub returned: String,
}

impl ReturnedArtifact {
    /// The return addressed nothing: the mechanism moved but named no material.
    pub fn addresses_nothing(&self) -> bool {
        self.returned.trim().is_empty()
    }
}

/// The movement between two readings, held in the form a production consumes its material in.
///
/// **Empty exactly when the two readings agree.** Every contributor is a difference, so this carrier
/// cannot be non-empty over a still reading, and the no-op control is a property of the construction
/// rather than a check bolted onto it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReturnedReading {
    pub schema: String,
    returns: Vec<ReturnedArtifact>,
}

impl ReturnedReading {
    /// A reading that returned nothing.
    pub fn still() -> Self {
        Self {
            schema: "holonic-engine.returned-reading.v1".to_owned(),
            returns: Vec::new(),
        }
    }

    pub fn from_returns(returns: impl IntoIterator<Item = ReturnedArtifact>) -> Self {
        Self {
            schema: "holonic-engine.returned-reading.v1".to_owned(),
            returns: returns.into_iter().collect(),
        }
    }

    /// Every returned artifact, in the order the mechanisms returned them.
    pub fn returns(&self) -> &[ReturnedArtifact] {
        &self.returns
    }

    /// Nothing moved between the two readings.
    pub fn is_still(&self) -> bool {
        self.returns.is_empty()
    }

    /// The returns that named no material. A mechanism can move without addressing anything — a
    /// grade whose Betti number changed over an unchanged cell population is the standing case — and
    /// such a return is retained and reported rather than dropped, because dropping it would make
    /// the returned population look like the moved population.
    pub fn addressing_nothing(&self) -> Vec<&ReturnedArtifact> {
        self.returns
            .iter()
            .filter(|artifact| artifact.addresses_nothing())
            .collect()
    }

    /// Each return read by the same codec every other whole of material goes through.
    pub fn exposures(&self) -> Vec<Exposure> {
        self.returns
            .iter()
            .map(|artifact| expose(&artifact.whole, &artifact.returned))
            .collect()
    }

    /// The returns that named a word, by name.
    pub fn wholes_naming(&self, word: &str) -> Vec<String> {
        self.exposures()
            .into_iter()
            .filter(|exposure| exposure.words.iter().any(|carried| carried == word))
            .map(|exposure| exposure.whole)
            .collect()
    }

    /// **The join.** The standing morphology with this reading's returns witnessed into it.
    ///
    /// The standing population is re-founded from its own stems first, in its own founding order,
    /// carrying each stem's wholes and foreign lineage whole — so a still reading returns a
    /// morphology **equal** to the one it was handed, not merely equivalent to it. The returns are
    /// then witnessed after, each under its own mechanism's name.
    ///
    /// Nothing is removed, nothing is reweighted, and no stem is preferred to another. A word the
    /// standing corpus already committed simply gains one more whole in its lineage.
    pub fn carried_into(&self, standing: &FoundedMorphology) -> FoundedMorphology {
        let carried = standing.founded().iter().map(|stem| {
            (
                stem.stem.clone(),
                stem.wholes.clone(),
                stem.foreign_lineage.clone(),
            )
        });
        let mut returned: Vec<(String, Vec<String>, Vec<String>)> = Vec::new();
        for exposure in self.exposures() {
            for word in exposure.words {
                returned.push((
                    word,
                    vec![exposure.whole.clone()],
                    vec![exposure.whole.clone()],
                ));
            }
        }
        FoundedMorphology::from_founded_words(carried.chain(returned))
    }
}

// -------------------------------------------------------------------------------------------------
// One circuit, read
// -------------------------------------------------------------------------------------------------

/// The declared family the temper is read over: one structure per declaration vertex, being the
/// 1-cells incident to it — its recruitments and its reach.
///
/// This is the circuit's own decomposition and not a family invented for the reading: a declaration
/// *is* the cells it founded. The names are the declarations' own.
pub fn declared_family(circuit: &ConditionedCircuit) -> Vec<(String, BTreeSet<CausalCellId>)> {
    let mut family: BTreeMap<String, BTreeSet<CausalCellId>> = BTreeMap::new();
    for ((key, _symbol), cell) in circuit.circuit.recruitments() {
        family.entry(key.clone()).or_default().insert(*cell);
    }
    for ((key, _statement), cell) in circuit.circuit.reaches() {
        family.entry(key.clone()).or_default().insert(*cell);
    }
    family.into_iter().collect()
}

/// The 0-cell the potential is founded from: the first vertex in the circuit's own canonical order.
///
/// A base has to be named and the complex does not privilege one. Canonical order over the vertex
/// *names* is material-derived, reproduces on any machine, and carries no filesystem or insertion
/// frame. It is a declaration, not a tie-break: no magnitude is compared to choose it.
pub fn canonical_base(circuit: &ConditionedCircuit) -> Option<String> {
    circuit.circuit.vertices().keys().next().cloned()
}

/// One circuit, read through the temper ⇄ derivation-integral circuit, in sequence.
///
/// ```text
///   derivation_integral::accumulation   the rule's 1-cochain over the circuit
///   temper::TemperedFamily::read        which declarations close and which leak, named
///   derivation_integral::potential_over the certified remainder: every retained chord, addressed
///   temper::found_on                    the remainder deposited back onto the cochain
///   temper::TemperedFamily::read        the twist, read again
///   derivation_integral::potential_over the remainder, read again
/// ```
///
/// The founding step is `⟨a, ∂Σ⟩ = ⟨da, Σ⟩` in checkable form. `found_potential` builds its spanning
/// tree from the incidence alone, so depositing a chord's own **implied** value moves no tree edge
/// and cannot move another chord's residual: the coil closes exactly, and
/// [`CircuitReading::the_returned_remainder_closes_the_coil`] is the return, not an assumption.
#[derive(Clone, Debug)]
pub struct CircuitReading {
    pub schema: String,
    pub rule: AccumulationRule,
    pub base: String,
    pub invariants: RebaseInvariants,
    /// What the rule accumulated over the circuit.
    pub accumulated: Cochain,
    /// The twist of every declared structure under that accumulation.
    pub temper: TemperedFamily,
    /// The certified remainder: the chords the potential could not carry, each addressed.
    pub potential: NamedPotential,
    /// The same cochain with every retained chord's own implied value deposited on it.
    pub founded: Cochain,
    /// The twist, read again on the founded cochain.
    pub tempered_again: TemperedFamily,
    /// The remainder, read again on the founded cochain.
    pub potential_again: NamedPotential,
    /// Every declaration that leaks, with the leak, named. Never counted.
    pub leaking: Vec<(String, BigInt)>,
}

impl CircuitReading {
    /// The remainder, returned to the cochain, closed the coil: no chord is retained and no declared
    /// structure leaks.
    pub fn the_returned_remainder_closes_the_coil(&self) -> bool {
        self.potential_again.admits_a_potential()
            && self.tempered_again.population_leak() == BigInt::from(0)
    }

    /// The remainder had something to close. A reading over a circuit that already admitted a
    /// potential closes for free and the verdict above carries no evidence — `CLAUDE.md` §8's
    /// tautology rule against this organ's own return.
    pub fn the_closure_was_tested(&self) -> bool {
        !self.potential.admits_a_potential() && self.potential.cycle_rank() > 0
    }

    /// The structures that may condense, named.
    pub fn condensing(&self) -> Vec<&str> {
        self.temper.condensing()
    }
}

/// Read one circuit: the accumulation, the temper, the certified remainder, and the founding that
/// returns the remainder to the cochain.
pub fn read_circuit(
    circuit: &ConditionedCircuit,
    rule: AccumulationRule,
    pivot: PivotRule,
) -> Result<CircuitReading, ReturnedReadingRefusal> {
    let base = canonical_base(circuit).ok_or(ReturnedReadingRefusal::CircuitCarriesNoVertex)?;
    let base_cell = circuit.circuit.vertices()[&base];
    let complex = circuit.circuit.complex();

    let invariants = circuit
        .circuit
        .invariants(pivot)
        .map_err(|refusal| ReturnedReadingRefusal::Invariants(format!("{refusal}")))?;

    let accumulated = accumulation(circuit, rule);
    let family = declared_family(circuit);
    let temper = TemperedFamily::read(complex, &accumulated, base_cell, &family)?;
    let potential = potential_over(circuit, &accumulated, rule, &base)?;

    let mut founded = accumulated.clone();
    for chord in &potential.search.retained_obstructions {
        founded = found_on(&founded, chord.cell, chord.implied.clone());
    }
    let tempered_again = TemperedFamily::read(complex, &founded, base_cell, &family)?;
    let potential_again = potential_over(circuit, &founded, rule, &base)?;

    let leaking = temper
        .expanded()
        .into_iter()
        .map(|(name, leak)| (name.to_owned(), leak))
        .collect();

    Ok(CircuitReading {
        schema: "holonic-engine.returned-reading-circuit.v1".to_owned(),
        rule,
        base,
        invariants,
        accumulated,
        temper,
        potential,
        founded,
        tempered_again,
        potential_again,
        leaking,
    })
}

// -------------------------------------------------------------------------------------------------
// The movement between two readings
// -------------------------------------------------------------------------------------------------

/// One declared structure whose twist moved between two readings.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TwistMovement {
    pub structure: String,
    pub before: Option<Twist>,
    pub after: Option<Twist>,
}

impl TwistMovement {
    /// It closed before — or did not exist — and leaks now.
    pub fn opened(&self) -> bool {
        let closed_before = self.before.as_ref().is_none_or(Twist::may_condense);
        closed_before && self.after.as_ref().is_some_and(|twist| !twist.may_condense())
    }

    /// It leaked before and closes now, or is gone.
    pub fn closed(&self) -> bool {
        let leaked_before = self.before.as_ref().is_some_and(|twist| !twist.may_condense());
        leaked_before && self.after.as_ref().is_none_or(Twist::may_condense)
    }
}

/// What one production moved in the machine's own reading of its deposits, and what that movement
/// returned as material.
#[derive(Clone, Debug)]
pub struct ProductionReading {
    pub schema: String,
    pub rule: AccumulationRule,
    pub statement: String,
    /// The circuit before the production: the deposit alone.
    pub before: CircuitReading,
    /// The circuit after it: the deposit and what the body derived.
    pub after: CircuitReading,
    pub movement: InvariantMovement,
    pub routes: RouteMovement,
    /// Declared structures whose twist moved between the two circuits.
    pub twists: Vec<TwistMovement>,
    /// Chords the certified remainder gained, addressed.
    pub remainder_founded: Vec<NamedChord>,
    /// Chords the certified remainder lost, by name.
    pub remainder_withdrawn: Vec<String>,
    /// The route lineage of the queried statement on the after circuit's raw accumulation.
    pub lineage: Option<HolonomyPopulation>,
    /// The same lineage on the cochain the remainder was founded back onto. Both are kept: the pair
    /// is the return, and choosing one would be resolving an `OPEN` by choosing.
    pub lineage_founded: Option<HolonomyPopulation>,
    /// Why one of the two lineages was refused, if it was.
    pub lineage_refusal: Option<String>,
    /// The carrier.
    pub returned: ReturnedReading,
}

fn cells_at_grade(circuit: &ConditionedCircuit, grade: u32) -> BTreeSet<String> {
    circuit
        .circuit
        .complex()
        .cells()
        .values()
        .filter(|cell| cell.grade == grade)
        .map(|cell| cell.name.clone())
        .collect()
}

fn lines(named: impl IntoIterator<Item = String>) -> String {
    let mut rendered = String::new();
    for name in named {
        rendered.push_str(&name);
        rendered.push('\n');
    }
    rendered
}

fn twist_of<'a>(family: &'a TemperedFamily, structure: &str) -> Option<&'a Twist> {
    family
        .twists
        .iter()
        .find(|(name, _)| name == structure)
        .map(|(_, twist)| twist)
}

/// The structures that leaked under one circuit's raw accumulation and close once its own retained
/// remainder is deposited back onto the cochain: the founding's return, for one circuit.
fn closed_by_founding(reading: &CircuitReading) -> BTreeSet<String> {
    reading
        .temper
        .expanded()
        .into_iter()
        .map(|(name, _)| name.to_owned())
        .filter(|name| twist_of(&reading.tempered_again, name).is_some_and(Twist::may_condense))
        .collect()
}

/// The compared route pairs of one statement's lineage whose residual moved when the retained
/// remainder was deposited back onto the cochain, by pair name.
///
/// Returns the two lineages whole beside the moved population: the pair is the return, and keeping
/// only one would resolve an `OPEN` by choosing.
fn lineage_founding_movement(
    circuit: &ConditionedCircuit,
    reading: &CircuitReading,
    rule: AccumulationRule,
    statement: &str,
) -> (
    Option<HolonomyPopulation>,
    Option<HolonomyPopulation>,
    BTreeSet<String>,
    Option<String>,
) {
    let mut refusal = None;
    let raw = match statement_lineage(circuit, &reading.accumulated, rule, statement) {
        Ok(population) => Some(population),
        Err(refused) => {
            refusal = Some(format!("{refused}"));
            None
        }
    };
    let deposited = statement_lineage(circuit, &reading.founded, rule, statement).ok();
    let moved = match (&raw, &deposited) {
        (Some(here), Some(there)) => here
            .compared
            .iter()
            .zip(&there.compared)
            .filter(|(before, after)| before.residual() != after.residual())
            .map(|(before, _)| before.named())
            .collect(),
        _ => BTreeSet::new(),
    };
    (raw, deposited, moved, refusal)
}

/// Read what one production moved, and return that movement as material.
///
/// `before` is the circuit of the deposit alone; `after` is the circuit of the deposit together with
/// what the body derived. Every field of the returned [`ReturnedReading`] is a difference between
/// the two, so a production that moved nothing returns a still reading.
pub fn read_production(
    before: &ConditionedCircuit,
    after: &ConditionedCircuit,
    rule: AccumulationRule,
    pivot: PivotRule,
    statement: &str,
) -> Result<ProductionReading, ReturnedReadingRefusal> {
    let earlier = read_circuit(before, rule, pivot)?;
    let later = read_circuit(after, rule, pivot)?;

    let movement = invariant_movement(&earlier.invariants, &later.invariants);
    let routes = route_movement(&before.circuit, &after.circuit);

    let mut returns: Vec<ReturnedArtifact> = Vec::new();

    // --- the invariant movement --------------------------------------------------------------
    for grade in movement.moved() {
        let was = cells_at_grade(before, grade.grade);
        let now = cells_at_grade(after, grade.grade);
        let moved: BTreeSet<String> = was.symmetric_difference(&now).cloned().collect();
        let fields: Vec<&str> = grade
            .fields_moved()
            .into_iter()
            .map(|field| match field {
                MovedField::Cells => "cells",
                MovedField::BoundaryRank => "boundary rank",
                MovedField::FillingRank => "filling rank",
                MovedField::Betti => "betti",
                MovedField::Torsion => "torsion",
            })
            .collect();
        returns.push(ReturnedArtifact {
            whole: format!(
                "the invariant movement at grade {}: {}",
                grade.grade,
                fields.join(", ")
            ),
            returned: lines(moved),
        });
    }

    // --- the route movement ------------------------------------------------------------------
    if !routes.founded_statements().is_empty() {
        returns.push(ReturnedArtifact {
            whole: "the route movement: statements founded".to_owned(),
            returned: lines(routes.founded_statements().iter().cloned()),
        });
    }
    if !routes.withdrawn_statements().is_empty() {
        returns.push(ReturnedArtifact {
            whole: "the route movement: statements withdrawn".to_owned(),
            returned: lines(routes.withdrawn_statements().iter().cloned()),
        });
    }
    for (reached, reaching) in routes.founded_routes() {
        returns.push(ReturnedArtifact {
            whole: format!("the route movement: routes founded to |- {reached}"),
            returned: lines(reaching.iter().cloned()),
        });
    }
    for (reached, deepened) in routes.deepened_routes() {
        returns.push(ReturnedArtifact {
            whole: format!("the route movement: routes deepened to |- {reached}"),
            returned: lines(deepened.keys().cloned()),
        });
    }
    if !routes.became_plural().is_empty() {
        returns.push(ReturnedArtifact {
            whole: "the route movement: statements that became plural".to_owned(),
            returned: lines(routes.became_plural().iter().cloned()),
        });
    }

    // --- the temper movement -----------------------------------------------------------------
    let structures: BTreeSet<String> = earlier
        .temper
        .twists
        .iter()
        .chain(&later.temper.twists)
        .map(|(name, _)| name.clone())
        .collect();
    let mut twists = Vec::new();
    for structure in structures {
        let was = twist_of(&earlier.temper, &structure);
        let now = twist_of(&later.temper, &structure);
        if was == now {
            continue;
        }
        let moved = TwistMovement {
            structure: structure.clone(),
            before: was.cloned(),
            after: now.cloned(),
        };
        if moved.opened() {
            let addressed: BTreeSet<String> = later
                .potential
                .retained
                .iter()
                .filter(|chord| chord.cell.starts_with(&structure))
                .map(|chord| chord.cell.clone())
                .collect();
            returns.push(ReturnedArtifact {
                whole: format!("the temper movement: the structure {structure} opened"),
                returned: lines(std::iter::once(structure.clone()).chain(addressed)),
            });
        }
        if moved.closed() {
            let addressed: BTreeSet<String> = earlier
                .potential
                .retained
                .iter()
                .filter(|chord| chord.cell.starts_with(&structure))
                .map(|chord| chord.cell.clone())
                .collect();
            returns.push(ReturnedArtifact {
                whole: format!("the temper movement: the structure {structure} closed"),
                returned: lines(std::iter::once(structure.clone()).chain(addressed)),
            });
        }
        twists.push(moved);
    }
    // The founding's own return, **differenced against the earlier circuit**. Every structure the
    // deposited remainder closed here that it did not close there. Differencing is what keeps the
    // carrier still over a still production: the temper/integral founding is a second pair of
    // readings and, undifferenced, it would return on a circuit that never moved.
    let closed_before = closed_by_founding(&earlier);
    let closed_after = closed_by_founding(&later);
    let newly_closed: BTreeSet<String> = closed_after.difference(&closed_before).cloned().collect();
    if !newly_closed.is_empty() {
        returns.push(ReturnedArtifact {
            whole: "the founding movement: structures the returned remainder closed".to_owned(),
            returned: lines(newly_closed),
        });
    }

    // --- the remainder movement --------------------------------------------------------------
    let retained_before: BTreeSet<String> = earlier
        .potential
        .retained
        .iter()
        .map(|chord| chord.cell.clone())
        .collect();
    let retained_after: BTreeSet<String> = later
        .potential
        .retained
        .iter()
        .map(|chord| chord.cell.clone())
        .collect();
    let remainder_founded: Vec<NamedChord> = later
        .potential
        .retained
        .iter()
        .filter(|chord| !retained_before.contains(&chord.cell))
        .cloned()
        .collect();
    let remainder_withdrawn: Vec<String> = retained_before
        .difference(&retained_after)
        .cloned()
        .collect();
    for chord in &remainder_founded {
        returns.push(ReturnedArtifact {
            whole: format!(
                "the remainder movement: the chord {} was retained, residual {}",
                chord.cell, chord.residual
            ),
            returned: lines([
                chord.cell.clone(),
                chord.tail.clone(),
                chord.head.clone(),
            ]),
        });
    }
    if !remainder_withdrawn.is_empty() {
        returns.push(ReturnedArtifact {
            whole: "the remainder movement: chords withdrawn".to_owned(),
            returned: lines(remainder_withdrawn.iter().cloned()),
        });
    }

    // --- the founding movement, on the route lineage, differenced against the earlier circuit ---
    let (_, _, moved_before, _) = lineage_founding_movement(before, &earlier, rule, statement);
    let (lineage, lineage_founded, moved_after, lineage_refusal) =
        lineage_founding_movement(after, &later, rule, statement);
    let newly_moved: BTreeSet<String> = moved_after.difference(&moved_before).cloned().collect();
    if !newly_moved.is_empty() {
        returns.push(ReturnedArtifact {
            whole: "the founding movement: route pairs whose residual moved when the \
                    remainder was returned to the cochain"
                .to_owned(),
            returned: lines(newly_moved),
        });
    }

    Ok(ProductionReading {
        schema: "holonic-engine.returned-reading-production.v1".to_owned(),
        rule,
        statement: statement.to_owned(),
        before: earlier,
        after: later,
        movement,
        routes,
        twists,
        remainder_founded,
        remainder_withdrawn,
        lineage,
        lineage_founded,
        lineage_refusal,
        returned: ReturnedReading::from_returns(returns),
    })
}

// -------------------------------------------------------------------------------------------------
// The second production
// -------------------------------------------------------------------------------------------------

/// One stem the return witnessed, with the returns that witnessed it and where it stands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReturnedStem {
    pub stem: String,
    /// Every whole that witnessed it, in the order it did — corpus wholes first, then returns.
    pub wholes: Vec<String>,
    /// The returns that named it, by mechanism. Named, never counted.
    pub returns: Vec<String>,
    /// The first [`crate::conditioned_derivation::COMMITTING_RECURRENCE`] wholes: **the recurrence
    /// that committed it**. This is the founding order the morphology already keeps, not a ranking —
    /// no whole is preferred to another and none is discarded; the whole population is `wholes`.
    pub committed_at: Vec<String>,
    /// Whether the standing corpus had already committed it before the reading returned.
    pub stood_before: bool,
    pub standing: StemStanding,
}

/// One passage of the second production, with the earlier returns that caused it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttributedPassage {
    pub passage: String,
    /// The stem that licensed it.
    pub stem: String,
    /// The identifier the passage brought that the licensing route did not recruit.
    pub brought: String,
    /// The earlier returns that founded the licensing stem, by mechanism. **Empty is a report, not
    /// a default**: a founded passage whose stem no return witnessed is not attributable to the
    /// reading and must be read as a defect in the join.
    pub caused_by: Vec<String>,
    /// The recurrence that committed the licensing stem: the wholes at which it crossed from
    /// provisional contact to continuing cultivation.
    pub committed_at: Vec<String>,
}

/// One passage the second production lost, with the returned stem that swallowed its licence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WithdrawnPassage {
    pub passage: String,
    /// The stem that had licensed it.
    pub stem: String,
    /// The returned stems that take one of this passage's own occurrences by maximality, each with
    /// the identifier and offset it takes it at. **Occurrence-precise**: a returned stem merely
    /// containing the licensing text is not an explanation, and listing one would be attribution by
    /// coincidence.
    pub covered_by: Vec<TakenOccurrence>,
    pub caused_by: Vec<String>,
}

/// One occurrence a returned stem takes from a standing one, addressed.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TakenOccurrence {
    /// The returned stem that takes it.
    pub taker: String,
    /// The identifier the occurrence stood in.
    pub identifier: String,
    /// Where the standing stem stood in it.
    pub at: usize,
    /// Where the returned stem stands, which strictly contains the position above.
    pub taken_at: usize,
}

/// One passage present in both productions whose licensing lineage moved.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelicensedPassage {
    pub passage: String,
    pub stem: String,
    /// The routes that licensed it before, and after. Both kept.
    pub routes_before: Vec<String>,
    pub routes_after: Vec<String>,
}

/// Two productions on one standing and one query, the second conducted through the morphology the
/// first reading's return founded.
#[derive(Clone, Debug)]
pub struct ConditionedAgain {
    pub schema: String,
    pub first: Vec<DerivedPassage>,
    pub second: Vec<DerivedPassage>,
    /// The morphology the second production conducted through.
    pub carried: FoundedMorphology,
    pub founded_passages: Vec<AttributedPassage>,
    pub withdrawn_passages: Vec<WithdrawnPassage>,
    pub relicensed_passages: Vec<RelicensedPassage>,
    /// Stems the return committed that the standing morphology had not.
    pub committed_by_return: Vec<ReturnedStem>,
    /// Words one return named and no second return did. **Retained, off the path, never discarded.**
    /// An empty population here would say the recurrence law never refused anything, which would
    /// make the law decorative.
    pub provisional_by_return: Vec<ReturnedStem>,
}

impl ConditionedAgain {
    /// The second production differs from the first.
    pub fn the_production_moved(&self) -> bool {
        self.first != self.second
    }

    /// Every moved passage names at least one earlier return.
    pub fn every_movement_is_attributed(&self) -> bool {
        self.founded_passages
            .iter()
            .all(|passage| !passage.caused_by.is_empty())
            && self
                .withdrawn_passages
                .iter()
                .all(|passage| !passage.caused_by.is_empty())
    }

    /// The recurrence law refused something: some returned word was contacted once and stayed
    /// provisional. If every returned word commits, the law is decorative.
    pub fn the_recurrence_law_refused_something(&self) -> bool {
        !self.provisional_by_return.is_empty()
    }
}

fn passage_key(passage: &DerivedPassage) -> (String, String) {
    (passage.name.clone(), passage.text.clone())
}

fn routes_of(passage: &DerivedPassage) -> Vec<String> {
    passage
        .routes()
        .into_iter()
        .map(str::to_owned)
        .collect()
}

/// Every returned stem that **strictly contains** the occurrence `[at, at + length)` in `identifier`,
/// with the offset it stands at.
///
/// This is [`FoundedMorphology::cover`]'s maximality rule read backwards, and it is the only honest
/// account of a withdrawal: a returned stem that merely shares a letter with the licensing one
/// explains nothing, and naming it would be attribution by coincidence.
fn occurrences_taken(
    identifier: &str,
    at: usize,
    length: usize,
    returned: &[&str],
) -> Vec<TakenOccurrence> {
    let folded = identifier.to_ascii_lowercase();
    let mut taken = Vec::new();
    for candidate in returned {
        let span = candidate.len();
        for start in 0..folded.len().saturating_sub(span.saturating_sub(1)) {
            let Some(window) = folded.get(start..start + span) else {
                continue;
            };
            if window != *candidate {
                continue;
            }
            if start <= at && at + length <= start + span && (start, span) != (at, length) {
                taken.push(TakenOccurrence {
                    taker: (*candidate).to_owned(),
                    identifier: identifier.to_owned(),
                    at,
                    taken_at: start,
                });
            }
        }
    }
    taken
}

/// **The join, conducted.** The same standing and the same query, derived twice: once through the
/// standing morphology and once through the morphology this reading's return founded.
///
/// Nothing about the query moves between the two productions. The only thing that moves is the
/// morphology, and the only thing that moved it is the return.
pub fn condition_again(
    standing: &[Derivation],
    morphology: &FoundedMorphology,
    query: &DerivationQuery,
    returned: &ReturnedReading,
) -> Result<ConditionedAgain, ConditionedDerivationRefusal> {
    let first = derive(standing, morphology, query)?;
    let carried = returned.carried_into(morphology);
    let second = derive(standing, &carried, query)?;

    // Which stems the return founded, and where each stands.
    let mut committed_by_return = Vec::new();
    let mut provisional_by_return = Vec::new();
    for stem in carried.founded() {
        let returns = returned.wholes_naming(&stem.stem);
        if returns.is_empty() {
            continue;
        }
        let stood_before = morphology
            .stem(&stem.stem)
            .is_some_and(|earlier| earlier.standing() == StemStanding::Committed);
        let entry = ReturnedStem {
            stem: stem.stem.clone(),
            wholes: stem.wholes.clone(),
            returns,
            committed_at: stem
                .wholes
                .iter()
                .take(crate::conditioned_derivation::COMMITTING_RECURRENCE)
                .cloned()
                .collect(),
            stood_before,
            standing: stem.standing(),
        };
        match (entry.standing, stood_before) {
            (StemStanding::Committed, false) => committed_by_return.push(entry),
            (StemStanding::Provisional, _) => provisional_by_return.push(entry),
            (StemStanding::Committed, true) => {}
        }
    }

    let cause_of = |stem: &str| -> Vec<String> { returned.wholes_naming(stem) };
    let committing = |stem: &str| -> Vec<String> {
        carried.stem(stem).map_or_else(Vec::new, |founded| {
            founded
                .wholes
                .iter()
                .take(crate::conditioned_derivation::COMMITTING_RECURRENCE)
                .cloned()
                .collect()
        })
    };

    let before: BTreeMap<(String, String), &DerivedPassage> = first
        .iter()
        .map(|passage| (passage_key(passage), passage))
        .collect();
    let after: BTreeMap<(String, String), &DerivedPassage> = second
        .iter()
        .map(|passage| (passage_key(passage), passage))
        .collect();

    let founded_passages: Vec<AttributedPassage> = second
        .iter()
        .filter(|passage| !before.contains_key(&passage_key(passage)))
        .map(|passage| AttributedPassage {
            passage: passage.name.clone(),
            stem: passage.stem.clone(),
            brought: passage.brought.clone(),
            caused_by: cause_of(&passage.stem),
            committed_at: committing(&passage.stem),
        })
        .collect();

    let returned_stems: Vec<&str> = committed_by_return
        .iter()
        .map(|stem| stem.stem.as_str())
        .collect();
    let withdrawn_passages: Vec<WithdrawnPassage> = first
        .iter()
        .filter(|passage| !after.contains_key(&passage_key(passage)))
        .map(|passage| {
            let mut covered_by: BTreeSet<TakenOccurrence> = BTreeSet::new();
            for bridge in &passage.bridges {
                for (identifier, at) in [
                    (&bridge.held, bridge.held_at),
                    (&bridge.brought, bridge.brought_at),
                ] {
                    covered_by.extend(occurrences_taken(
                        identifier,
                        at,
                        passage.stem.len(),
                        &returned_stems,
                    ));
                }
            }
            let covered_by: Vec<TakenOccurrence> = covered_by.into_iter().collect();
            let caused_by: Vec<String> = covered_by
                .iter()
                .flat_map(|taken| cause_of(&taken.taker))
                .collect::<BTreeSet<String>>()
                .into_iter()
                .collect();
            WithdrawnPassage {
                passage: passage.name.clone(),
                stem: passage.stem.clone(),
                covered_by,
                caused_by,
            }
        })
        .collect();

    let relicensed_passages: Vec<RelicensedPassage> = second
        .iter()
        .filter_map(|passage| {
            let earlier = before.get(&passage_key(passage))?;
            if earlier.bridges == passage.bridges {
                return None;
            }
            Some(RelicensedPassage {
                passage: passage.name.clone(),
                stem: passage.stem.clone(),
                routes_before: routes_of(earlier),
                routes_after: routes_of(passage),
            })
        })
        .collect();

    Ok(ConditionedAgain {
        schema: "holonic-engine.returned-reading-conditioned-again.v1".to_owned(),
        first,
        second,
        carried,
        founded_passages,
        withdrawn_passages,
        relicensed_passages,
        committed_by_return,
        provisional_by_return,
    })
}

// -------------------------------------------------------------------------------------------------
// Refusals
// -------------------------------------------------------------------------------------------------

#[derive(Debug)]
pub enum ReturnedReadingRefusal {
    /// A circuit with no 0-cell has no base to found a potential from.
    CircuitCarriesNoVertex,
    /// The complex refused the invariant reading.
    Invariants(String),
    Integral(DerivationIntegralError),
    RunningIntegral(crate::running_integral::RunningIntegralError),
}

impl std::fmt::Display for ReturnedReadingRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CircuitCarriesNoVertex => {
                write!(formatter, "the circuit carries no 0-cell to found a potential from")
            }
            Self::Invariants(refusal) => write!(formatter, "{refusal}"),
            Self::Integral(refusal) => write!(formatter, "{refusal}"),
            Self::RunningIntegral(refusal) => write!(formatter, "{refusal}"),
        }
    }
}

impl std::error::Error for ReturnedReadingRefusal {}

impl From<DerivationIntegralError> for ReturnedReadingRefusal {
    fn from(refusal: DerivationIntegralError) -> Self {
        Self::Integral(refusal)
    }
}

impl From<crate::running_integral::RunningIntegralError> for ReturnedReadingRefusal {
    fn from(refusal: crate::running_integral::RunningIntegralError) -> Self {
        Self::RunningIntegral(refusal)
    }
}

// -------------------------------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    use crate::conditioned_derivation::{ConditionedBody, PassageOrigin};
    use crate::derivation_atlas::CircuitAperture;

    const STATEMENT: &str = "(P : Prop) (h : P) : exactCarrier P";

    /// Verbatim from `standing/output/lean-proof-production/`. Real production, quoted rather than
    /// read from disk so the fixture carries no filesystem frame.
    fn deposit() -> Vec<(String, String)> {
        vec![
            (
                "lean-proof-production/carrier-transport-00000.lean".to_owned(),
                "import KernelWitness\nnamespace Soma\ntheorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by\n  assumption\nend Soma\n".to_owned(),
            ),
            (
                "lean-proof-production/carrier-transport-00012.lean".to_owned(),
                "import KernelWitness\nnamespace Soma\ntheorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by\n  apply exact_chart_carry\n  apply exact_chart_carry\n  assumption\nend Soma\n".to_owned(),
            ),
            (
                "lean-kernel-witness/carrier_transport-00000.lean".to_owned(),
                "namespace Soma\ndef exactCarrier (P : Prop) : Prop := P\nvariable (P : Prop)\ntheorem carrier_transport (h : P) : exactCarrier P := formal_carry\nend Soma\n".to_owned(),
            ),
        ]
    }

    /// Two wholes of prose that between them commit `exact`, `carry` and `chart`.
    fn corpus() -> Vec<Exposure> {
        vec![
            expose(
                "prose/one",
                "an exact chart carries a transport; the carry is exact and the chart is a chart",
            ),
            expose(
                "prose/two",
                "exact transport carries a chart across a carrier, and the carry stands",
            ),
        ]
    }

    fn body() -> ConditionedBody {
        let mut mounted = ConditionedBody::mount(deposit()).expect("the deposit declares theorems");
        mounted.condition(&corpus());
        mounted
    }

    fn readings() -> (ConditionedCircuit, ConditionedCircuit) {
        let mounted = body();
        let query = DerivationQuery::reaching(STATEMENT);
        let before = crate::conditioned_derivation::found_conditioned_circuit(
            mounted.standing().to_vec(),
            CircuitAperture::STATEMENT_INCIDENT,
        )
        .expect("the deposit founds");
        let after = mounted
            .circuit(&query, CircuitAperture::STATEMENT_INCIDENT)
            .expect("the production founds");
        (before, after)
    }

    #[test]
    fn the_falsifier_fires_before_the_repair() {
        // Two productions on the same standing, the same morphology and the same query are
        // bit-identical. This is the defect, measured: the body emits and drops.
        let mounted = body();
        let query = DerivationQuery::reaching(STATEMENT);
        let first = mounted.derive(&query).expect("derives");
        let second = mounted.derive(&query).expect("derives");
        assert_eq!(first, second, "the unjoined body cannot move on its own return");
        assert!(!first.is_empty(), "a still production of nothing proves nothing");
    }

    #[test]
    fn a_still_reading_carries_a_morphology_equal_to_the_one_it_was_handed() {
        // THE NO-OP CONTROL, at the level of the carrier: the round trip through the seam is the
        // identity, so a reading that returned nothing cannot move a production by construction.
        let mounted = body();
        let still = ReturnedReading::still();
        assert!(still.is_still());
        let carried = still.carried_into(mounted.morphology());
        assert_eq!(&carried, mounted.morphology());

        let query = DerivationQuery::reaching(STATEMENT);
        let again = condition_again(
            &mounted.standing_derivations(),
            mounted.morphology(),
            &query,
            &still,
        )
        .expect("derives");
        assert_eq!(again.first, again.second);
        assert!(!again.the_production_moved());
        assert!(again.founded_passages.is_empty() && again.withdrawn_passages.is_empty());
    }

    #[test]
    fn a_reading_that_addressed_nothing_moves_nothing_either() {
        // The second half of the no-op control: a reading whose mechanisms moved but which named no
        // material. The returns are retained and reported; the morphology does not move.
        let mounted = body();
        let empty = ReturnedReading::from_returns([ReturnedArtifact {
            whole: "the invariant movement at grade 7: betti".to_owned(),
            returned: String::new(),
        }]);
        assert!(!empty.is_still());
        assert_eq!(empty.addressing_nothing().len(), 1);
        assert_eq!(&empty.carried_into(mounted.morphology()), mounted.morphology());
    }

    #[test]
    fn the_temper_and_the_integral_are_called_in_sequence_and_the_remainder_closes_the_coil() {
        let (_, after) = readings();
        let reading = read_circuit(&after, AccumulationRule::RecruitmentLoad, PivotRule::SmallestMagnitude)
            .expect("reads");
        assert!(
            reading.the_closure_was_tested(),
            "a remainder that was already empty closes for free and proves nothing"
        );
        assert!(
            reading.the_returned_remainder_closes_the_coil(),
            "the deposited remainder must close every chord it addressed"
        );
        assert_ne!(reading.accumulated, reading.founded, "the founding deposited something");
        assert!(!reading.leaking.is_empty(), "the raw accumulation leaks somewhere");
    }

    #[test]
    fn the_reading_of_a_circuit_against_itself_is_still() {
        // THE NO-OP CONTROL in its strongest form, and the reason every contributor is differenced
        // against the earlier circuit. The production's circuit leaks under `RecruitmentLoad`, so
        // the temper/integral founding returns on it — and that return must NOT reach the carrier,
        // because the production did not move. The deposit's own circuit would not do here: it is a
        // star, it admits a potential, and the founding would have nothing to return.
        let (_, after) = readings();
        let alone = read_circuit(&after, AccumulationRule::RecruitmentLoad, PivotRule::SmallestMagnitude)
            .expect("reads");
        assert!(
            !alone.potential.admits_a_potential() && alone.potential.cycle_rank() > 0,
            "a circuit that already admits a potential makes this control vacuous"
        );

        let reading = read_production(
            &after,
            &after,
            AccumulationRule::RecruitmentLoad,
            PivotRule::SmallestMagnitude,
            STATEMENT,
        )
        .expect("reads");
        assert!(
            reading.returned.is_still(),
            "a circuit read against itself returned {:?}",
            reading
                .returned
                .returns()
                .iter()
                .map(|artifact| artifact.whole.as_str())
                .collect::<Vec<_>>()
        );

        let mounted = body();
        let query = DerivationQuery::reaching(STATEMENT);
        let again = condition_again(
            &mounted.standing_derivations(),
            mounted.morphology(),
            &query,
            &reading.returned,
        )
        .expect("derives");
        assert_eq!(&again.carried, mounted.morphology());
        assert_eq!(again.first, again.second);
    }

    #[test]
    fn the_movement_between_two_readings_is_non_empty_and_addresses_material() {
        let (before, after) = readings();
        let reading = read_production(
            &before,
            &after,
            AccumulationRule::RecruitmentLoad,
            PivotRule::SmallestMagnitude,
            STATEMENT,
        )
        .expect("reads");
        assert!(!reading.returned.is_still());
        assert!(
            reading
                .returned
                .returns()
                .iter()
                .any(|artifact| !artifact.addresses_nothing()),
            "a movement that names no material cannot condition anything"
        );
        assert!(!reading.routes.founded_routes().is_empty());
    }

    #[test]
    fn the_second_production_differs_and_every_difference_names_the_return_that_caused_it() {
        let mounted = body();
        let (before, after) = readings();
        let reading = read_production(
            &before,
            &after,
            AccumulationRule::RecruitmentLoad,
            PivotRule::SmallestMagnitude,
            STATEMENT,
        )
        .expect("reads");
        let query = DerivationQuery::reaching(STATEMENT);
        let again = condition_again(
            &mounted.standing_derivations(),
            mounted.morphology(),
            &query,
            &reading.returned,
        )
        .expect("derives");

        assert!(again.the_production_moved(), "the return did not reach the production");
        assert!(
            !again.founded_passages.is_empty() || !again.withdrawn_passages.is_empty(),
            "the production moved without founding or withdrawing a passage"
        );
        assert!(
            again.every_movement_is_attributed(),
            "a moved passage that names no earlier return is not a return path"
        );
        assert!(
            !again.committed_by_return.is_empty(),
            "no stem was committed by the return"
        );
        assert!(
            again.the_recurrence_law_refused_something(),
            "every returned word committed; the recurrence law is decorative here"
        );
    }

    #[test]
    fn the_query_did_not_move_between_the_two_productions() {
        // The design constraint that decides whether this is real. Both productions are derived
        // from one `DerivationQuery` value, so a difference cannot be a difference of question.
        let mounted = body();
        let (before, after) = readings();
        let reading = read_production(
            &before,
            &after,
            AccumulationRule::RecruitmentLoad,
            PivotRule::SmallestMagnitude,
            STATEMENT,
        )
        .expect("reads");
        let query = DerivationQuery::reaching(STATEMENT);
        let again = condition_again(
            &mounted.standing_derivations(),
            mounted.morphology(),
            &query,
            &reading.returned,
        )
        .expect("derives");
        assert_eq!(query, DerivationQuery::reaching(STATEMENT));
        // And the standing did not move either: every passage of the deposit is still standing.
        assert!(mounted
            .standing()
            .iter()
            .all(|passage| matches!(passage.origin, PassageOrigin::Standing { .. })));
        assert!(again.the_production_moved());
    }

    #[test]
    fn a_returns_prose_never_becomes_material() {
        // The one rule about what a return says. The mechanism's name carries `movement`, `route`,
        // `the`, `at` and `to`; none of them may be founded as a stem.
        let returned = ReturnedReading::from_returns([ReturnedArtifact {
            whole: "the route movement: routes founded to |- (P : Prop) : exactCarrier P".to_owned(),
            returned: "carrier_transport\n".to_owned(),
        }]);
        let words: BTreeSet<String> = returned
            .exposures()
            .into_iter()
            .flat_map(|exposure| exposure.words)
            .collect();
        assert_eq!(
            words,
            BTreeSet::from(["carrier".to_owned(), "transport".to_owned()])
        );
        for prose in ["the", "route", "movement", "routes", "founded", "to", "at"] {
            assert!(!words.contains(prose), "the mechanism's prose reached the material");
        }
    }

    #[test]
    fn the_declared_family_is_the_circuits_own_decomposition() {
        let (_, after) = readings();
        let family = declared_family(&after);
        assert!(!family.is_empty());
        // Every structure is named by a declaration vertex the circuit carries.
        for (name, structure) in &family {
            assert!(after.circuit.vertices().contains_key(name));
            assert!(!structure.is_empty());
        }
        // And every 1-cell of the complex belongs to exactly one structure: the family is a
        // partition, so the temper's population leak is the circuit's whole leak.
        let carried: usize = family.iter().map(|(_, cells)| cells.len()).sum();
        let ones = after
            .circuit
            .complex()
            .cells()
            .values()
            .filter(|cell| cell.grade == 1)
            .count();
        assert_eq!(carried, ones);
    }
}
