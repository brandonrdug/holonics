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

use holonic_structure::{LocalSequence, LocalSet};
use num_bigint::BigInt;
use serde::Serialize;

use crate::algebraic::CausalCellId;
use crate::conditioned_derivation::{
    Bridge, ConditionedCircuit, ConditionedDerivationRefusal, DerivationQuery, DerivedPassage,
    Exposure, FoundedMorphology, StemStanding, derive, expose,
};
use crate::derivation_atlas::{
    Derivation, InvariantMovement, MovedField, RouteMovement, invariant_movement, route_movement,
};
use crate::derivation_integral::{
    AccumulationRule, DerivationIntegralError, HolonomyPopulation, NamedChord, NamedPotential,
    accumulation, potential_over, statement_lineage,
};
use crate::rebase_invariants::{PivotRule, RebaseInvariants};
use crate::running_integral::Cochain;
use crate::temper::{TemperedFamily, Twist, found_on};

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

    /// **The seal.** This reading as octets, so the return can cross the world's own record instead
    /// of a call.
    ///
    /// `canon/THE_HOLOBROCHOS_SPINE.md` §4 carries Soma's prohibition and this is what it asks for:
    ///
    /// > *"The membrane mails the radiation OUT into the world's own record; the world answers; the
    /// > answer returns as the next light. **Reafference is the world's, never a wire's.**"*
    ///
    /// [`condition_again`] hands this carrier from a reading straight into a production across a
    /// call. Nothing leaves the process, so by §4's test — *did it get written and re-read?* — that
    /// is the shape the contaminant list names. The seal is the other half: [`Self::unseal`] returns
    /// a carrier reconstructed **only** from octets, and a production conditioned on it has consumed
    /// the world's record rather than the emitter's memory.
    ///
    /// **The spine bounds its own test and the bound is carried here.** §4 states that the write-and-
    /// re-read rule is *that file's* `interpretation` and not an entailment from FORMULA, which
    /// requires a shared medium and a genuinely later return without naming a filesystem. So this is
    /// **one** lawful medium, not the only one, and its presence does not convict any other.
    ///
    /// ## The format, and why it is length-prefixed rather than delimited
    ///
    /// A `whole` is a document name and a `returned` is production text; both are arbitrary octets
    /// and both routinely contain newlines. A delimited encoding would have to escape, and an escape
    /// is a codec the reader must agree with silently. Lengths cannot disagree:
    ///
    /// ```text
    ///   <schema>\n
    ///   <count>\n
    ///   <whole octets> <returned octets>\n      one header line per return
    ///   <whole bytes><returned bytes>           immediately after its own header
    /// ```
    ///
    /// The population's order is the order the mechanisms returned in and is retained exactly, so
    /// `unseal(seal(r)) == r` on the nose rather than up to a set.
    pub fn seal(&self) -> Vec<u8> {
        let mut octets = Vec::new();
        octets.extend_from_slice(self.schema.as_bytes());
        octets.push(b'\n');
        octets.extend_from_slice(self.returns.len().to_string().as_bytes());
        octets.push(b'\n');
        for artifact in &self.returns {
            let whole = artifact.whole.as_bytes();
            let returned = artifact.returned.as_bytes();
            octets.extend_from_slice(whole.len().to_string().as_bytes());
            octets.push(b' ');
            octets.extend_from_slice(returned.len().to_string().as_bytes());
            octets.push(b'\n');
            octets.extend_from_slice(whole);
            octets.extend_from_slice(returned);
        }
        octets
    }

    /// **The mouth.** A reading reconstructed from octets and from nothing else.
    ///
    /// Every refusal names the material that caused it, so a body that cannot read its own record
    /// says which octets it could not read rather than returning a shorter population. A truncated
    /// deposit is not a smaller reading.
    pub fn unseal(octets: &[u8]) -> Result<Self, ReturnedReadingRefusal> {
        fn line<'a>(octets: &'a [u8], at: &mut usize) -> Option<&'a str> {
            let rest = octets.get(*at..)?;
            let end = rest.iter().position(|octet| *octet == b'\n')?;
            let read = std::str::from_utf8(&rest[..end]).ok()?;
            *at += end + 1;
            Some(read)
        }

        let mut at = 0usize;
        let schema = line(octets, &mut at)
            .ok_or(ReturnedReadingRefusal::SealCarriesNoSchema)?
            .to_owned();
        if schema != Self::still().schema {
            return Err(ReturnedReadingRefusal::SealSchemaUnknown { declared: schema });
        }
        let count_line =
            line(octets, &mut at).ok_or(ReturnedReadingRefusal::SealCarriesNoPopulationCount)?;
        let count: usize =
            count_line
                .parse()
                .map_err(|_| ReturnedReadingRefusal::SealHeaderMalformed {
                    line: count_line.to_owned(),
                })?;

        let mut returns = Vec::with_capacity(count);
        for _ in 0..count {
            let header = line(octets, &mut at).ok_or(ReturnedReadingRefusal::SealTruncated {
                expected: count,
                read: returns.len(),
            })?;
            let (whole_len, returned_len) = header.split_once(' ').ok_or_else(|| {
                ReturnedReadingRefusal::SealHeaderMalformed {
                    line: header.to_owned(),
                }
            })?;
            let widths: Result<Vec<usize>, _> = [whole_len, returned_len]
                .iter()
                .map(|read| read.parse::<usize>())
                .collect();
            let widths = widths.map_err(|_| ReturnedReadingRefusal::SealHeaderMalformed {
                line: header.to_owned(),
            })?;
            let (whole_len, returned_len) = (widths[0], widths[1]);

            let end = at + whole_len + returned_len;
            if end > octets.len() {
                return Err(ReturnedReadingRefusal::SealTruncated {
                    expected: count,
                    read: returns.len(),
                });
            }
            let whole = std::str::from_utf8(&octets[at..at + whole_len])
                .map_err(|_| ReturnedReadingRefusal::SealIsNotText { at })?
                .to_owned();
            let returned = std::str::from_utf8(&octets[at + whole_len..end])
                .map_err(|_| ReturnedReadingRefusal::SealIsNotText { at: at + whole_len })?
                .to_owned();
            at = end;
            returns.push(ReturnedArtifact { whole, returned });
        }

        if at != octets.len() {
            return Err(ReturnedReadingRefusal::SealCarriesTrailingOctets {
                count: octets.len() - at,
            });
        }
        Ok(Self { schema, returns })
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
        closed_before
            && self
                .after
                .as_ref()
                .is_some_and(|twist| !twist.may_condense())
    }

    /// It leaked before and closes now, or is gone.
    pub fn closed(&self) -> bool {
        let leaked_before = self
            .before
            .as_ref()
            .is_some_and(|twist| !twist.may_condense());
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
            returned: lines([chord.cell.clone(), chord.tail.clone(), chord.head.clone()]),
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

/// The part of a bridge that does not change when its local face or crossing population moves.
///
/// `route` is present deliberately.  Two contacts carrying the same stem at the same offsets but
/// licensed by different deposited routes are two local occurrences, not one pooled carrier.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct BridgeAddress {
    pub route: String,
    pub stem: String,
    pub held: String,
    pub held_at: usize,
    pub brought: String,
    pub brought_at: usize,
}

impl BridgeAddress {
    fn of(bridge: &Bridge) -> Self {
        Self {
            route: bridge.route.to_owned(),
            stem: bridge.stem.to_owned(),
            held: bridge.held.to_owned(),
            held_at: bridge.held_at,
            brought: bridge.brought.to_owned(),
            brought_at: bridge.brought_at,
        }
    }

    fn names(&self, bridge: &Bridge) -> bool {
        self.route == bridge.route
            && self.stem == bridge.stem
            && self.held == bridge.held
            && self.held_at == bridge.held_at
            && self.brought == bridge.brought
            && self.brought_at == bridge.brought_at
    }
}

/// Which receiver-local population of one bridge moved.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum BridgeSite {
    HeldFace,
    BroughtFace,
    HeldCrossings,
    BroughtCrossings,
}

impl BridgeSite {
    const DECLARED: [Self; 4] = [
        Self::HeldFace,
        Self::BroughtFace,
        Self::HeldCrossings,
        Self::BroughtCrossings,
    ];
}

/// One carrier entering or leaving one exact bridge site.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct CarrierMovement {
    pub carrier: String,
    pub stood_before: bool,
    pub stands_after: bool,
    /// Earlier return mechanisms which named this exact entering or leaving carrier.
    pub caused_by: LocalSet<String>,
}

/// The exact difference at one site of one route-local bridge.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct BridgeSiteMovement {
    pub bridge: BridgeAddress,
    pub site: BridgeSite,
    /// Only the local symmetric difference, never the unchanged carrier population.
    pub carriers: LocalSequence<CarrierMovement>,
}

/// One passage present in both productions whose licensing lineage moved.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelicensedPassage {
    pub passage: String,
    pub stem: String,
    /// Every moved bridge site.  Empty means no relicensing occurred.
    pub bridge_movements: LocalSequence<BridgeSiteMovement>,
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

    /// The supplied receipt is the exact difference of the two production populations, and every
    /// local difference names a return.
    ///
    /// This is deliberately stronger than an `all` over the receipt rows.  It refuses duplicate
    /// passage or receipt identities, a missing or surplus row, non-canonical order, and a bridge
    /// movement whose carriers have been pooled across routes or sites.
    pub fn movement_is_exactly_attributed(&self) -> bool {
        movement_receipt_is_exact(self)
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

fn same_passage(left: &DerivedPassage, right: &DerivedPassage) -> bool {
    left.name == right.name && left.text == right.text
}

fn bridge_at<'a>(passage: &'a DerivedPassage, address: &BridgeAddress) -> Option<&'a Bridge> {
    passage.bridges.iter().find(|bridge| address.names(bridge))
}

fn carriers_at(bridge: Option<&Bridge>, site: BridgeSite) -> &[String] {
    let Some(bridge) = bridge else {
        return &[];
    };
    match site {
        BridgeSite::HeldFace => &bridge.held_face,
        BridgeSite::BroughtFace => &bridge.brought_face,
        BridgeSite::HeldCrossings => &bridge.held_crossings,
        BridgeSite::BroughtCrossings => &bridge.brought_crossings,
    }
}

/// Every bridge/site difference between two occurrences of one passage.
fn bridge_site_movements(
    before: &DerivedPassage,
    after: &DerivedPassage,
    causes_of: &impl Fn(&str) -> LocalSet<String>,
) -> LocalSequence<BridgeSiteMovement> {
    let mut addresses = LocalSet::new();
    for bridge in &before.bridges {
        addresses.insert(BridgeAddress::of(bridge));
    }
    for bridge in &after.bridges {
        addresses.insert(BridgeAddress::of(bridge));
    }

    let mut movements = LocalSequence::new();
    for address in addresses {
        let before_bridge = bridge_at(before, &address);
        let after_bridge = bridge_at(after, &address);
        for site in BridgeSite::DECLARED {
            let before_carriers = carriers_at(before_bridge, site);
            let after_carriers = carriers_at(after_bridge, site);
            let mut carriers = LocalSequence::new();
            for carrier in before_carriers {
                if !after_carriers.contains(carrier) {
                    carriers.push(CarrierMovement {
                        carrier: carrier.to_owned(),
                        stood_before: true,
                        stands_after: false,
                        caused_by: causes_of(carrier),
                    });
                }
            }
            for carrier in after_carriers {
                if !before_carriers.contains(carrier) {
                    carriers.push(CarrierMovement {
                        carrier: carrier.to_owned(),
                        stood_before: false,
                        stands_after: true,
                        caused_by: causes_of(carrier),
                    });
                }
            }
            if !carriers.is_empty() {
                movements.push(BridgeSiteMovement {
                    bridge: BridgeAddress {
                        route: address.route.to_owned(),
                        stem: address.stem.to_owned(),
                        held: address.held.to_owned(),
                        held_at: address.held_at,
                        brought: address.brought.to_owned(),
                        brought_at: address.brought_at,
                    },
                    site,
                    carriers,
                });
            }
        }
    }
    movements
}

fn strictly_ordered<T: Ord>(members: &[T]) -> bool {
    members.windows(2).all(|pair| pair[0] < pair[1])
}

fn bridge_population_is_canonical(passage: &DerivedPassage) -> bool {
    if !strictly_ordered(&passage.bridges) {
        return false;
    }
    let mut addresses = LocalSet::new();
    for bridge in &passage.bridges {
        if !addresses.insert(BridgeAddress::of(bridge))
            || !strictly_ordered(&bridge.held_face)
            || !strictly_ordered(&bridge.brought_face)
            || !strictly_ordered(&bridge.held_crossings)
            || !strictly_ordered(&bridge.brought_crossings)
        {
            return false;
        }
    }
    true
}

fn production_is_canonical(production: &[DerivedPassage]) -> bool {
    let ordered = production.windows(2).all(|pair| {
        (&pair[0].reaches, &pair[0].stem, &pair[0].brought)
            < (&pair[1].reaches, &pair[1].stem, &pair[1].brought)
    });
    if !ordered {
        return false;
    }
    let mut names = LocalSet::new();
    for passage in production {
        if !names.insert(passage.name.as_str()) || !bridge_population_is_canonical(passage) {
            return false;
        }
    }
    true
}

fn passage_named<'a>(production: &'a [DerivedPassage], name: &str) -> Option<&'a DerivedPassage> {
    production.iter().find(|passage| passage.name == name)
}

fn matching_passage<'a>(
    production: &'a [DerivedPassage],
    sought: &DerivedPassage,
) -> Option<&'a DerivedPassage> {
    production
        .iter()
        .find(|passage| same_passage(passage, sought))
}

fn returned_stem<'a>(returned: &'a [ReturnedStem], stem: &str) -> Option<&'a ReturnedStem> {
    returned.iter().find(|candidate| candidate.stem == stem)
}

fn returned_causes(stem: &ReturnedStem) -> LocalSet<String> {
    let mut causes = LocalSet::new();
    for cause in &stem.returns {
        causes.insert(cause.to_owned());
    }
    causes
}

fn relicensing_structure_is_exact(
    receipt: &RelicensedPassage,
    before: &DerivedPassage,
    after: &DerivedPassage,
    returned: &[ReturnedStem],
) -> bool {
    let no_causes = |_: &str| LocalSet::new();
    let expected = bridge_site_movements(before, after, &no_causes);
    if expected.is_empty() || receipt.bridge_movements.len() != expected.len() {
        return false;
    }

    let mut seen = LocalSet::new();
    for movement in &receipt.bridge_movements {
        if !seen.insert((&movement.bridge, movement.site)) {
            return false;
        }
        let Some(expected_movement) = expected.iter().find(|candidate| {
            candidate.bridge == movement.bridge && candidate.site == movement.site
        }) else {
            return false;
        };
        if expected_movement.carriers.len() != movement.carriers.len() {
            return false;
        }
        let mut carriers_seen = LocalSet::new();
        for carrier in &movement.carriers {
            let Some(returned_stem) = returned_stem(returned, &carrier.carrier) else {
                return false;
            };
            if !carriers_seen.insert(carrier.carrier.as_str())
                || carrier.stood_before == carrier.stands_after
                || carrier.caused_by.is_empty()
                || carrier.caused_by != returned_causes(returned_stem)
                || !expected_movement.carriers.iter().any(|expected_carrier| {
                    expected_carrier.carrier == carrier.carrier
                        && expected_carrier.stood_before == carrier.stood_before
                        && expected_carrier.stands_after == carrier.stands_after
                })
            {
                return false;
            }
        }
    }
    true
}

/// Recompute the complete movement population and compare it to the supplied causal receipt.
fn movement_receipt_is_exact(receipt: &ConditionedAgain) -> bool {
    if !production_is_canonical(&receipt.first) || !production_is_canonical(&receipt.second) {
        return false;
    }
    let mut returned_stems = LocalSet::new();
    for stem in &receipt.committed_by_return {
        if !returned_stems.insert(stem.stem.as_str()) || stem.returns.is_empty() {
            return false;
        }
    }

    // One readable passage name must continue to name one artifact.  A text substitution under the
    // same name is exact movement, but this receipt shape cannot honestly describe it as either a
    // founding or a withdrawal, so it is refused rather than silently paired.
    for passage in &receipt.first {
        if passage_named(&receipt.second, &passage.name)
            .is_some_and(|later| !same_passage(passage, later))
        {
            return false;
        }
    }

    let mut founded = LocalSet::new();
    let mut withdrawn = LocalSet::new();
    let mut relicensed = LocalSet::new();
    for passage in &receipt.second {
        match matching_passage(&receipt.first, passage) {
            None => {
                founded.insert(passage.name.to_owned());
            }
            Some(earlier) if earlier.bridges != passage.bridges => {
                relicensed.insert(passage.name.to_owned());
            }
            Some(_) => {}
        }
    }
    for passage in &receipt.first {
        if matching_passage(&receipt.second, passage).is_none() {
            withdrawn.insert(passage.name.to_owned());
        }
    }

    // Equal semantic populations in a different vector or bridge order are not a causal movement.
    // Canonicality above rejects the moved ordering rather than letting empty receipt rows pass.
    if receipt.first != receipt.second
        && founded.is_empty()
        && withdrawn.is_empty()
        && relicensed.is_empty()
    {
        return false;
    }

    let mut founded_receipts = LocalSet::new();
    for passage in &receipt.founded_passages {
        if !founded_receipts.insert(passage.passage.to_owned())
            || passage.caused_by.is_empty()
            || passage.committed_at.is_empty()
        {
            return false;
        }
        let Some(actual) = passage_named(&receipt.second, &passage.passage) else {
            return false;
        };
        if matching_passage(&receipt.first, actual).is_some()
            || passage.stem != actual.stem
            || passage.brought != actual.brought
        {
            return false;
        }
        let Some(returned) = returned_stem(&receipt.committed_by_return, &passage.stem) else {
            return false;
        };
        if passage.caused_by != returned.returns || passage.committed_at != returned.committed_at {
            return false;
        }
    }
    if founded != founded_receipts {
        return false;
    }

    let mut returned_names = LocalSequence::new();
    for stem in &receipt.committed_by_return {
        returned_names.push(stem.stem.as_str());
    }
    let mut withdrawn_receipts = LocalSet::new();
    for passage in &receipt.withdrawn_passages {
        if !withdrawn_receipts.insert(passage.passage.to_owned())
            || passage.covered_by.is_empty()
            || passage.caused_by.is_empty()
        {
            return false;
        }
        let Some(actual) = passage_named(&receipt.first, &passage.passage) else {
            return false;
        };
        if matching_passage(&receipt.second, actual).is_some() || passage.stem != actual.stem {
            return false;
        }
        let mut expected_covered = LocalSet::new();
        for bridge in &actual.bridges {
            for (identifier, at) in [
                (&bridge.held, bridge.held_at),
                (&bridge.brought, bridge.brought_at),
            ] {
                for taken in occurrences_taken(identifier, at, actual.stem.len(), &returned_names) {
                    expected_covered.insert(taken);
                }
            }
        }
        let mut opened_covered = LocalSet::new();
        for taken in &passage.covered_by {
            if !opened_covered.insert(taken.to_owned()) {
                return false;
            }
        }
        if opened_covered != expected_covered {
            return false;
        }
        let mut expected_causes = LocalSet::new();
        for taken in &expected_covered {
            let Some(returned) = returned_stem(&receipt.committed_by_return, &taken.taker) else {
                return false;
            };
            for cause in &returned.returns {
                expected_causes.insert(cause.to_owned());
            }
        }
        let mut opened_causes = LocalSet::new();
        for cause in &passage.caused_by {
            if !opened_causes.insert(cause.to_owned()) {
                return false;
            }
        }
        if opened_causes != expected_causes {
            return false;
        }
    }
    if withdrawn != withdrawn_receipts {
        return false;
    }

    let mut relicensed_receipts = LocalSet::new();
    for passage in &receipt.relicensed_passages {
        if !relicensed_receipts.insert(passage.passage.to_owned()) {
            return false;
        }
        let Some(before) = passage_named(&receipt.first, &passage.passage) else {
            return false;
        };
        let Some(after) = passage_named(&receipt.second, &passage.passage) else {
            return false;
        };
        if !same_passage(before, after)
            || passage.stem != after.stem
            || !relicensing_structure_is_exact(passage, before, after, &receipt.committed_by_return)
        {
            return false;
        }
    }
    relicensed == relicensed_receipts
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
/// **The world-mediated conditioning: the only entry that cannot be handed a wire.**
///
/// It takes **octets**, not a carrier. A caller holding a `ReturnedReading` in memory cannot reach
/// this function without sealing it first, and a caller who sealed to disk and then conditioned on
/// the memory value would have to call [`condition_again`] by name to do it.
///
/// That distinction is the whole content. `canon/THE_HOLOBROCHOS_SPINE.md` §4 quotes Soma's
/// prohibition — *"Reafference is the world's, never a wire's"* — and its test is one question: *did
/// it get written and re-read?* A function whose argument is a live carrier cannot answer that
/// question about itself; one whose argument is octets has already answered it, because octets are
/// what a world's record is made of.
///
/// **The bound the spine states about itself is carried here too:** FORMULA requires a shared medium
/// and a genuinely later return and names no filesystem, so this is one lawful medium rather than
/// the only one, and the seal is not an architectural theorem.
pub fn condition_again_from_sealed(
    standing: &[Derivation],
    morphology: &FoundedMorphology,
    query: &DerivationQuery,
    sealed: &[u8],
) -> Result<ConditionedAgain, ConditionedDerivationRefusal> {
    let returned = ReturnedReading::unseal(sealed).map_err(|refusal| {
        ConditionedDerivationRefusal::MaterialDeclaresNothing {
            source: format!("the world's record is unreadable: {refusal}"),
        }
    })?;
    condition_again(standing, morphology, query, &returned)
}

/// The in-memory conditioning. **Retained deliberately, and named so a reader can see which one a
/// call site chose** — the still and addressed-nothing controls need to construct a reading directly,
/// and forcing them through a seal would test the codec rather than the no-op.
///
/// A production path calling this rather than [`condition_again_from_sealed`] is the private wire
/// the spine names, and the difference is now visible at the call site instead of in a comment.
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
    let local_causes = |stem: &str| -> LocalSet<String> {
        let mut causes = LocalSet::new();
        for cause in returned.wholes_naming(stem) {
            causes.insert(cause);
        }
        causes
    };
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

    let mut relicensed_passages = LocalSequence::new();
    for passage in &second {
        let Some(earlier) = before.get(&passage_key(passage)) else {
            continue;
        };
        if earlier.bridges == passage.bridges {
            continue;
        }
        relicensed_passages.push(RelicensedPassage {
            passage: passage.name.to_owned(),
            stem: passage.stem.to_owned(),
            bridge_movements: bridge_site_movements(earlier, passage, &local_causes),
        });
    }

    Ok(ConditionedAgain {
        schema: "holonic-engine.returned-reading-conditioned-again.v3".to_owned(),
        first,
        second,
        carried,
        founded_passages,
        withdrawn_passages,
        relicensed_passages: relicensed_passages.into_inner(),
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
    /// The octets end before the schema line does.
    SealCarriesNoSchema,
    /// The octets declare a schema this carrier does not read. Carried by name so a deposit written
    /// by a later version is refused rather than partially understood.
    SealSchemaUnknown {
        declared: String,
    },
    /// The schema line stands alone; no population count follows it.
    SealCarriesNoPopulationCount,
    /// A header line is not the two octet widths this format declares.
    SealHeaderMalformed {
        line: String,
    },
    /// The octets end inside the declared population. **A truncated deposit is not a smaller
    /// reading**, so the count read so far is reported beside the count declared rather than
    /// returned as the answer.
    SealTruncated {
        expected: usize,
        read: usize,
    },
    /// Octets remain after the declared population is complete.
    SealCarriesTrailingOctets {
        count: usize,
    },
    /// A declared width lands inside a multi-octet character.
    SealIsNotText {
        at: usize,
    },
}

impl std::fmt::Display for ReturnedReadingRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CircuitCarriesNoVertex => {
                write!(
                    formatter,
                    "the circuit carries no 0-cell to found a potential from"
                )
            }
            Self::Invariants(refusal) => write!(formatter, "{refusal}"),
            Self::Integral(refusal) => write!(formatter, "{refusal}"),
            Self::RunningIntegral(refusal) => write!(formatter, "{refusal}"),
            Self::SealCarriesNoSchema => {
                write!(
                    formatter,
                    "the sealed octets end before the schema line does"
                )
            }
            Self::SealSchemaUnknown { declared } => {
                write!(
                    formatter,
                    "the sealed octets declare the schema `{declared}`, which this carrier does not read"
                )
            }
            Self::SealCarriesNoPopulationCount => {
                write!(
                    formatter,
                    "the sealed octets carry a schema and no population count"
                )
            }
            Self::SealHeaderMalformed { line } => {
                write!(
                    formatter,
                    "the return header `{line}` is not two octet widths"
                )
            }
            Self::SealTruncated { expected, read } => {
                write!(
                    formatter,
                    "the sealed octets end inside the population: {expected} declared, {read} read"
                )
            }
            Self::SealCarriesTrailingOctets { count } => {
                write!(
                    formatter,
                    "{count} octets remain after the declared population is complete"
                )
            }
            Self::SealIsNotText { at } => {
                write!(
                    formatter,
                    "a declared width lands inside a character at octet {at}"
                )
            }
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

    // --------------------------------------------------------------------------------------------
    // The seal — the return crossing the world's record instead of a call
    // --------------------------------------------------------------------------------------------

    /// A reading whose returned text carries newlines, spaces and a trailing blank line, because
    /// that is what production text is and it is the whole reason the format prefixes lengths.
    fn awkward() -> ReturnedReading {
        ReturnedReading::from_returns([
            ReturnedArtifact {
                whole: "invariant-movement/grade-1".to_owned(),
                returned: "theorem carrier_transport : exactCarrier P := by\n  apply exact_chart_carry\n  assumption\n".to_owned(),
            },
            ReturnedArtifact {
                whole: "route-movement/became-plural".to_owned(),
                returned: "5 3\nnot a header\n\n".to_owned(),
            },
            // A mechanism that moved and addressed nothing. Retained, so the seal must carry an
            // empty return rather than dropping it and shortening the population.
            ReturnedArtifact {
                whole: "temper-movement/closed".to_owned(),
                returned: String::new(),
            },
        ])
    }

    #[test]
    fn the_seal_round_trips_a_reading_whose_text_would_break_a_delimited_codec() {
        let reading = awkward();
        let octets = reading.seal();
        // The second return's text is itself a well-formed header line followed by a blank line. A
        // delimited or line-scanning codec reads it as structure; this one reads it as content.
        assert!(reading.returns()[1].returned.starts_with("5 3\n"));
        assert_eq!(
            ReturnedReading::unseal(&octets).expect("the seal is readable"),
            reading
        );
    }

    #[test]
    fn a_still_reading_seals_and_returns_still() {
        let octets = ReturnedReading::still().seal();
        let read = ReturnedReading::unseal(&octets).expect("a still seal is readable");
        assert!(read.is_still());
        assert_eq!(read, ReturnedReading::still());
    }

    #[test]
    fn the_seal_carries_the_return_that_addressed_nothing() {
        let read = ReturnedReading::unseal(&awkward().seal()).expect("readable");
        assert_eq!(read.returns().len(), 3, "an empty return is a return");
        assert_eq!(read.addressing_nothing().len(), 1);
    }

    /// **The control that makes the seal load-bearing.** Every octet of a real seal is truncated in
    /// turn, and each must refuse by name. A truncated deposit that returned a shorter population
    /// would be a body silently conditioning on less than its own record — the failure the length
    /// prefix exists to prevent.
    #[test]
    fn every_truncation_of_a_seal_refuses_and_none_returns_a_shorter_reading() {
        let reading = awkward();
        let octets = reading.seal();
        for cut in 0..octets.len() {
            match ReturnedReading::unseal(&octets[..cut]) {
                Err(_) => {}
                Ok(read) => panic!(
                    "truncating to {cut} of {} octets returned a reading of {} returns",
                    octets.len(),
                    read.returns().len()
                ),
            }
        }
        assert_eq!(
            ReturnedReading::unseal(&octets)
                .expect("whole")
                .returns()
                .len(),
            3
        );
    }

    #[test]
    fn a_seal_with_trailing_octets_refuses_by_name() {
        let mut octets = awkward().seal();
        octets.push(b'\n');
        assert!(matches!(
            ReturnedReading::unseal(&octets),
            Err(ReturnedReadingRefusal::SealCarriesTrailingOctets { count: 1 })
        ));
    }

    #[test]
    fn a_seal_declaring_another_schema_refuses_rather_than_being_partly_understood() {
        let octets = awkward().seal();
        let text = String::from_utf8(octets).expect("the fixture is text");
        let forged = text
            .replacen("returned-reading.v1", "returned-reading.v2", 1)
            .into_bytes();
        match ReturnedReading::unseal(&forged) {
            Err(ReturnedReadingRefusal::SealSchemaUnknown { declared }) => {
                assert_eq!(declared, "holonic-engine.returned-reading.v2");
            }
            other => panic!("a later schema must be refused by name, got {other:?}"),
        }
    }

    /// The seal is a function of the reading and of nothing else — no clock, no path, no ordering
    /// of a hash map — so two seals of one reading are bit-identical and two checkouts agree.
    #[test]
    fn the_seal_is_a_function_of_the_reading_alone() {
        assert_eq!(awkward().seal(), awkward().seal());
    }

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

    fn returned_conditioning() -> ConditionedAgain {
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
        condition_again(
            &mounted.standing_derivations(),
            mounted.morphology(),
            &DerivationQuery::reaching(STATEMENT),
            &reading.returned,
        )
        .expect("derives")
    }

    #[test]
    fn the_falsifier_fires_before_the_repair() {
        // Two productions on the same standing, the same morphology and the same query are
        // bit-identical. This is the defect, measured: the body emits and drops.
        let mounted = body();
        let query = DerivationQuery::reaching(STATEMENT);
        let first = mounted.derive(&query).expect("derives");
        let second = mounted.derive(&query).expect("derives");
        assert_eq!(
            first, second,
            "the unjoined body cannot move on its own return"
        );
        assert!(
            !first.is_empty(),
            "a still production of nothing proves nothing"
        );
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
        assert_eq!(
            &empty.carried_into(mounted.morphology()),
            mounted.morphology()
        );
    }

    #[test]
    fn the_temper_and_the_integral_are_called_in_sequence_and_the_remainder_closes_the_coil() {
        let (_, after) = readings();
        let reading = read_circuit(
            &after,
            AccumulationRule::RecruitmentLoad,
            PivotRule::SmallestMagnitude,
        )
        .expect("reads");
        assert!(
            reading.the_closure_was_tested(),
            "a remainder that was already empty closes for free and proves nothing"
        );
        assert!(
            reading.the_returned_remainder_closes_the_coil(),
            "the deposited remainder must close every chord it addressed"
        );
        assert_ne!(
            reading.accumulated, reading.founded,
            "the founding deposited something"
        );
        assert!(
            !reading.leaking.is_empty(),
            "the raw accumulation leaks somewhere"
        );
    }

    #[test]
    fn the_reading_of_a_circuit_against_itself_is_still() {
        // THE NO-OP CONTROL in its strongest form, and the reason every contributor is differenced
        // against the earlier circuit. The production's circuit leaks under `RecruitmentLoad`, so
        // the temper/integral founding returns on it — and that return must NOT reach the carrier,
        // because the production did not move. The deposit's own circuit would not do here: it is a
        // star, it admits a potential, and the founding would have nothing to return.
        let (_, after) = readings();
        let alone = read_circuit(
            &after,
            AccumulationRule::RecruitmentLoad,
            PivotRule::SmallestMagnitude,
        )
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

        assert!(
            again.the_production_moved(),
            "the return did not reach the production"
        );
        assert!(
            !again.founded_passages.is_empty() || !again.withdrawn_passages.is_empty(),
            "the production moved without founding or withdrawing a passage"
        );
        assert!(
            again.movement_is_exactly_attributed(),
            "a moved passage that names no earlier return is not a return path"
        );
        assert!(
            !again.relicensed_passages.is_empty(),
            "the fixture moved no bridge face or crossing, so relicensing attribution was untested"
        );
        for passage in &again.relicensed_passages {
            assert!(
                !passage.bridge_movements.is_empty()
                    && passage.bridge_movements.iter().all(|movement| movement
                        .carriers
                        .iter()
                        .all(|carrier| !carrier.caused_by.is_empty())),
                "relicensing {} carried no bridge-local cause",
                passage.passage
            );
        }
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
    fn exact_attribution_refuses_vacuity_duplicates_order_and_a_local_movement_without_cause() {
        let valid = returned_conditioning();
        assert!(valid.movement_is_exactly_attributed());

        let mut missing = returned_conditioning();
        assert!(!missing.founded_passages.is_empty());
        missing.founded_passages.clear();
        assert!(
            !missing.movement_is_exactly_attributed(),
            "an empty receipt passed over a founded population"
        );

        let mut duplicate_receipt = returned_conditioning();
        let mut receipt_donor = returned_conditioning();
        duplicate_receipt
            .founded_passages
            .push(receipt_donor.founded_passages.remove(0));
        assert!(
            !duplicate_receipt.movement_is_exactly_attributed(),
            "a duplicated receipt identity hid the missing bijection"
        );

        let mut duplicate_passage = returned_conditioning();
        let mut passage_donor = returned_conditioning();
        duplicate_passage
            .second
            .push(passage_donor.second.remove(0));
        assert!(
            !duplicate_passage.movement_is_exactly_attributed(),
            "a duplicated production occurrence was collapsed"
        );

        let mounted = body();
        let mut order_only = condition_again(
            &mounted.standing_derivations(),
            mounted.morphology(),
            &DerivationQuery::reaching(STATEMENT),
            &ReturnedReading::still(),
        )
        .expect("derives");
        assert!(order_only.movement_is_exactly_attributed());
        assert!(order_only.second.len() > 1);
        order_only.second.swap(0, 1);
        assert!(order_only.the_production_moved());
        assert!(
            !order_only.movement_is_exactly_attributed(),
            "order-only movement passed an empty receipt"
        );

        let mut uncaused = returned_conditioning();
        let local = &mut uncaused.relicensed_passages[0].bridge_movements[0].carriers[0];
        local.caused_by.clear();
        assert!(
            !uncaused.movement_is_exactly_attributed(),
            "a bridge-local movement without a return passed"
        );
    }

    #[test]
    fn one_carrier_moving_between_bridges_cannot_disappear_into_a_pooled_set() {
        fn pooled(passage: &DerivedPassage) -> LocalSet<String> {
            let mut carriers = LocalSet::new();
            for bridge in &passage.bridges {
                for population in [
                    &bridge.held_face,
                    &bridge.brought_face,
                    &bridge.held_crossings,
                    &bridge.brought_crossings,
                ] {
                    for carrier in population {
                        carriers.insert(carrier.to_owned());
                    }
                }
            }
            carriers
        }

        let mounted = body();
        let query = DerivationQuery::reaching(STATEMENT);
        let mut before_population = mounted.derive(&query).expect("derives");
        let at = before_population
            .iter()
            .position(|passage| {
                passage.bridges.len() > 1
                    && BridgeAddress::of(&passage.bridges[0])
                        != BridgeAddress::of(&passage.bridges[1])
            })
            .expect("the fixture has two local bridges");
        let mut before = before_population.remove(at);
        let mut after_population = mounted.derive(&query).expect("derives again");
        let mut after = after_population.remove(at);
        let carrier = "zzzzzz-local-carrier";
        before.bridges[0].held_face.push(carrier.to_owned());
        after.bridges[1].held_face.push(carrier.to_owned());

        assert_eq!(
            pooled(&before),
            pooled(&after),
            "the control must be invisible to the retired pooled reading"
        );
        let causes = |stem: &str| {
            let mut named = LocalSet::new();
            if stem == carrier {
                named.insert("the addressed return".to_owned());
            }
            named
        };
        let movements = bridge_site_movements(&before, &after, &causes);
        assert_eq!(movements.len(), 2);
        assert_ne!(movements[0].bridge, movements[1].bridge);
        assert!(movements.iter().all(|movement| {
            movement.site == BridgeSite::HeldFace
                && movement.carriers.len() == 1
                && movement.carriers[0].carrier == carrier
                && !movement.carriers[0].caused_by.is_empty()
        }));
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
        assert!(
            mounted
                .standing()
                .iter()
                .all(|passage| matches!(passage.origin, PassageOrigin::Standing { .. }))
        );
        assert!(again.the_production_moved());
    }

    #[test]
    fn a_returns_prose_never_becomes_material() {
        // The one rule about what a return says. The mechanism's name carries `movement`, `route`,
        // `the`, `at` and `to`; none of them may be founded as a stem.
        let returned = ReturnedReading::from_returns([ReturnedArtifact {
            whole: "the route movement: routes founded to |- (P : Prop) : exactCarrier P"
                .to_owned(),
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
            assert!(
                !words.contains(prose),
                "the mechanism's prose reached the material"
            );
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
