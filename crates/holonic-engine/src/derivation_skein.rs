//! The moves a conditioned production made, read as substitutions and paid for by placement.
//!
//! `conditioned_derivation` returns a [`ConditionedCircuit`]: the deposited mathematical material
//! and the passages a conditioned body derived from it, founded as one `GradedCausalComplex`, with
//! `passages_founding` naming, per cell, the passages that put it there. What that carrier did not
//! have was a **move**. A cell records that something is there; it does not record the replacement
//! that deposited it, so nothing in the circuit could be asked *which local substitution paid for
//! this class*.
//!
//! [`crate::skein::Substitution`] is that record — two fillings of one hole across a shared
//! boundary — and `substitution_realizers` already turns a declared substitution family into a
//! realizer population whose landings are `added()`. This module supplies the missing half: it
//! reads the moves **off the production itself** rather than declaring a fixture family, and reads
//! the placement back into the circuit's own vocabulary, so a standing class names the passages it
//! is made of and an open class names the obstruction that keeps it open.
//!
//! ```text
//!   derived passage population  ->  DerivationMove  ->  Substitution  ->  realizer  ->  class
//!   (what the body emitted)         (what replaced      (fixed          (landings    (STANDING
//!                                    what)               boundary,       = added())   or OPEN)
//!                                                        changed
//!                                                        interior)
//! ```
//!
//! ## The three species, and why each one is a move the production actually made
//!
//! A derived passage carries `PassageOrigin::Derived { stem, reaches, brought }`: the founded stem
//! that licensed it, the standing declaration whose recruitment it extends, and the one identifier
//! it brought that that declaration does not carry. Those three coordinates generate the moves:
//!
//! ```text
//!   Deposit               the frame          ->  the frame with one passage's own cells
//!                         (recruited symbol vertices and the statement vertex, which every
//!                          passage reaching that statement already shares)
//!
//!   RecruitmentExchange   one passage        ->  another with the same stem and the same standing
//!                                                declaration, differing only in what it brought.
//!                                                *One recruitment replaced by another.*
//!
//!   LemmaSplit            one passage        ->  the two passages that carry the SAME bridge under
//!                                                two other standing declarations.
//!                                                *One lemma replaced by two.*
//! ```
//!
//! ## The obstruction species this leg exists for
//!
//! A `LemmaSplit` deposits two passages that recruit the same symbols and reach the same statement.
//! They differ only in the standing declaration their name records — and a **name is not a receiver
//! coordinate**. Every cell the split deposits therefore arrives with a twin the declared receiver
//! family cannot separate from it, so the move reaches each of those classes as `2·c` and never as
//! `c`. That is `supported_realizers`' `ReachableOnlyInMultiple`: supported over the rationals,
//! unsupported over the integers, which is the failure of the *integral* cycle-class statement and
//! which `CLAUDE.md` §3 reads as torsion — winding that cannot be un-deposited.
//!
//! It is exhibited rather than asserted, and it **dissolves**: declaring the `Deposit` move for one
//! member of the same bridge reaches those classes singly, the invariant factor returns to one, and
//! the classes stand. Without that second half the `2` could be an artifact of the reduction rather
//! than a statement about what the production's moves can reach.
//!
//! ## Two declared apertures, and why both are in the return
//!
//! The **receiver family** is one dilated section per 0-cell the derived passages recruit, plus one
//! at the statement vertex, each reading `AddressReading::Metric` — the invariant, never the walk
//! order. The **conduct aperture** is the 1-cells the *standing* deposit founded, and no others: the
//! terrain the deposit laid down is what conduct may step across, and the production's own edges are
//! the material being placed rather than the ruler placing it. Both are declared by
//! [`declare_receivers`] and both are legible from its return.
//!
//! Discharge is named by [`crate::substitution_realizers::discharge_substitutions`] and never by
//! `placement::discharge`, which reports a realizer-side aperture widening as the FOUND that pays.
//!
//! ## What is not claimed
//!
//! Nothing here submits a passage to a kernel, and a derived passage is production read as
//! structure exactly as the deposited artifacts are. An invariance verdict carries `skein`'s own
//! boundary clause: it is relative to the declared context family and to the invariants read.
//! Nothing here bears on the Hodge conjecture; per `CLAUDE.md` §3 a deed may be graded by movement
//! on named substructure without claiming the conjecture.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use serde::{Deserialize, Serialize};

use crate::algebraic::{CausalAlgebraicError, CausalCellId};
use crate::complex_system::{cell as cell_of_item, item as item_of_cell, AddressReading, ComplexSystem, ComplexSystemError};
use crate::conditioned_derivation::{ConditionedCircuit, Passage, PassageId, PassageOrigin};
use crate::derivation_atlas::{statement_vertex_key, DerivationIdentity};
use crate::dilation::{dilate, Horizon, WalkOrder};
use crate::placement::Placement;
use crate::rebase_invariants::PivotRule;
use crate::receiver_exact_compression::{ItemId, ObservedSystem};
use crate::skein::Substitution;
use crate::substitution_realizers::{
    place_substitutions, read_and_realize, RealizerAdmission, SubstitutionPlacement,
    SubstitutionRealizers,
};
use crate::supported_realizers::RealizerId;

// -------------------------------------------------------------------------------------------------
// The moves
// -------------------------------------------------------------------------------------------------

/// What a derivation move does to the circuit. Named by mechanism; never ranked.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum MoveSpecies {
    /// The frame becomes the frame carrying one passage's own cells. Withdraws nothing.
    Deposit,
    /// One recruitment replaced by another: same licensing stem, same standing declaration, a
    /// different brought identifier.
    RecruitmentExchange,
    /// One passage replaced by the two that carry the same bridge under two other standing
    /// declarations. The move whose deposits arrive in twins.
    LemmaSplit,
}

impl MoveSpecies {
    pub const fn name(self) -> &'static str {
        match self {
            Self::Deposit => "deposit",
            Self::RecruitmentExchange => "recruitment-exchange",
            Self::LemmaSplit => "lemma-split",
        }
    }
}

/// One move the production made, with the passages on each side of it.
///
/// `substitution` is the move as `skein` reads it; `withdraws` and `deposits` are the same move in
/// the production's vocabulary, so a placement can be reported by passage name rather than by cell
/// identity. `skein::Substitution` is not `Serialize`, which is why this type is not either — the
/// serializable form of the family is the one `SubstitutionRealizers` carries.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DerivationMove {
    pub species: MoveSpecies,
    /// The statement every passage on both sides of the move reaches.
    pub statement: String,
    /// The founded stem that licensed the passages this move deposits.
    pub stem: String,
    /// The passages whose cells the move withdraws, by declaration name.
    pub withdraws: Vec<String>,
    /// The passages whose cells the move deposits, by declaration name.
    pub deposits: Vec<String>,
    pub substitution: Substitution,
}

impl DerivationMove {
    /// The move in the vocabulary a placement reports in.
    pub fn naming(&self, declared: usize) -> MoveNaming {
        MoveNaming {
            declared,
            species: self.species,
            stem: self.stem.clone(),
            withdraws: self.withdraws.clone(),
            deposits: self.deposits.clone(),
        }
    }
}

/// A move, named rather than counted, as a placement reports it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MoveNaming {
    /// The move's declared position, which is also its `RealizerId`.
    pub declared: usize,
    pub species: MoveSpecies,
    pub stem: String,
    pub withdraws: Vec<String>,
    pub deposits: Vec<String>,
}

/// The declared aperture on the production: which derived passages the moves are read over.
///
/// A stem family and nothing else. There is no threshold and no ranking: the caller names the
/// bridges it is reading the production through, and every derived passage licensed by one of them
/// enters. Every standing passage always enters — the deposit is the frame the moves happen in, not
/// part of what is being placed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MoveAperture {
    pub stems: BTreeSet<String>,
}

impl MoveAperture {
    pub fn through(stems: impl IntoIterator<Item = String>) -> Self {
        Self {
            stems: stems.into_iter().collect(),
        }
    }

    /// The stems of at least `letters` characters that licensed something in this population.
    ///
    /// The morphemic bridges: a licence carried by a single residual letter is a different kind of
    /// object from one carried by a whole word the corpus committed, and this names which is being
    /// read. It is an aperture, not a filter on quality — the population it excludes is recoverable
    /// by declaring those stems.
    pub fn morphemic(passages: &[Passage], letters: usize) -> Self {
        Self::through(
            passages
                .iter()
                .filter_map(|passage| match &passage.origin {
                    PassageOrigin::Derived { stem, .. } if stem.chars().count() >= letters => {
                        Some(stem.clone())
                    }
                    _ => None,
                })
                .collect::<BTreeSet<String>>(),
        )
    }
}

/// The passage population this aperture admits, with `PassageId`s renumbered onto their positions.
///
/// [`ConditionedCircuit::passages_founding`] resolves a `PassageId` by indexing `passages`, so a
/// filtered population whose ids still name their old positions would attribute every cell to the
/// wrong passage. The renumbering is what makes the restriction safe, and
/// `every_passage_id_names_its_own_position` is the test that it happened.
pub fn passages_under(passages: &[Passage], aperture: &MoveAperture) -> Vec<Passage> {
    passages
        .iter()
        .filter(|passage| match &passage.origin {
            PassageOrigin::Standing { .. } => true,
            PassageOrigin::Derived { stem, .. } => aperture.stems.contains(stem),
        })
        .enumerate()
        .map(|(position, passage)| Passage {
            id: PassageId(position as u64),
            origin: passage.origin.clone(),
            derivation: passage.derivation.clone(),
            text: passage.text.clone(),
        })
        .collect()
}

/// The 0-cell key the circuit gave one passage, under the circuit's own declared identity.
fn vertex_key(circuit: &ConditionedCircuit, passage: &Passage) -> String {
    match circuit.aperture.identity {
        DerivationIdentity::ByDeclaration => passage.derivation.name.clone(),
        DerivationIdentity::ByRoute => format!("{}#{}", passage.derivation.name, passage.id.0),
    }
}

/// The frame one passage stands in: the symbol vertices it recruits and the statement vertex it
/// reaches, and nothing it founded itself.
///
/// A set of 0-cells, so it is closed under boundary for free. This is the hole every move of this
/// module fills, and it is shared by every passage reaching that statement with that recruitment.
pub fn passage_frame(circuit: &ConditionedCircuit, passage: &Passage) -> BTreeSet<CausalCellId> {
    let mut frame = BTreeSet::new();
    for symbol in passage.derivation.recruited.keys() {
        if let Some(cell) = circuit.circuit.vertices().get(symbol) {
            frame.insert(*cell);
        }
    }
    if let Some(cell) = circuit
        .circuit
        .vertices()
        .get(&statement_vertex_key(&passage.derivation.statement))
    {
        frame.insert(*cell);
    }
    frame
}

/// The cells one passage founded: its own 0-cell, its recruitment 1-cells and its reach 1-cell.
pub fn passage_interior(
    circuit: &ConditionedCircuit,
    passage: &Passage,
) -> BTreeSet<CausalCellId> {
    let key = vertex_key(circuit, passage);
    let mut interior = BTreeSet::new();
    if let Some(cell) = circuit.circuit.vertices().get(&key) {
        interior.insert(*cell);
    }
    for symbol in passage.derivation.recruited.keys() {
        if let Some(cell) = circuit
            .circuit
            .recruitments()
            .get(&(key.clone(), symbol.clone()))
        {
            interior.insert(*cell);
        }
    }
    if let Some(cell) = circuit
        .circuit
        .reaches()
        .get(&(key.clone(), passage.derivation.statement.clone()))
    {
        interior.insert(*cell);
    }
    interior
}

/// The closed subcomplex one passage presents: its frame together with what it founded.
pub fn passage_support(circuit: &ConditionedCircuit, passage: &Passage) -> BTreeSet<CausalCellId> {
    let mut support = passage_frame(circuit, passage);
    support.extend(passage_interior(circuit, passage));
    support
}

/// The derived passages, grouped by the bridge they carry: statement, licensing stem and brought
/// identifier. Members of one group differ **only** in the standing declaration they extend.
fn bridge_groups<'a>(passages: &'a [Passage]) -> BTreeMap<(String, String, String), Vec<&'a Passage>> {
    let mut grouped: BTreeMap<(String, String, String), Vec<&Passage>> = BTreeMap::new();
    for passage in passages {
        if let PassageOrigin::Derived { stem, brought, .. } = &passage.origin {
            grouped
                .entry((
                    passage.derivation.statement.clone(),
                    stem.clone(),
                    brought.clone(),
                ))
                .or_default()
                .push(passage);
        }
    }
    for members in grouped.values_mut() {
        members.sort_by(|left, right| left.derivation.name.cmp(&right.derivation.name));
    }
    grouped
}

/// The derived passages, grouped by the route they extend: statement, licensing stem and the
/// standing declaration. Members of one group differ **only** in what they brought.
fn route_groups<'a>(passages: &'a [Passage]) -> BTreeMap<(String, String, String), Vec<&'a Passage>> {
    let mut grouped: BTreeMap<(String, String, String), Vec<&Passage>> = BTreeMap::new();
    for passage in passages {
        if let PassageOrigin::Derived { stem, reaches, .. } = &passage.origin {
            grouped
                .entry((
                    passage.derivation.statement.clone(),
                    stem.clone(),
                    reaches.clone(),
                ))
                .or_default()
                .push(passage);
        }
    }
    for members in grouped.values_mut() {
        members.sort_by(|left, right| left.derivation.name.cmp(&right.derivation.name));
    }
    grouped
}

fn stem_of(passage: &Passage) -> String {
    match &passage.origin {
        PassageOrigin::Derived { stem, .. } => stem.clone(),
        PassageOrigin::Standing { source } => source.clone(),
    }
}

/// Every `Deposit` move the production made: one per derived passage.
pub fn deposit_moves(circuit: &ConditionedCircuit) -> Vec<DerivationMove> {
    circuit
        .passages
        .iter()
        .filter(|passage| passage.is_derived())
        .map(|passage| {
            let frame = passage_frame(circuit, passage);
            let support = passage_support(circuit, passage);
            DerivationMove {
                species: MoveSpecies::Deposit,
                statement: passage.derivation.statement.clone(),
                stem: stem_of(passage),
                withdraws: Vec::new(),
                deposits: vec![passage.derivation.name.clone()],
                substitution: Substitution {
                    boundary: frame.clone(),
                    before: frame,
                    after: support,
                },
            }
        })
        .collect()
}

/// Every `RecruitmentExchange` the production made: consecutive pairs inside each route group.
///
/// Consecutive rather than all pairs, so the declared family grows linearly with the production and
/// a group of `n` brought identifiers contributes `n - 1` moves rather than `n(n-1)/2`. The
/// population is a chain through the group, which reaches every member.
pub fn exchange_moves(circuit: &ConditionedCircuit) -> Vec<DerivationMove> {
    let mut moves = Vec::new();
    for ((statement, stem, _), members) in route_groups(&circuit.passages) {
        for pair in members.windows(2) {
            let (left, right) = (pair[0], pair[1]);
            let before = passage_support(circuit, left);
            let after = passage_support(circuit, right);
            let boundary: BTreeSet<CausalCellId> = before.intersection(&after).copied().collect();
            moves.push(DerivationMove {
                species: MoveSpecies::RecruitmentExchange,
                statement: statement.clone(),
                stem: stem.clone(),
                withdraws: vec![left.derivation.name.clone()],
                deposits: vec![right.derivation.name.clone()],
                substitution: Substitution {
                    boundary,
                    before,
                    after,
                },
            });
        }
    }
    moves
}

/// Every `LemmaSplit` the production made: one passage replaced by the two other members of its own
/// bridge group.
///
/// Only groups of three or more contribute, because a group of two would make the move a rename
/// rather than a split, and a group of one has nothing to split into.
pub fn split_moves(circuit: &ConditionedCircuit) -> Vec<DerivationMove> {
    let mut moves = Vec::new();
    for ((statement, stem, _), members) in bridge_groups(&circuit.passages) {
        if members.len() < 3 {
            continue;
        }
        let withdrawn = members[0];
        let before = passage_support(circuit, withdrawn);
        let mut after: BTreeSet<CausalCellId> = passage_frame(circuit, withdrawn);
        for deposited in &members[1..3] {
            after.extend(passage_support(circuit, deposited));
        }
        let boundary: BTreeSet<CausalCellId> = before.intersection(&after).copied().collect();
        moves.push(DerivationMove {
            species: MoveSpecies::LemmaSplit,
            statement: statement.clone(),
            stem: stem.clone(),
            withdraws: vec![withdrawn.derivation.name.clone()],
            deposits: members[1..3]
                .iter()
                .map(|passage| passage.derivation.name.clone())
                .collect(),
            substitution: Substitution {
                boundary,
                before,
                after,
            },
        });
    }
    moves
}

/// Every move the production made, in species order: splits, then deposits, then exchanges.
pub fn moves_the_production_made(circuit: &ConditionedCircuit) -> Vec<DerivationMove> {
    let mut moves = split_moves(circuit);
    moves.extend(deposit_moves(circuit));
    moves.extend(exchange_moves(circuit));
    moves
}

/// The moves as `skein` reads them, in declared order.
pub fn substitutions(moves: &[DerivationMove]) -> Vec<Substitution> {
    moves
        .iter()
        .map(|declared| declared.substitution.clone())
        .collect()
}

// -------------------------------------------------------------------------------------------------
// The declared contexts and the declared receivers
// -------------------------------------------------------------------------------------------------

/// The declared context family a move's invariance is relative to.
///
/// Three closed subcomplexes that are three different readings and not one counted three times:
///
/// ```text
///   0   the statement vertex alone            the narrowest hole a move can be read in
///   1   every 0-cell of the circuit           the frame with nothing filled in
///   2   frame 1 with the standing deposit     the terrain the production was emitted against
/// ```
///
/// A move whose remainder is the same in all three is invisible to the family, not invariant; the
/// distinction is `skein`'s own and this module does not soften it.
pub fn declared_contexts(
    circuit: &ConditionedCircuit,
    statement: &str,
) -> Vec<BTreeSet<CausalCellId>> {
    let complex = circuit.circuit.complex();
    let statement_vertex: BTreeSet<CausalCellId> = circuit
        .circuit
        .vertices()
        .get(&statement_vertex_key(statement))
        .copied()
        .into_iter()
        .collect();
    let every_vertex: BTreeSet<CausalCellId> = complex
        .cells()
        .values()
        .filter(|cell| cell.grade == 0)
        .map(|cell| cell.id)
        .collect();
    let mut with_deposit = every_vertex.clone();
    for passage in &circuit.passages {
        if !passage.is_derived() {
            with_deposit.extend(passage_support(circuit, passage));
        }
    }
    vec![statement_vertex, every_vertex, with_deposit]
}

/// A declaration this module refuses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DerivationSkeinRefusal {
    /// A focus the receiver family asked for is not a cell of this circuit.
    Algebraic(CausalAlgebraicError),
    /// The conduct aperture or the receiver family was refused by the adapter that reads it.
    System(ComplexSystemError),
    /// The circuit holds no cell the derived production founded, so there is nothing to place and a
    /// returned placement would be a reading of the deposit alone.
    ProductionFoundedNothing,
}

impl std::fmt::Display for DerivationSkeinRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Algebraic(error) => write!(formatter, "{error}"),
            Self::System(error) => write!(formatter, "{error}"),
            Self::ProductionFoundedNothing => write!(
                formatter,
                "the circuit holds no cell a derived passage founded; there is no production to \
                 place and any returned class would be the deposit's"
            ),
        }
    }
}

impl std::error::Error for DerivationSkeinRefusal {}

impl From<CausalAlgebraicError> for DerivationSkeinRefusal {
    fn from(error: CausalAlgebraicError) -> Self {
        Self::Algebraic(error)
    }
}

impl From<ComplexSystemError> for DerivationSkeinRefusal {
    fn from(error: ComplexSystemError) -> Self {
        Self::System(error)
    }
}

/// The 0-cells the receiver family is focused at: every symbol a derived passage recruits, and the
/// statement vertex.
///
/// Focusing at the recruited symbols is what makes the family able to tell one bridge from another —
/// a receiver at `formal_carry` reads a passage that brought it at one step and a passage that
/// brought something else at three. It cannot tell two passages carrying the *same* bridge apart,
/// and that is the point: the only identity separating those two is a declaration name, which is not
/// a receiver coordinate, and the placement's obstruction is exactly that fact.
pub fn receiver_foci(circuit: &ConditionedCircuit) -> Vec<CausalCellId> {
    let mut foci = BTreeSet::new();
    for passage in &circuit.passages {
        if !passage.is_derived() {
            continue;
        }
        foci.extend(passage_frame(circuit, passage));
    }
    foci.into_iter().collect()
}

/// The 1-cells conduct may step across: the ones the **standing deposit** founded, and no others.
///
/// The deposit is the terrain; the production is what is being placed. Admitting the production's
/// own edges as conduct steps would let the material under test carry the ruler that measures it,
/// and every derived vertex would then be separated by the edges it founded rather than by anything
/// a receiver reads.
pub fn conduct_aperture(circuit: &ConditionedCircuit) -> Vec<CausalCellId> {
    let complex = circuit.circuit.complex();
    let mut admitted = BTreeSet::new();
    for passage in &circuit.passages {
        if passage.is_derived() {
            continue;
        }
        for cell in passage_interior(circuit, passage) {
            if complex.cell(cell).is_ok_and(|body| body.grade == 1) {
                admitted.insert(cell);
            }
        }
    }
    admitted.into_iter().collect()
}

/// Declare the system the moves are placed against: the circuit read through
/// [`receiver_foci`] at [`conduct_aperture`], each receiver reading the metric address.
///
/// `AddressReading::Metric` and never `Chart`: the chart is the walk order, and two receivers that
/// differ only in the order they walked would be one frame wearing two names.
pub fn declare_receivers(
    circuit: &ConditionedCircuit,
) -> Result<ComplexSystem<'_>, DerivationSkeinRefusal> {
    let complex = circuit.circuit.complex();
    let mut receivers = Vec::new();
    for focus in receiver_foci(circuit) {
        receivers.push(dilate(complex, focus, Horizon::Unbounded, WalkOrder::Breadth)?);
    }
    if receivers.is_empty() {
        return Err(DerivationSkeinRefusal::ProductionFoundedNothing);
    }
    Ok(ComplexSystem::declare(
        complex,
        AddressReading::Metric,
        receivers,
        conduct_aperture(circuit),
    )?)
}

// -------------------------------------------------------------------------------------------------
// The placement, read back into the circuit's vocabulary
// -------------------------------------------------------------------------------------------------

/// One passage, named, as a class reading reports it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct PassageNaming {
    pub name: String,
    pub derived: bool,
    /// The founded stem that licensed it. `None` for a deposited artifact.
    pub stem: Option<String>,
    /// The identifier it brought that the standing route does not carry. `None` for a deposit.
    pub brought: Option<String>,
}

/// One conduct class, read back into the circuit's own vocabulary.
///
/// Cells and passages are **named**, never counted: a class is what it is made of, and a reading
/// that returned only its size could not be traced to the production that founded it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClassReading {
    pub class: usize,
    pub cells: Vec<String>,
    pub passages: Vec<PassageNaming>,
}

impl ClassReading {
    /// The class holds a cell a derived passage founded.
    pub fn holds_derived(&self) -> bool {
        self.passages.iter().any(|passage| passage.derived)
    }
}

/// A class a move paid for.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SupportedClass {
    pub reading: ClassReading,
    /// The moves that deposited into it. Never empty.
    pub paid_by: Vec<MoveNaming>,
}

/// Why a class stayed open.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum MoveObstruction {
    /// No declared move deposited into this class at all.
    NoMoveReached,
    /// Reached, and every deposit a proper multiple: supported rationally, not integrally. The
    /// integral cycle-class failure, with the factor returned rather than the fact of it.
    ReachedOnlyInMultiple {
        factor: BigInt,
        reached_by: Vec<MoveNaming>,
    },
}

/// A class the receivers distinguish and no move paid for.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpenClass {
    pub reading: ClassReading,
    pub obstruction: MoveObstruction,
}

/// What placing the production's moves returns.
#[derive(Clone, Debug)]
pub struct PlacedMoves {
    /// The declared move family, in declared order. A move's position is its `RealizerId`.
    pub moves: Vec<DerivationMove>,
    pub realizers: SubstitutionRealizers,
    pub placed: SubstitutionPlacement,
    pub supported: Vec<SupportedClass>,
    pub open: Vec<OpenClass>,
}

impl PlacedMoves {
    /// The classes reached only in multiple — the torsion species.
    pub fn reached_only_in_multiple(&self) -> Vec<&OpenClass> {
        self.open
            .iter()
            .filter(|class| {
                matches!(
                    class.obstruction,
                    MoveObstruction::ReachedOnlyInMultiple { .. }
                )
            })
            .collect()
    }

    /// The classes no declared move deposited into — the free species.
    pub fn unreached(&self) -> Vec<&OpenClass> {
        self.open
            .iter()
            .filter(|class| class.obstruction == MoveObstruction::NoMoveReached)
            .collect()
    }

    /// The standing classes that hold a cell a derived passage founded: what the conditioning's own
    /// production paid for.
    pub fn supported_from_production(&self) -> Vec<&SupportedClass> {
        self.supported
            .iter()
            .filter(|class| class.reading.holds_derived())
            .collect()
    }

    /// The invariant factors above one of the incidence this placement rests on.
    pub fn torsion(&self) -> Vec<BigInt> {
        self.placed.placement.support.torsion_obstruction()
    }
}

fn read_class(
    circuit: &ConditionedCircuit,
    class: usize,
    members: &BTreeSet<ItemId>,
) -> ClassReading {
    let complex = circuit.circuit.complex();
    let mut cells = Vec::new();
    let mut passages: BTreeSet<PassageNaming> = BTreeSet::new();
    for item in members {
        let cell = cell_of_item(*item);
        if let Ok(body) = complex.cell(cell) {
            cells.push(body.name.clone());
        }
        for passage in circuit.passages_founding(cell) {
            passages.insert(match &passage.origin {
                PassageOrigin::Derived { stem, brought, .. } => PassageNaming {
                    name: passage.derivation.name.clone(),
                    derived: true,
                    stem: Some(stem.clone()),
                    brought: Some(brought.clone()),
                },
                PassageOrigin::Standing { .. } => PassageNaming {
                    name: passage.derivation.name.clone(),
                    derived: false,
                    stem: None,
                    brought: None,
                },
            });
        }
    }
    cells.sort();
    ClassReading {
        class,
        cells,
        passages: passages.into_iter().collect(),
    }
}

fn naming_of(moves: &[DerivationMove], realizer: RealizerId) -> Option<MoveNaming> {
    let declared = realizer.0 as usize;
    moves
        .get(declared)
        .map(|declared_move| declared_move.naming(declared))
}

/// Which moves deposited into one class, by re-reading the realizer landings rather than by
/// re-deriving them: `place` already decided the classes and this reads its own record.
fn reached_by(
    placed: &SubstitutionPlacement,
    realizers: &SubstitutionRealizers,
    admission: RealizerAdmission,
    class: usize,
) -> Vec<RealizerId> {
    realizers
        .realizations_under(admission, &placed.placement.compression.conduct)
        .into_iter()
        .filter(|realization| realization.landings.contains_key(&class))
        .map(|realization| realization.realizer)
        .collect()
}

/// Place a declared move family against a declared system, and read the result back into the
/// circuit's vocabulary.
///
/// The composition is `skein` founds the realizers, `placement` decides what stands, and this reads
/// standing and open classes back as cells and passages. Nothing here decides which moves *should*
/// be declared; the family is the caller's declaration and it is carried in the return.
pub fn place_moves(
    circuit: &ConditionedCircuit,
    system: &dyn ObservedSystem,
    moves: &[DerivationMove],
    contexts: &[BTreeSet<CausalCellId>],
    admission: RealizerAdmission,
    rule: PivotRule,
) -> PlacedMoves {
    let declared = substitutions(moves);
    let realizers = read_and_realize(circuit.circuit.complex(), &declared, contexts, rule);
    let placed = place_substitutions(system, &realizers, admission);

    let supported: Vec<SupportedClass> = placed
        .placement
        .standing
        .iter()
        .map(|standing| SupportedClass {
            reading: read_class(circuit, standing.class, &standing.members),
            paid_by: standing
                .realizers
                .iter()
                .filter_map(|realizer| naming_of(moves, *realizer))
                .collect(),
        })
        .collect();

    let open: Vec<OpenClass> = placed
        .placement
        .open
        .iter()
        .map(|open| OpenClass {
            reading: read_class(circuit, open.class, &open.members),
            obstruction: match &open.reached_only_in_multiple {
                Some(factor) => MoveObstruction::ReachedOnlyInMultiple {
                    factor: factor.clone(),
                    reached_by: reached_by(&placed, &realizers, admission, open.class)
                        .into_iter()
                        .filter_map(|realizer| naming_of(moves, realizer))
                        .collect(),
                },
                None => MoveObstruction::NoMoveReached,
            },
        })
        .collect();

    PlacedMoves {
        moves: moves.to_vec(),
        realizers,
        placed,
        supported,
        open,
    }
}

/// The cells one class holds, as items — the bridge from a class back to `passages_founding`.
pub fn class_cells(placement: &Placement, class: usize) -> Vec<CausalCellId> {
    placement
        .compression
        .conduct
        .blocks
        .get(class)
        .map(|members| members.iter().copied().map(cell_of_item).collect())
        .unwrap_or_default()
}

/// The class one named cell falls in, computed from the conduct partition directly.
pub fn class_of(placement: &Placement, cell: CausalCellId) -> Option<usize> {
    placement.compression.conduct.block_of(item_of_cell(cell))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conditioned_derivation::{
        expose, ConditionedBody, DerivationQuery, Exposure,
    };
    use crate::derivation_atlas::CircuitAperture;
    use crate::rebase_invariants::{smith_normal_form, IntegerMatrix};
    use crate::substitution_realizers::{discharge_substitutions, SubstitutionDischarge};
    use crate::supported_realizers::{incidence, positive_form, quadratic_value};
    use num_traits::Zero;

    // ---------------------------------------------------------------------------------------
    // the material
    //
    // Three deposited artifacts reach ONE statement under three distinct declarations, so a bridge
    // group has three members and a lemma split has two passages to split into. Three more reach
    // three other statements and are the source of the identifiers a bridge can bring: without them
    // every route group would hold one member, no recruitment exchange would exist, and the
    // invisible aperture would be empty — which is a comparison between a reading and nothing.
    //
    // Two committed stems license — `carry` and `chart` — so an aperture can properly restrict the
    // production. A material licensed by one stem cannot vary that property at all.

    fn corpus() -> Vec<Exposure> {
        vec![
            expose(
                "one",
                "an exact transport must carry the boundary across the chart it was formal on",
            ),
            expose(
                "two",
                "exact transport, and what it must carry across a formal chart",
            ),
        ]
    }

    fn artifact(name: &str, statement: &str, recruits: &str) -> String {
        format!(
            "namespace Soma\ntheorem {name} {statement} := by\n  have step := {recruits}\nend Soma\n"
        )
    }

    fn deposit() -> Vec<(String, String)> {
        vec![
            (
                "direct".to_owned(),
                artifact(
                    "carrier_direct",
                    "(P : Prop) : exactCarrier P",
                    "exact_chart_carry",
                ),
            ),
            (
                "relayed".to_owned(),
                artifact(
                    "carrier_relayed",
                    "(P : Prop) : exactCarrier P",
                    "exact_chart_carry",
                ),
            ),
            (
                "third".to_owned(),
                artifact(
                    "carrier_third",
                    "(P : Prop) : exactCarrier P",
                    "exact_chart_carry",
                ),
            ),
            (
                "elsewhere".to_owned(),
                artifact(
                    "formal_elsewhere",
                    "(P : Prop) : formalCarrier P",
                    "formal_carry",
                ),
            ),
            (
                "charted".to_owned(),
                artifact(
                    "chart_elsewhere",
                    "(P : Prop) : chartCarrier P",
                    "chart_transport",
                ),
            ),
            (
                "crossed".to_owned(),
                artifact(
                    "across_elsewhere",
                    "(P : Prop) : acrossCarrier P",
                    "carry_across",
                ),
            ),
        ]
    }

    fn query() -> DerivationQuery {
        DerivationQuery::reaching("(P : Prop) : exactCarrier P")
    }

    fn body() -> ConditionedBody {
        let mut body = ConditionedBody::mount(deposit()).expect("the deposit reads");
        body.condition(&corpus());
        body
    }

    fn circuit() -> ConditionedCircuit {
        let body = body();
        let passages = body
            .passages(&query())
            .expect("the production reads back");
        let aperture = MoveAperture::morphemic(&passages, 4);
        crate::conditioned_derivation::found_conditioned_circuit(
            passages_under(&passages, &aperture),
            CircuitAperture::STATEMENT_INCIDENT,
        )
        .expect("the circuit founds")
    }

    fn contexts(circuit: &ConditionedCircuit) -> Vec<BTreeSet<CausalCellId>> {
        declared_contexts(circuit, "(P : Prop) : exactCarrier P")
    }

    /// `|M x|^2`, summed directly. The independent route the positive form has to agree with.
    fn squared_norm(matrix: &IntegerMatrix, probe: &[BigInt]) -> BigInt {
        let mut total = BigInt::zero();
        for row in 0..matrix.rows() {
            let mut entry = BigInt::zero();
            for column in 0..matrix.columns() {
                entry += matrix.at(row, column) * &probe[column];
            }
            total += &entry * &entry;
        }
        total
    }

    // ---------------------------------------------------------------------------------------
    // the fixture must be able to vary what is claimed of it

    /// The material carries a bridge group of three, which is what makes a split possible, and a
    /// second statement, which is what makes an unreachable class possible. Without either, half
    /// this file would be unfalsifiable rather than merely unpaid.
    #[test]
    fn the_fixture_holds_a_three_member_bridge_group_and_a_statement_the_production_never_reaches() {
        let circuit = circuit();
        let groups = bridge_groups(&circuit.passages);
        let widest = groups
            .values()
            .map(Vec::len)
            .max()
            .expect("the production licensed something");
        assert!(
            widest >= 3,
            "a split needs three members in one bridge group; the widest is {widest}"
        );

        let statements: BTreeSet<&str> = circuit
            .passages
            .iter()
            .map(|passage| passage.derivation.statement.as_str())
            .collect();
        assert!(
            statements.len() >= 2,
            "one statement only, so every class is on the production's own route: {statements:?}"
        );
    }

    /// A restricted population's ids must name their own positions, or every cell would be
    /// attributed to the wrong passage by `passages_founding`.
    ///
    /// The aperture is built by dropping one licensing stem from the family the production actually
    /// used, so the restriction is provably proper on this material rather than proper by
    /// assumption. `MoveAperture::morphemic` is not used here: on this corpus every licensing stem
    /// is already a whole morpheme, so it restricts nothing and this test would pass against an
    /// implementation that renumbered nothing.
    #[test]
    fn every_passage_id_names_its_own_position_after_the_aperture_restricts_the_population() {
        let body = body();
        let passages = body.passages(&query()).expect("the production reads back");
        let licensing: BTreeSet<String> = passages
            .iter()
            .filter_map(|passage| match &passage.origin {
                PassageOrigin::Derived { stem, .. } => Some(stem.clone()),
                PassageOrigin::Standing { .. } => None,
            })
            .collect();
        assert!(
            licensing.len() >= 2,
            "one licensing stem cannot be restricted by a stem family: {licensing:?}"
        );
        let dropped = licensing.iter().next().cloned().expect("plural");
        let aperture = MoveAperture::through(
            licensing
                .iter()
                .filter(|stem| **stem != dropped)
                .cloned()
                .collect::<Vec<String>>(),
        );
        let restricted = passages_under(&passages, &aperture);

        assert!(
            restricted.len() < passages.len(),
            "dropping the stem {dropped:?} removed nothing: {} of {}",
            restricted.len(),
            passages.len()
        );
        assert!(restricted.iter().any(Passage::is_derived));
        assert!(
            restricted.iter().all(|passage| match &passage.origin {
                PassageOrigin::Derived { stem, .. } => *stem != dropped,
                PassageOrigin::Standing { .. } => true,
            }),
            "the dropped stem still licenses something in the restricted population"
        );
        for (position, passage) in restricted.iter().enumerate() {
            assert_eq!(passage.id, PassageId(position as u64));
        }

        // And the circuit founded over it can name every cell, which is what the ids are for.
        let circuit = crate::conditioned_derivation::found_conditioned_circuit(
            restricted,
            CircuitAperture::STATEMENT_INCIDENT,
        )
        .expect("the circuit founds");
        assert!(
            circuit.provenance_is_total(),
            "unclaimed: {:?}",
            circuit.unclaimed
        );
    }

    /// The declared receiver family must be more than one frame, and the conduct aperture must
    /// exclude the production's own edges. Both are the declarations every later claim rests on.
    #[test]
    fn the_receiver_family_is_plural_and_the_conduct_aperture_is_the_deposits_own_edges() {
        let circuit = circuit();
        let system = declare_receivers(&circuit).expect("the aperture is one the carrier honours");
        assert!(
            system.receivers.len() >= 2,
            "one receiver is one frame and cannot audit itself"
        );

        // The frames genuinely disagree: two receivers that address every cell alike are one frame
        // wearing two names.
        let first = system.addresses(crate::receiver_exact_compression::ReceiverId(0));
        let disagreeing = (1..system.receivers.len()).filter(|index| {
            system.addresses(crate::receiver_exact_compression::ReceiverId(*index as u64)) != first
        });
        assert!(
            disagreeing.count() > 0,
            "every declared receiver returned the same addresses; the gauge acts trivially"
        );

        // The conduct aperture holds the deposit's edges and none of the production's.
        let admitted: BTreeSet<CausalCellId> = conduct_aperture(&circuit).into_iter().collect();
        assert!(!admitted.is_empty(), "no conduct step at all is not an aperture");
        for passage in circuit.passages.iter().filter(|p| p.is_derived()) {
            for cell in passage_interior(&circuit, passage) {
                assert!(
                    !admitted.contains(&cell),
                    "a cell the production founded is admitted as a conduct step"
                );
            }
        }
    }

    /// `passage_interior` must be exactly the cells the circuit's own provenance gives that passage
    /// and no other — the second frame on one quantity, and the only thing that pins **which**
    /// cells a move deposits.
    ///
    /// A version omitting one species of cell survived every other test in this file: the class
    /// those cells fall in merely stays open, and an unreached class is an ordinary return. Nothing
    /// distinguishes "the move does not reach it" from "the move was built short".
    #[test]
    fn the_interior_of_a_derived_passage_is_exactly_what_the_circuits_provenance_gives_it_alone() {
        let circuit = circuit();
        let mut alone: BTreeMap<String, BTreeSet<CausalCellId>> = BTreeMap::new();
        for cell in circuit.circuit.complex().cells().values() {
            let founding = circuit.passages_founding(cell.id);
            if let [only] = founding.as_slice() {
                alone
                    .entry(only.derivation.name.clone())
                    .or_default()
                    .insert(cell.id);
            }
        }

        let derived: Vec<&Passage> = circuit
            .passages
            .iter()
            .filter(|passage| passage.is_derived())
            .collect();
        assert!(!derived.is_empty(), "no derived passage to read");
        for passage in derived {
            let interior = passage_interior(&circuit, passage);
            assert!(
                interior.len() >= 3,
                "a passage founds a vertex, its recruitment 1-cells and its reach 1-cell; {} has {}",
                passage.derivation.name,
                interior.len()
            );
            assert_eq!(
                interior,
                alone
                    .get(&passage.derivation.name)
                    .cloned()
                    .unwrap_or_default(),
                "the interior of {} disagrees with the circuit's own provenance",
                passage.derivation.name
            );
        }
    }

    // ---------------------------------------------------------------------------------------
    // the moves

    /// A split deposits two passages that carry one bridge, and withdraws the one it replaced. A
    /// deposit withdraws nothing. An exchange does both.
    #[test]
    fn each_species_is_the_move_its_name_says_and_none_of_them_is_trivial() {
        let circuit = circuit();
        for declared in moves_the_production_made(&circuit) {
            assert!(
                !declared.substitution.is_trivial(),
                "{:?} changed nothing",
                declared.deposits
            );
            match declared.species {
                MoveSpecies::Deposit => {
                    assert!(declared.withdraws.is_empty());
                    assert_eq!(declared.deposits.len(), 1);
                    assert!(
                        declared.substitution.removed().is_empty(),
                        "a deposit withdraws no cell"
                    );
                    assert!(!declared.substitution.added().is_empty());
                }
                MoveSpecies::RecruitmentExchange => {
                    assert_eq!(declared.withdraws.len(), 1);
                    assert_eq!(declared.deposits.len(), 1);
                    assert!(!declared.substitution.removed().is_empty());
                    assert!(!declared.substitution.added().is_empty());
                }
                MoveSpecies::LemmaSplit => {
                    assert_eq!(declared.withdraws.len(), 1);
                    assert_eq!(declared.deposits.len(), 2, "one lemma by two");
                    assert!(!declared.substitution.removed().is_empty());
                    assert!(!declared.substitution.added().is_empty());
                }
            }
        }
    }

    /// Every declared move is a substitution `skein` accepts: both fillings closed, the boundary
    /// shared. A refusal here would mean the moves were read off the production wrongly, and it is
    /// checked rather than assumed because `read_and_realize` retains refusals silently.
    #[test]
    fn every_move_the_production_made_is_read_without_refusal() {
        let circuit = circuit();
        let moves = moves_the_production_made(&circuit);
        assert!(moves.len() >= 3, "{} declared", moves.len());
        let founded = read_and_realize(
            circuit.circuit.complex(),
            &substitutions(&moves),
            &contexts(&circuit),
            PivotRule::FirstNonzero,
        );
        assert!(founded.refused.is_empty(), "{:?}", founded.refused);
        assert_eq!(founded.realizers.len(), moves.len());
        for (declared, realizer) in moves.iter().zip(&founded.realizers) {
            assert_eq!(realizer.landings, declared.substitution.added());
            assert_eq!(realizer.withdrawn, declared.substitution.removed());
        }
    }

    /// The declared context family is three readings and not one counted three times. A family
    /// whose members return one remainder for every move cannot exhibit a per-context verdict at
    /// all, and `remainder()` truncating to the first would then be invisible.
    #[test]
    fn two_declared_contexts_return_different_remainders_for_the_same_move() {
        let circuit = circuit();
        let moves = moves_the_production_made(&circuit);
        let founded = read_and_realize(
            circuit.circuit.complex(),
            &substitutions(&moves),
            &contexts(&circuit),
            PivotRule::FirstNonzero,
        );
        let disagreeing = founded.realizers.iter().filter(|realizer| {
            let reading = realizer.reading.as_ref().expect("read");
            reading
                .verdicts
                .windows(2)
                .any(|pair| pair[0].remainder != pair[1].remainder)
        });
        assert!(
            disagreeing.count() > 0,
            "no move is read differently by any two declared contexts, so the family is one \
             context counted three times"
        );
    }

    // ---------------------------------------------------------------------------------------
    // the required return: what stands, what is open, and the obstruction species

    /// **The artifact.** The split family alone reaches its classes only doubled — the twin the
    /// receivers cannot separate — so those classes are supported rationally and not integrally,
    /// and the factor is returned rather than the fact of failure.
    #[test]
    fn a_lemma_split_reaches_its_classes_only_in_multiple_and_the_factor_is_returned() {
        let circuit = circuit();
        let system = declare_receivers(&circuit).expect("declared");
        let splits = split_moves(&circuit);
        assert!(!splits.is_empty(), "the fixture declared no split");

        let placed = place_moves(
            &circuit,
            &system,
            &splits,
            &contexts(&circuit),
            RealizerAdmission::EveryRead,
            PivotRule::FirstNonzero,
        );

        let doubled = placed.reached_only_in_multiple();
        assert!(
            !doubled.is_empty(),
            "no class came back reached only in multiple; the split's twins are being separated"
        );
        for class in &doubled {
            match &class.obstruction {
                MoveObstruction::ReachedOnlyInMultiple { factor, reached_by } => {
                    assert!(
                        *factor > BigInt::from(1),
                        "a factor of one is not an obstruction"
                    );
                    assert!(
                        !reached_by.is_empty(),
                        "a class reached only in multiple must name what reached it"
                    );
                    assert!(reached_by
                        .iter()
                        .all(|naming| naming.species == MoveSpecies::LemmaSplit));
                }
                MoveObstruction::NoMoveReached => panic!("filtered above"),
            }
            assert!(
                class.reading.holds_derived(),
                "the doubled class must hold a cell the production founded: {:?}",
                class.reading.cells
            );
        }
        assert!(
            !placed.torsion().is_empty(),
            "the integral-versus-rational split must be nonzero in the invariant factors"
        );
    }

    /// And it dissolves. Declaring the `Deposit` move for one member of the same bridge reaches
    /// those classes singly, the invariant factor returns to one, and they stand — so the `2` is a
    /// statement about what the moves reach and not an artifact of the reduction.
    #[test]
    fn declaring_the_deposit_of_one_member_dissolves_the_doubled_obstruction_and_is_a_founding() {
        let circuit = circuit();
        let system = declare_receivers(&circuit).expect("declared");
        let family = contexts(&circuit);

        let splits = split_moves(&circuit);
        let mut with_deposits = splits.clone();
        with_deposits.extend(deposit_moves(&circuit));

        let before = place_moves(
            &circuit,
            &system,
            &splits,
            &family,
            RealizerAdmission::EveryRead,
            PivotRule::FirstNonzero,
        );
        let after = place_moves(
            &circuit,
            &system,
            &with_deposits,
            &family,
            RealizerAdmission::EveryRead,
            PivotRule::FirstNonzero,
        );

        assert!(!before.reached_only_in_multiple().is_empty());
        assert!(
            after.reached_only_in_multiple().is_empty(),
            "reaching the class singly must remove the obstruction, not merely add to it: {:?}",
            after
                .reached_only_in_multiple()
                .iter()
                .map(|class| &class.reading.cells)
                .collect::<Vec<_>>()
        );
        assert!(after.torsion().is_empty(), "{:?}", after.torsion());
        assert!(
            after.supported.len() > before.supported.len(),
            "the dissolved classes must now stand: {} -> {}",
            before.supported.len(),
            after.supported.len()
        );

        // And the discharge is named for what it is: a move was declared that had not been.
        assert_eq!(
            discharge_substitutions(&before.placed, &after.placed),
            SubstitutionDischarge::Founded
        );
    }

    /// Relaxing the admission filter over a **fixed** declared family is a widening and never a
    /// founding. `placement::discharge` reports it as `Founded`, which is why this module never
    /// calls it.
    #[test]
    fn relaxing_the_filter_over_one_family_is_a_widening_and_not_a_founding() {
        let circuit = circuit();
        let system = declare_receivers(&circuit).expect("declared");
        let family = contexts(&circuit);
        let moves = moves_the_production_made(&circuit);

        let narrow = place_moves(
            &circuit,
            &system,
            &moves,
            &family,
            RealizerAdmission::Invisible,
            PivotRule::FirstNonzero,
        );
        let wide = place_moves(
            &circuit,
            &system,
            &moves,
            &family,
            RealizerAdmission::EveryRead,
            PivotRule::FirstNonzero,
        );

        // The material can vary the property: the two apertures admit different populations.
        assert!(
            !narrow.placed.admitted.is_empty(),
            "no move is invisible to every declared context, so the narrow aperture is empty and \
             the comparison is between a reading and nothing"
        );
        assert!(narrow.placed.admitted.len() < wide.placed.admitted.len());
        assert_eq!(
            narrow.placed.declared, wide.placed.declared,
            "one declared family, read at two apertures"
        );
        assert!(wide.placed.placement.open.len() < narrow.placed.placement.open.len());

        assert_eq!(
            discharge_substitutions(&narrow.placed, &wide.placed),
            SubstitutionDischarge::Widened
        );
        assert_eq!(
            crate::placement::discharge(&narrow.placed.placement, &wide.placed.placement),
            crate::placement::Discharge::Founded,
            "placement alone reads the widening as production, which is the convicted defect"
        );
    }

    /// A class the receivers distinguish and no declared move deposits into stays OPEN and is
    /// named, not counted. The second statement's own cells are that population.
    #[test]
    fn a_class_no_move_reaches_stays_open_and_names_the_passages_it_is_made_of() {
        let circuit = circuit();
        let system = declare_receivers(&circuit).expect("declared");
        let moves = moves_the_production_made(&circuit);
        let placed = place_moves(
            &circuit,
            &system,
            &moves,
            &contexts(&circuit),
            RealizerAdmission::EveryRead,
            PivotRule::FirstNonzero,
        );

        let unreached = placed.unreached();
        assert!(
            !unreached.is_empty(),
            "every class was paid for, so the OPEN half of the claim cannot fail here"
        );
        for class in &unreached {
            assert!(
                !class.reading.cells.is_empty(),
                "a class with no cells is not a class"
            );
            assert!(
                !class.reading.passages.is_empty(),
                "an open class must name the passages its cells came from: {:?}",
                class.reading.cells
            );
        }
        assert!(
            placed.placed.placement.support.free_obstruction() > 0,
            "and the free obstruction is exhibited"
        );
    }

    /// The production's own cells are paid for by the production's own moves, and the standing
    /// class names both. A placement that stood on the deposit's classes alone would be a reading
    /// of the terrain rather than of the production.
    #[test]
    fn a_class_the_production_founded_stands_and_names_the_move_and_the_passage_that_paid() {
        let circuit = circuit();
        let system = declare_receivers(&circuit).expect("declared");
        let mut moves = split_moves(&circuit);
        moves.extend(deposit_moves(&circuit));
        let placed = place_moves(
            &circuit,
            &system,
            &moves,
            &contexts(&circuit),
            RealizerAdmission::EveryRead,
            PivotRule::FirstNonzero,
        );

        let from_production = placed.supported_from_production();
        assert!(
            !from_production.is_empty(),
            "no standing class holds a cell the production founded"
        );
        for class in &from_production {
            assert!(!class.paid_by.is_empty(), "a standing class is never unpaid");
            for naming in &class.paid_by {
                assert!(
                    !naming.deposits.is_empty(),
                    "a move that paid must have deposited something"
                );
            }
            assert!(
                class.reading.passages.iter().any(|passage| passage.derived
                    && passage.stem.is_some()
                    && passage.brought.is_some()),
                "a derived passage names the stem that licensed it and what it brought"
            );
        }
    }

    /// **Which** move a class names, and not merely that it names one.
    ///
    /// Two claims, and they pin different things. The declared position must be a move that really
    /// deposited a cell of that class — checked against `Substitution::added()` directly, which is
    /// the frame `place` used. And the reported species, stem and passages must be the ones the move
    /// **at that position** carries: a reading that returns the right position with another move's
    /// payload points every class at the wrong substitution, and non-emptiness plus a species check
    /// are both satisfied by doing so.
    #[test]
    fn every_move_a_class_names_is_the_move_at_that_declared_position_and_it_reached_that_class() {
        let circuit = circuit();
        let system = declare_receivers(&circuit).expect("declared");
        let moves = moves_the_production_made(&circuit);

        // The material can vary the property: naming the wrong move is only detectable if the moves
        // differ from one another.
        let distinct: BTreeSet<&Vec<String>> =
            moves.iter().map(|declared| &declared.deposits).collect();
        assert!(
            distinct.len() >= 3,
            "the declared family must hold moves that differ, or naming the wrong one is invisible"
        );

        let placed = place_moves(
            &circuit,
            &system,
            &moves,
            &contexts(&circuit),
            RealizerAdmission::EveryRead,
            PivotRule::FirstNonzero,
        );
        let placement = &placed.placed.placement;

        let mut namings = 0usize;
        let mut positions = BTreeSet::new();
        let mut check = |naming: &MoveNaming, class: usize| {
            let declared = moves
                .get(naming.declared)
                .expect("a naming points at a declared move");
            let landed: BTreeSet<usize> = declared
                .substitution
                .added()
                .into_iter()
                .filter_map(|cell| class_of(placement, cell))
                .collect();
            assert!(
                landed.contains(&class),
                "move {} is named by class {class} and deposited nothing in it",
                naming.declared
            );
            assert_eq!(naming.species, declared.species);
            assert_eq!(naming.stem, declared.stem);
            assert_eq!(naming.deposits, declared.deposits);
            assert_eq!(naming.withdraws, declared.withdraws);
            namings += 1;
            positions.insert(naming.declared);
        };

        for class in &placed.supported {
            assert!(!class.paid_by.is_empty());
            for naming in &class.paid_by {
                check(naming, class.reading.class);
            }
        }
        for class in &placed.open {
            if let MoveObstruction::ReachedOnlyInMultiple { reached_by, .. } = &class.obstruction {
                for naming in reached_by {
                    check(naming, class.reading.class);
                }
            }
        }
        assert!(namings > 0, "no class named a move, so nothing was checked");
        assert!(
            positions.len() >= 3,
            "every naming pointed at the same position, so the check cannot separate them"
        );
    }

    // ---------------------------------------------------------------------------------------
    // two frames on one quantity

    /// The positive form on this move population, evaluated exactly, against an incidence rebuilt
    /// here straight off `Substitution::added()`. Two frames on one quantity, and the form is
    /// required to be nonzero on the classes the moves paid for rather than merely non-negative —
    /// `x^T (M^T M) x >= 0` is a theorem for every integer matrix and grades nothing.
    #[test]
    fn the_positive_form_agrees_with_an_incidence_rebuilt_from_the_moves_themselves() {
        let circuit = circuit();
        let system = declare_receivers(&circuit).expect("declared");
        let moves = moves_the_production_made(&circuit);
        let placed = place_moves(
            &circuit,
            &system,
            &moves,
            &contexts(&circuit),
            RealizerAdmission::EveryRead,
            PivotRule::FirstNonzero,
        );
        let placement = &placed.placed.placement;
        let extent = placement.class_extent;
        let realizations = placed
            .realizers
            .realizations_under(RealizerAdmission::EveryRead, &placement.compression.conduct);
        let form = positive_form(&incidence(&realizations, extent));

        let mut theirs = IntegerMatrix::zeros(moves.len(), extent);
        for (row, declared) in moves.iter().enumerate() {
            for cell in declared.substitution.added() {
                let class = class_of(placement, cell).expect("every cell is an item");
                let carried = theirs.at(row, class) + BigInt::from(1);
                theirs.set(row, class, carried);
            }
        }

        let mut probes: Vec<Vec<BigInt>> = vec![
            (0..extent).map(|_| BigInt::from(1)).collect(),
            (0..extent)
                .map(|index| {
                    let magnitude = (index as i64) + 2;
                    BigInt::from(if index % 2 == 0 { magnitude } else { -magnitude })
                })
                .collect(),
        ];
        for class in 0..extent {
            let mut probe = vec![BigInt::zero(); extent];
            probe[class] = BigInt::from(1);
            probes.push(probe);
        }

        let mut nonzero = 0usize;
        for probe in &probes {
            let value = quadratic_value(&form, probe);
            assert_eq!(
                value,
                squared_norm(&theirs, probe),
                "the form and the moves disagree on {probe:?}"
            );
            if !value.is_zero() {
                nonzero += 1;
            }
        }
        assert!(
            nonzero >= 3,
            "the form is zero almost everywhere, so agreement carries no evidence"
        );
    }

    /// The incidence this module hands to `supported_realizers` has the rank `place` computed, at
    /// two apertures whose ranks differ — a fixture where they did not differ would let a constant
    /// pass as agreement.
    #[test]
    fn the_incidence_has_the_rank_placement_computed_at_two_apertures_of_different_rank() {
        let circuit = circuit();
        let system = declare_receivers(&circuit).expect("declared");
        let moves = moves_the_production_made(&circuit);
        let family = contexts(&circuit);

        let mut ranks = BTreeSet::new();
        for admission in [RealizerAdmission::Invisible, RealizerAdmission::EveryRead] {
            let placed = place_moves(
                &circuit,
                &system,
                &moves,
                &family,
                admission,
                PivotRule::FirstNonzero,
            );
            let placement = &placed.placed.placement;
            let realizations = placed
                .realizers
                .realizations_under(admission, &placement.compression.conduct);
            let rank = smith_normal_form(
                &incidence(&realizations, placement.class_extent),
                PivotRule::FirstNonzero,
            )
            .rank();
            assert_eq!(rank, placement.support.supported_rank);
            ranks.insert(rank);
        }
        assert_eq!(ranks.len(), 2, "the two apertures must not have the same rank");
    }

    // ---------------------------------------------------------------------------------------
    // the zero controls, each paired with a case that is not zero

    /// Nothing declared pays for nothing, and every class stays open. The same circuit with the
    /// production's moves declared does close classes, so the zero is a property of the empty
    /// family and not of the code.
    #[test]
    fn no_declared_move_pays_for_nothing_and_the_same_circuit_does_pay_when_moves_are_declared() {
        let circuit = circuit();
        let system = declare_receivers(&circuit).expect("declared");
        let family = contexts(&circuit);

        let nothing = place_moves(
            &circuit,
            &system,
            &[],
            &family,
            RealizerAdmission::EveryRead,
            PivotRule::FirstNonzero,
        );
        assert!(nothing.supported.is_empty());
        assert!(nothing.reached_only_in_multiple().is_empty());
        assert_eq!(nothing.unreached().len(), nothing.open.len());
        assert!(!nothing.placed.placement.closed());

        let something = place_moves(
            &circuit,
            &system,
            &moves_the_production_made(&circuit),
            &family,
            RealizerAdmission::EveryRead,
            PivotRule::FirstNonzero,
        );
        assert!(
            !something.supported.is_empty(),
            "the same circuit and the same receivers must close classes once moves are declared"
        );
    }

    /// An empty context family admits nothing receiver-relative, and the same population under
    /// `EveryRead` still places — so the zero is the aperture's and not the code's.
    #[test]
    fn a_move_nobody_looked_at_is_not_invisible() {
        let circuit = circuit();
        let system = declare_receivers(&circuit).expect("declared");
        let moves = moves_the_production_made(&circuit);

        let unlooked = place_moves(
            &circuit,
            &system,
            &moves,
            &[],
            RealizerAdmission::Invisible,
            PivotRule::FirstNonzero,
        );
        assert!(unlooked.placed.admitted.is_empty());
        assert!(unlooked.supported.is_empty());

        let looked = place_moves(
            &circuit,
            &system,
            &moves,
            &contexts(&circuit),
            RealizerAdmission::Invisible,
            PivotRule::FirstNonzero,
        );
        assert!(
            !looked.placed.admitted.is_empty(),
            "declaring a context must admit something at the invisible aperture"
        );
        assert_eq!(
            discharge_substitutions(&unlooked.placed, &looked.placed),
            SubstitutionDischarge::Widened,
            "declaring a context admits a move without producing one"
        );
    }

    /// The aperture is an aperture: a stem family that admits no derived passage founds a circuit
    /// with nothing to place, and `declare_receivers` refuses rather than returning a reading of
    /// the deposit alone.
    #[test]
    fn an_aperture_that_admits_no_derived_passage_is_refused_rather_than_read() {
        let body = body();
        let passages = body.passages(&query()).expect("reads back");
        let empty = MoveAperture::through(["a stem no corpus committed".to_owned()]);
        let restricted = passages_under(&passages, &empty);
        assert!(restricted.iter().all(|passage| !passage.is_derived()));

        let circuit = crate::conditioned_derivation::found_conditioned_circuit(
            restricted,
            CircuitAperture::STATEMENT_INCIDENT,
        )
        .expect("the deposit alone still founds a circuit");
        assert_eq!(
            declare_receivers(&circuit).unwrap_err(),
            DerivationSkeinRefusal::ProductionFoundedNothing
        );
        assert!(moves_the_production_made(&circuit).is_empty());
    }
}
