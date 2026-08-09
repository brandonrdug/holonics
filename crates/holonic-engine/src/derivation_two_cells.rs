//! The 2-cells that make a derivation a proof rather than a graph, founded on elaborated meaning.
//!
//! ## The refusal this resolves, and how it is resolved
//!
//! `crate::derivation_atlas` founds **no 2-cell**, and says so at its own module documentation
//! rather than quietly: a square 2-cell over two derivations sharing two symbols *"cancels exactly
//! the grade-1 cycle"* that the same design reads as *"independent distinct routes to one result"*.
//! Those two sentences are not compatible, and that module refused to pick one silently.
//!
//! The refusal is resolved **by construction and not by choosing**, because the distinction it could
//! not make is now available. [`crate::name_elaboration`] returns the constructive meaning of a name
//! — the transitive closure of what it recruits, with the depth at which each constituent entered.
//! So:
//!
//! > Two routes to one result are **the same proof** when their elaborations agree, and **genuinely
//! > two** when they do not.
//!
//! - Where two routes' elaborations agree, the loop is **filled** with a 2-cell.
//! - Where they disagree, the hole is **left open** and the disagreement is retained as a typed
//!   obstruction ([`ElaborationDisagreement`]) naming exactly what differs.
//!
//! `β₁` after filling is therefore *the routes that are genuinely different*, and the filled
//! population is *the routes that were the same proof wearing two names*. **Both are returned, with
//! the population behind each.** A caller that wants the difference subtracts two numbers it was
//! handed; nothing here reports a delta in place of what moved.
//!
//! ## The square, and why its boundary closes
//!
//! Under a statement-founded aperture the circuit carries a recruitment 1-cell `A<-x` with boundary
//! `A - x` and a reach 1-cell `A|-S` with boundary `A - S`. For two derivation vertices `A`, `B`
//! reaching one statement `S` and sharing a recruited symbol `x`:
//!
//! ```text
//!   square(A, B, x, S) = +(A<-x) - (B<-x) - (A|-S) + (B|-S)
//!
//!   d = (A - x) - (B - x) - (A - S) + (B - S) = 0
//! ```
//!
//! One square per agreeing pair **per shared symbol**, because two squares over the same pair and
//! different symbols are independent — their difference is the quadrilateral `A—x—B—y—A` — and
//! choosing one shared symbol per pair would be a receiver coordinate promoted into the filling.
//!
//! An agreeing pair with **no** shared symbol founds no square. That is not the same as a
//! disagreement and it is not silently dropped: [`RouteFilling::agreeing_without_square`] returns
//! that population by name, because a pair whose elaborations agree and whose vertices touch no
//! common symbol closes no loop for a 2-cell to fill.
//!
//! ## Two declared criteria, because one of them is vacuous on this material
//!
//! [`AgreementCriterion::Exact`] asks that the two meanings be the same population at the same
//! depths. [`AgreementCriterion::OnOverlap`] asks only that they agree **where they meet** — every
//! constituent in both enters at the same depth, and the cycles they share are the same. The second
//! is the sheaf condition: local sections agreeing on overlaps.
//!
//! Both are run and both are reported. `CLAUDE.md` §8: *a check whose material cannot vary the
//! property under test is the same defect as a check that cannot fail.* On the deposited material
//! `Exact` fills nothing — every pair of declarations differs by at least one recruited symbol — and
//! that is reported as a vacuity of the criterion rather than repaired by loosening it. `OnOverlap`
//! separates the population, and the two criteria disagreeing on the same pairs is what makes this a
//! gauge with a non-trivial orbit rather than one reading wearing two names.
//!
//! ## Higher overlaps
//!
//! `papers/source/holonics/logic-category.typ` H.0035 carries the standing bound: *"Pairwise
//! compatibility alone may be insufficient when higher overlaps matter."* A graph `β₁` cannot see a
//! triple; a 2-complex can, and three questions are asked of every triple reaching one statement:
//!
//! - **Is the agreement relation transitive here?** `A ~ B`, `B ~ C`, `A !~ C` is the classic
//!   failure and [`TripleOverlap::is_non_transitive`] names it. `Exact` agreement is an equality and
//!   is transitive by construction; `OnOverlap` is not, and whether the deposit exhibits it is a
//!   measurement.
//! - **Does a pairwise-agreeing triple admit a joint section?** The union of the three signatures
//!   must be a function *and* must be closed under the deposit's own recruitment: a constituent in
//!   the union that recruits another constituent in the union may not stand more than one depth
//!   above it. [`JointSectionObstruction`] names which of the two failed and on what. It is computed
//!   because it is the literal question, and **it provably cannot fail under a uniform aperture** —
//!   see the theorem below, which is the finding rather than a caveat on it.
//! - **Are the three pairwise fillings independent?** For a symbol `x` all three share,
//!   `square(A,B,x) - square(A,C,x) + square(B,C,x)` has boundary zero — a grade-2 **cycle**. The
//!   three pairwise fillings are then not independent, and the redundancy is exactly `β₂`. This is
//!   the higher overlap the graph reading cannot carry, and it is verified against the complex
//!   rather than asserted from the algebra above.
//!
//! ### The theorem, because a check that cannot fail must be proved rather than reported
//!
//! `CLAUDE.md` §8: *a law that returns zero proves nothing about itself*, and *a check whose material
//! cannot vary the property under test is the same defect as a check that cannot fail.* The
//! joint-section question is exactly such a check here, and the honest return is the proof:
//!
//! > **Under one uniform elaboration aperture, three pairwise-agreeing meanings always admit a joint
//! > section.** Let `u` stand in the union at depth `d(u)`, supplied by member `M`, and let `u`
//! > recruit `v`, which stands in the union at `d(v)`. Because `M`'s walk is breadth-first from its
//! > own root and every member is elaborated to the *same* depth, `M` opened `u` unless `u` sits at
//! > `M`'s frontier — and the frontier is the deepest layer, so nothing in the union stands deeper
//! > than it. If `M` opened `u` then `v ∈ elab(M)` at depth at most `d(u) + 1`, and pairwise
//! > agreement forces `d(v)` to be that depth. If `u` sits at the frontier then `d(u)` is the
//! > aperture and `d(v) ≤ d(u)`, so `d(v) > d(u) + 1` is unreachable. A `DepthConflict` is
//! > likewise unreachable: two members carrying one constituent at two depths *is* a pairwise
//! > disagreement.
//!
//! So the H.0035 caveat does **not** bite on this gluing datum, and the reason is that a
//! shortest-passage depth is not free data — it is determined by the recruitment relation the
//! members share. What the 2-complex sees that the graph cannot is therefore not a failure of
//! pairwise compatibility but the other two items above: the **non-transitivity** of on-overlap
//! agreement, and the **dependence** of the pairwise fillings, which is `β₂`.
//!
//! ## Two implementations of the one number that matters
//!
//! `β₁` after filling is `β₁` before minus `rank(∂₂)`, and `rank(∂₂)` is computed twice from
//! disjoint material: by Smith normal form over `BigInt` in `crate::rebase_invariants`, and here by
//! **exact rational elimination in a spanning-forest fundamental-cycle basis**
//! ([`RouteFilling::independent_filling_rank`]). The second reads a spanning forest of the unfilled
//! circuit and the boundary coefficients restricted to its non-tree edges; it shares no code path
//! with the first. `CLAUDE.md` §8 asks for exactly this where an independent implementation exists.
//!
//! ## No float, no scalar governor, no truncation
//!
//! Every coefficient is a `ComparativeMultiplicity` over `BigUint`; the independent rank runs over
//! `relational_geometry::Rat`, which is `BigRational`. Nothing is ranked, scored, or thresholded: a
//! pair either agrees under a declared criterion or it does not, and the population that does not is
//! returned whole. A square population past the declared aperture is **refused by name with its
//! size** ([`TwoCellRefusal::SquarePopulationExceedsAperture`]) rather than truncated, so a reading
//! can never silently be of less material than it says.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};

use crate::algebraic::{
    CausalAlgebraicError, CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};
use crate::derivation_atlas::{
    found_circuit, CircuitAperture, Derivation, DerivationAtlasRefusal, DerivationCircuit,
    SpanningForestReading, StatementIncidence,
};
use crate::name_elaboration::{
    Elaboration, ElaborationAperture, ElaborationDeposit, ElaborationRefusal, RetainedCycle,
};
use crate::rebase_invariants::{rebase_invariants, PivotRule, RebaseInvariants};

/// When two elaborated meanings count as one meaning.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum AgreementCriterion {
    /// The same constituents at the same depths, and the same retained cycles. An equality, and
    /// therefore transitive.
    Exact,
    /// Agreement **where the two meet**: every shared constituent enters at the same depth and every
    /// shared cycle is the same cycle. The sheaf condition, and **not** transitive.
    OnOverlap,
}

impl AgreementCriterion {
    pub const DECLARED: [Self; 2] = [Self::Exact, Self::OnOverlap];

    pub const fn name(&self) -> &'static str {
        match self {
            Self::Exact => "exact",
            Self::OnOverlap => "on-overlap",
        }
    }
}

/// Everything by which two elaborated meanings differ. The retained obstruction when a loop is left
/// open.
///
/// **The two roots are excluded from the constituent comparison and carried separately.** Two routes
/// to one result have different names by hypothesis, so letting `alpha` at depth zero count as a
/// constituent `beta` lacks would make every pair of distinct names disagree and
/// [`AgreementCriterion::Exact`] vacuous for every deposit that ever existed. What is *not* dropped
/// is the case that matters: one route's root standing **inside** the other's meaning is retained in
/// [`Self::contains_other_root`] and refuses agreement under both criteria, because a proof built
/// out of another proof is not that proof.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ElaborationDisagreement {
    pub left: String,
    pub right: String,
    /// Constituents of the left meaning that the right does not carry, with the depth they entered.
    /// Neither root appears here.
    pub only_left: BTreeMap<String, usize>,
    pub only_right: BTreeMap<String, usize>,
    /// Constituents both carry at different depths: `(left depth, right depth)`.
    pub depth_disagreement: BTreeMap<String, (usize, usize)>,
    /// A compared root standing as a constituent of the other's meaning, with the depth it stands
    /// at there. One entry per direction that holds. Non-empty refuses agreement outright.
    pub contains_other_root: BTreeMap<String, usize>,
    pub cycles_only_left: Vec<RetainedCycle>,
    pub cycles_only_right: Vec<RetainedCycle>,
    /// How many constituents both meanings carry, the roots excluded. The size of the overlap the
    /// on-overlap criterion is an agreement *on*, carried so an empty overlap is visible as one
    /// rather than as agreement.
    pub shared: usize,
}

impl ElaborationDisagreement {
    /// The constituents both meanings carry.
    pub const fn overlap(&self) -> usize {
        self.shared
    }

    /// Whether the two meanings agree under a declared criterion.
    pub fn agrees(&self, criterion: AgreementCriterion) -> bool {
        let where_they_meet = self.depth_disagreement.is_empty()
            && self.contains_other_root.is_empty()
            && self.cycles_only_left.is_empty()
            && self.cycles_only_right.is_empty();
        match criterion {
            AgreementCriterion::Exact => {
                where_they_meet && self.only_left.is_empty() && self.only_right.is_empty()
            }
            AgreementCriterion::OnOverlap => where_they_meet,
        }
    }

    /// A one-line reading of what differs, for a driver that has to print it.
    pub fn render(&self) -> String {
        let mut parts: Vec<String> = Vec::new();
        for (name, depth) in &self.contains_other_root {
            parts.push(format!("{name} is a constituent at depth {depth} and a root at depth 0"));
        }
        for (name, (left, right)) in &self.depth_disagreement {
            parts.push(format!("{name} at depth {left} vs {right}"));
        }
        if !self.only_left.is_empty() {
            let mut named: Vec<String> = self
                .only_left
                .iter()
                .map(|(name, depth)| format!("{name}@{depth}"))
                .collect();
            named.sort();
            parts.push(format!("only {}: {}", self.left, named.join(" ")));
        }
        if !self.only_right.is_empty() {
            let mut named: Vec<String> = self
                .only_right
                .iter()
                .map(|(name, depth)| format!("{name}@{depth}"))
                .collect();
            named.sort();
            parts.push(format!("only {}: {}", self.right, named.join(" ")));
        }
        for cycle in self.cycles_only_left.iter().chain(&self.cycles_only_right) {
            parts.push(format!("cycle {}", cycle.members.join("~")));
        }
        if parts.is_empty() {
            "nothing".to_owned()
        } else {
            parts.join("; ")
        }
    }
}

/// Compare two elaborated meanings, retaining every way they differ.
pub fn compare(left: &Elaboration, right: &Elaboration) -> ElaborationDisagreement {
    let full_left = left.signature();
    let full_right = right.signature();
    let roots = [left.root(), right.root()];

    // One root standing inside the other's meaning. Retained before the roots are set aside,
    // because it is the one way a name difference *is* a meaning difference.
    let mut contains_other_root = BTreeMap::new();
    if let Some(depth) = full_left.get(right.root()) {
        contains_other_root.insert(right.root().to_owned(), *depth);
    }
    if let Some(depth) = full_right.get(left.root()) {
        contains_other_root.insert(left.root().to_owned(), *depth);
    }

    let left_signature: BTreeMap<&str, usize> = full_left
        .into_iter()
        .filter(|(name, _)| !roots.contains(name))
        .collect();
    let right_signature: BTreeMap<&str, usize> = full_right
        .into_iter()
        .filter(|(name, _)| !roots.contains(name))
        .collect();

    let mut only_left = BTreeMap::new();
    let mut only_right = BTreeMap::new();
    let mut depth_disagreement = BTreeMap::new();
    let mut shared = 0usize;
    for (name, depth) in &left_signature {
        match right_signature.get(name) {
            Some(other) => {
                shared += 1;
                if other != depth {
                    depth_disagreement.insert((*name).to_owned(), (*depth, *other));
                }
            }
            None => {
                only_left.insert((*name).to_owned(), *depth);
            }
        }
    }
    for (name, depth) in &right_signature {
        if !left_signature.contains_key(name) {
            only_right.insert((*name).to_owned(), *depth);
        }
    }

    let left_cycles: BTreeSet<&RetainedCycle> = left.cycles().iter().collect();
    let right_cycles: BTreeSet<&RetainedCycle> = right.cycles().iter().collect();

    ElaborationDisagreement {
        left: left.root().to_owned(),
        right: right.root().to_owned(),
        only_left,
        only_right,
        depth_disagreement,
        contains_other_root,
        cycles_only_left: left_cycles
            .difference(&right_cycles)
            .map(|cycle| (*cycle).clone())
            .collect(),
        cycles_only_right: right_cycles
            .difference(&left_cycles)
            .map(|cycle| (*cycle).clone())
            .collect(),
        shared,
    }
}

/// One founded square: two routes to one statement, held together at one shared symbol.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FilledSquare {
    pub statement: String,
    pub left: String,
    pub right: String,
    pub shared_symbol: String,
    pub cell: CausalCellId,
    pub name: String,
}

/// One pair of routes to one statement whose meanings agree and that shares no recruited symbol.
///
/// No loop exists for a 2-cell to fill. Returned by name because "agreeing" and "filled" are not the
/// same population, and a reading that reported only the second would lose this one.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AgreeingWithoutSquare {
    pub statement: String,
    pub left: String,
    pub right: String,
}

/// One loop the criterion refused to fill, with the disagreement that refused it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HeldOpenRoute {
    pub statement: String,
    pub left: String,
    pub right: String,
    /// The symbols a square could have been founded over had the meanings agreed. Retained, so the
    /// hole is exhibited with the filling it refused rather than only with its own name.
    pub refused_symbols: BTreeSet<String>,
    pub disagreement: ElaborationDisagreement,
}

/// Why three pairwise-agreeing meanings admit no joint section.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum JointSectionObstruction {
    /// A constituent stands at two different depths across the triple. Pairwise agreement cannot
    /// see it when the two disagreeing members do not both carry it.
    DepthConflict {
        constituent: String,
        depths: BTreeMap<String, usize>,
    },
    /// The union is a function and is not closed under the deposit's own recruitment: `recruiter`
    /// names `recruited`, both are in the union, and `recruited` stands more than one depth below.
    NotRecruitmentClosed {
        recruiter: String,
        recruiter_depth: usize,
        recruited: String,
        recruited_depth: usize,
    },
}

/// Three routes to one statement, read as a higher overlap.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TripleOverlap {
    pub statement: String,
    pub members: [String; 3],
    /// How many of the three pairs agree under the declared criterion.
    pub agreeing_pairs: usize,
    /// The union of the three signatures admits no joint section. `None` when all three pairs agree
    /// and a joint section exists, and `None` when the triple is not pairwise agreeing at all —
    /// [`Self::pairwise_agrees`] separates those.
    pub joint_obstruction: Option<JointSectionObstruction>,
    /// Symbols all three members recruit. Each founds three squares whose alternating sum is a
    /// grade-2 cycle.
    pub common_symbols: BTreeSet<String>,
    /// Symbols at which the three pairwise fillings were verified dependent against the complex:
    /// `square(A,B,x) - square(A,C,x) + square(B,C,x)` has boundary zero.
    pub verified_relations: BTreeSet<String>,
}

impl TripleOverlap {
    pub const fn pairwise_agrees(&self) -> bool {
        self.agreeing_pairs == 3
    }

    /// Exactly two of the three pairs agree. The agreement relation is not transitive here, and this
    /// is the failure `logic-category.typ` H.0035 bounds the sheaf axiom with.
    pub const fn is_non_transitive(&self) -> bool {
        self.agreeing_pairs == 2
    }
}

/// A derivation circuit with its route loops filled where the meanings agree.
#[derive(Clone, Debug)]
pub struct RouteFilling {
    aperture: CircuitAperture,
    criterion: AgreementCriterion,
    elaboration_aperture: ElaborationAperture,
    circuit: DerivationCircuit,
    filled: GradedCausalComplex,
    squares: Vec<FilledSquare>,
    held_open: Vec<HeldOpenRoute>,
    agreeing_without_square: Vec<AgreeingWithoutSquare>,
    triples: Vec<TripleOverlap>,
    pairs_examined: usize,
    triples_examined: usize,
}

impl RouteFilling {
    pub const fn aperture(&self) -> CircuitAperture {
        self.aperture
    }

    pub const fn criterion(&self) -> AgreementCriterion {
        self.criterion
    }

    pub const fn elaboration_aperture(&self) -> ElaborationAperture {
        self.elaboration_aperture
    }

    /// The circuit before any filling. Its complex carries no 2-cell.
    pub const fn circuit(&self) -> &DerivationCircuit {
        &self.circuit
    }

    /// The same complex with the 2-cells founded.
    pub const fn filled_complex(&self) -> &GradedCausalComplex {
        &self.filled
    }

    /// **The routes that were the same proof wearing two names**, one entry per shared symbol.
    pub fn squares(&self) -> &[FilledSquare] {
        &self.squares
    }

    /// **The routes that are genuinely different**, each with what differs.
    pub fn held_open(&self) -> &[HeldOpenRoute] {
        &self.held_open
    }

    /// Agreeing pairs that share no recruited symbol, so no loop existed to fill.
    pub fn agreeing_without_square(&self) -> &[AgreeingWithoutSquare] {
        &self.agreeing_without_square
    }

    pub fn triples(&self) -> &[TripleOverlap] {
        &self.triples
    }

    /// How many route pairs the criterion was asked about.
    pub const fn pairs_examined(&self) -> usize {
        self.pairs_examined
    }

    pub const fn triples_examined(&self) -> usize {
        self.triples_examined
    }

    /// The distinct pairs a square was founded over. A pair may carry several squares.
    pub fn filled_pairs(&self) -> BTreeSet<(&str, &str, &str)> {
        self.squares
            .iter()
            .map(|square| {
                (
                    square.statement.as_str(),
                    square.left.as_str(),
                    square.right.as_str(),
                )
            })
            .collect()
    }

    pub fn held_open_pairs(&self) -> BTreeSet<(&str, &str, &str)> {
        self.held_open
            .iter()
            .map(|held| {
                (
                    held.statement.as_str(),
                    held.left.as_str(),
                    held.right.as_str(),
                )
            })
            .collect()
    }

    /// The invariants of the unfilled circuit.
    pub fn invariants_before(
        &self,
        rule: PivotRule,
    ) -> Result<RebaseInvariants, CausalAlgebraicError> {
        rebase_invariants(self.circuit.complex(), rule)
    }

    /// The invariants with the 2-cells founded.
    pub fn invariants_after(
        &self,
        rule: PivotRule,
    ) -> Result<RebaseInvariants, CausalAlgebraicError> {
        rebase_invariants(&self.filled, rule)
    }

    /// The spanning-forest reading of the unfilled circuit, which is the atlas's own second frame.
    pub fn spanning_forest(&self) -> SpanningForestReading {
        self.circuit.spanning_forest_reading()
    }

    /// **The second implementation of `rank(∂₂)`.**
    ///
    /// A spanning forest of the unfilled circuit gives a fundamental-cycle basis indexed by the
    /// non-tree 1-cells, and the coordinate of a 1-cycle on the fundamental cycle of a non-tree edge
    /// is simply its coefficient there — because the difference is a cycle supported on tree edges,
    /// and a forest carries none. Each square's boundary is restricted to those coordinates and the
    /// rank is taken by exact rational elimination.
    ///
    /// Shares no code path with `rebase_invariants`: union-find and `Rat` here, integer Smith normal
    /// form there. `β₁` after filling must equal `β₁` before minus this number.
    pub fn independent_filling_rank(&self) -> usize {
        let basis = fundamental_cycle_basis(self.circuit.complex());
        if basis.non_tree.is_empty() {
            return 0;
        }
        let mut columns: Vec<Vec<Rat>> = Vec::with_capacity(self.squares.len());
        for square in &self.squares {
            let Ok(cell) = self.filled.cell(square.cell) else {
                continue;
            };
            let column: Vec<Rat> = basis
                .non_tree
                .iter()
                .map(|edge| Rat::from(cell.boundary.coefficient(*edge).difference()))
                .collect();
            columns.push(column);
        }
        exact_rational_rank(&columns, basis.non_tree.len())
    }

}

/// Every derivation vertex to the symbols it recruits, read from the circuit's own 1-cells rather
/// than from the derivations, so a square can only be founded over a recruitment the complex
/// actually carries.
///
/// Taken once. Reading it per pair would make the pair walk quadratic in the edge population for no
/// reason, which is the kind of cost `CLAUDE.md` §8 asks to be stated rather than discovered.
fn recruited_by_vertex(circuit: &DerivationCircuit) -> BTreeMap<String, BTreeSet<String>> {
    let mut carried: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (vertex, symbol) in circuit.recruitments().keys() {
        carried
            .entry(vertex.clone())
            .or_default()
            .insert(symbol.clone());
    }
    carried
}

fn shared_between(
    recruited: &BTreeMap<String, BTreeSet<String>>,
    left: &str,
    right: &str,
) -> BTreeSet<String> {
    let (Some(a), Some(b)) = (recruited.get(left), recruited.get(right)) else {
        return BTreeSet::new();
    };
    a.intersection(b).cloned().collect()
}

/// Found a circuit and fill its route loops wherever the elaborated meanings agree.
///
/// `square_aperture` and `triple_aperture` are declared populations, not filters: exceeding either
/// **refuses the whole reading with the size it would have founded**, so a return can never be of
/// less material than the aperture it prints.
pub fn fill_routes(
    derivations: &[Derivation],
    aperture: CircuitAperture,
    criterion: AgreementCriterion,
    elaboration_aperture: ElaborationAperture,
    square_aperture: usize,
    triple_aperture: usize,
) -> Result<RouteFilling, TwoCellRefusal> {
    if aperture.statements != StatementIncidence::Founded {
        return Err(TwoCellRefusal::StatementsWithheld);
    }
    let circuit = found_circuit(derivations, aperture)?;
    let deposit = ElaborationDeposit::read(derivations);

    // Elaborate every derivation vertex once. The vertex keys `found_circuit` uses and the keys
    // `ElaborationDeposit` resolves are the same strings under both declared identities.
    let mut meanings: BTreeMap<String, Elaboration> = BTreeMap::new();
    for reaching in circuit.reaching_vertices().values() {
        for vertex in reaching {
            if meanings.contains_key(*vertex) {
                continue;
            }
            meanings.insert(
                (*vertex).to_owned(),
                deposit.elaborate(vertex, elaboration_aperture)?,
            );
        }
    }

    // Classify every pair of vertices reaching one statement.
    let mut agreeing: Vec<(String, String, String, BTreeSet<String>)> = Vec::new();
    let mut held_open: Vec<HeldOpenRoute> = Vec::new();
    let mut agreeing_without_square: Vec<AgreeingWithoutSquare> = Vec::new();
    let mut agreement: BTreeMap<(String, String, String), bool> = BTreeMap::new();
    let mut pairs_examined = 0usize;

    let reaching_by_statement: BTreeMap<String, Vec<String>> = circuit
        .reaching_vertices()
        .into_iter()
        .map(|(statement, reaching)| {
            (
                statement.to_owned(),
                reaching.into_iter().map(str::to_owned).collect(),
            )
        })
        .collect();

    let recruited = recruited_by_vertex(&circuit);

    for (statement, reaching) in &reaching_by_statement {
        for left in 0..reaching.len() {
            for right in (left + 1)..reaching.len() {
                pairs_examined += 1;
                let (a, b) = (&reaching[left], &reaching[right]);
                let disagreement = compare(&meanings[a], &meanings[b]);
                let agrees = disagreement.agrees(criterion);
                agreement.insert((statement.clone(), a.clone(), b.clone()), agrees);
                let shared = shared_between(&recruited, a, b);
                if agrees {
                    if shared.is_empty() {
                        agreeing_without_square.push(AgreeingWithoutSquare {
                            statement: statement.clone(),
                            left: a.clone(),
                            right: b.clone(),
                        });
                    } else {
                        agreeing.push((statement.clone(), a.clone(), b.clone(), shared));
                    }
                } else {
                    held_open.push(HeldOpenRoute {
                        statement: statement.clone(),
                        left: a.clone(),
                        right: b.clone(),
                        refused_symbols: shared,
                        disagreement,
                    });
                }
            }
        }
    }

    let square_population: usize = agreeing.iter().map(|(_, _, _, shared)| shared.len()).sum();
    if square_population > square_aperture {
        return Err(TwoCellRefusal::SquarePopulationExceedsAperture {
            squares: square_population,
            declared: square_aperture,
        });
    }

    let mut filled = circuit.complex().clone();
    let mut squares: Vec<FilledSquare> = Vec::new();
    let mut by_key: BTreeMap<(String, String, String, String), CausalCellId> = BTreeMap::new();
    for (statement, a, b, shared) in &agreeing {
        for symbol in shared {
            let (Some(left_recruits), Some(right_recruits), Some(left_reaches), Some(right_reaches)) = (
                circuit.recruitments().get(&(a.clone(), symbol.clone())),
                circuit.recruitments().get(&(b.clone(), symbol.clone())),
                circuit.reaches().get(&(a.clone(), statement.clone())),
                circuit.reaches().get(&(b.clone(), statement.clone())),
            ) else {
                continue;
            };
            let mut boundary = CausalChain::default();
            boundary.add_term(*left_recruits, ComparativeMultiplicity::positive(1u32));
            boundary.add_term(*right_recruits, ComparativeMultiplicity::negative(1u32));
            boundary.add_term(*left_reaches, ComparativeMultiplicity::negative(1u32));
            boundary.add_term(*right_reaches, ComparativeMultiplicity::positive(1u32));

            // The square is caused by exactly the passages that founded its four sides.
            let mut caused = BTreeSet::new();
            for side in [left_recruits, right_recruits, left_reaches, right_reaches] {
                caused.extend(filled.cell(*side)?.source_events.iter().copied());
            }

            let name = format!("[{a}={b}]@{symbol}|-{statement}");
            let cell = filled.found_cell(name.clone(), caused, 2, boundary)?;
            by_key.insert(
                (
                    statement.clone(),
                    a.clone(),
                    b.clone(),
                    symbol.clone(),
                ),
                cell,
            );
            squares.push(FilledSquare {
                statement: statement.clone(),
                left: a.clone(),
                right: b.clone(),
                shared_symbol: symbol.clone(),
                cell,
                name,
            });
        }
    }

    // ------------------------------------------------------------------ the higher overlaps
    let triples_available: usize = reaching_by_statement
        .values()
        .map(|reaching| {
            let population = reaching.len();
            population.saturating_sub(2) * population.saturating_sub(1) * population / 6
        })
        .sum();
    if triples_available > triple_aperture {
        return Err(TwoCellRefusal::TriplePopulationExceedsAperture {
            triples: triples_available,
            declared: triple_aperture,
        });
    }

    let mut triples: Vec<TripleOverlap> = Vec::new();
    let mut triples_examined = 0usize;
    for (statement, reaching) in &reaching_by_statement {
        for first in 0..reaching.len() {
            for second in (first + 1)..reaching.len() {
                for third in (second + 1)..reaching.len() {
                    triples_examined += 1;
                    let members = [
                        reaching[first].clone(),
                        reaching[second].clone(),
                        reaching[third].clone(),
                    ];
                    let pairs = [
                        (members[0].clone(), members[1].clone()),
                        (members[0].clone(), members[2].clone()),
                        (members[1].clone(), members[2].clone()),
                    ];
                    let agreeing_pairs = pairs
                        .iter()
                        .filter(|(a, b)| {
                            agreement
                                .get(&(statement.clone(), a.clone(), b.clone()))
                                .copied()
                                .unwrap_or(false)
                        })
                        .count();

                    let joint_obstruction = if agreeing_pairs == 3 {
                        joint_section_obstruction(&deposit, &members, &meanings)
                    } else {
                        None
                    };

                    let common_symbols: BTreeSet<String> = {
                        let mut carried: Option<BTreeSet<String>> = None;
                        for member in &members {
                            let here = recruited.get(member).cloned().unwrap_or_default();
                            carried = Some(match carried {
                                None => here,
                                Some(before) => before.intersection(&here).cloned().collect(),
                            });
                        }
                        carried.unwrap_or_default()
                    };

                    // The relation, verified against the complex rather than asserted.
                    let mut verified_relations = BTreeSet::new();
                    for symbol in &common_symbols {
                        let sides = [
                            by_key.get(&(
                                statement.clone(),
                                members[0].clone(),
                                members[1].clone(),
                                symbol.clone(),
                            )),
                            by_key.get(&(
                                statement.clone(),
                                members[0].clone(),
                                members[2].clone(),
                                symbol.clone(),
                            )),
                            by_key.get(&(
                                statement.clone(),
                                members[1].clone(),
                                members[2].clone(),
                                symbol.clone(),
                            )),
                        ];
                        let (Some(ab), Some(ac), Some(bc)) = (sides[0], sides[1], sides[2]) else {
                            continue;
                        };
                        let mut chain = CausalChain::default();
                        chain.add_term(*ab, ComparativeMultiplicity::positive(1u32));
                        chain.add_term(*ac, ComparativeMultiplicity::negative(1u32));
                        chain.add_term(*bc, ComparativeMultiplicity::positive(1u32));
                        if filled.boundary_of_chain(&chain)?.difference_is_zero() {
                            verified_relations.insert(symbol.clone());
                        }
                    }

                    triples.push(TripleOverlap {
                        statement: statement.clone(),
                        members,
                        agreeing_pairs,
                        joint_obstruction,
                        common_symbols,
                        verified_relations,
                    });
                }
            }
        }
    }

    Ok(RouteFilling {
        aperture,
        criterion,
        elaboration_aperture,
        circuit,
        filled,
        squares,
        held_open,
        agreeing_without_square,
        triples,
        pairs_examined,
        triples_examined,
    })
}

/// Whether the union of a triple's signatures is a section: one depth per constituent, closed under
/// the deposit's own recruitment.
fn joint_section_obstruction(
    deposit: &ElaborationDeposit,
    members: &[String; 3],
    meanings: &BTreeMap<String, Elaboration>,
) -> Option<JointSectionObstruction> {
    let mut union: BTreeMap<String, usize> = BTreeMap::new();
    let mut carried_by: BTreeMap<String, BTreeMap<String, usize>> = BTreeMap::new();
    for member in members {
        let Some(meaning) = meanings.get(member) else {
            continue;
        };
        for (name, depth) in meaning.signature() {
            carried_by
                .entry(name.to_owned())
                .or_default()
                .insert(member.clone(), depth);
            match union.get(name) {
                Some(before) if *before != depth => {
                    return Some(JointSectionObstruction::DepthConflict {
                        constituent: name.to_owned(),
                        depths: carried_by[name].clone(),
                    });
                }
                _ => {
                    union.insert(name.to_owned(), depth);
                }
            }
        }
    }

    for (name, depth) in &union {
        let Some(recruited) = deposit.recruitment(name) else {
            continue;
        };
        for symbol in recruited.keys() {
            let Some(other) = union.get(symbol) else {
                continue;
            };
            if *other > depth + 1 {
                return Some(JointSectionObstruction::NotRecruitmentClosed {
                    recruiter: name.clone(),
                    recruiter_depth: *depth,
                    recruited: symbol.clone(),
                    recruited_depth: *other,
                });
            }
        }
    }
    None
}

// -------------------------------------------------------------------------------------------------
// The independent rank: a spanning forest and exact rational elimination
// -------------------------------------------------------------------------------------------------

/// A fundamental-cycle basis of a complex's grade-1 cells, indexed by its non-tree edges.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FundamentalCycleBasis {
    pub tree: Vec<CausalCellId>,
    pub non_tree: Vec<CausalCellId>,
}

/// Split the grade-1 cells into a spanning forest and the edges that close a cycle.
///
/// Reads `boundary.support()` and never a coefficient, exactly as
/// `derivation_atlas::DerivationCircuit::spanning_forest_reading` does, so the split is
/// orientation-blind and the two cannot drift.
pub fn fundamental_cycle_basis(complex: &GradedCausalComplex) -> FundamentalCycleBasis {
    let vertices: Vec<CausalCellId> = complex
        .cells()
        .values()
        .filter(|cell| cell.grade == 0)
        .map(|cell| cell.id)
        .collect();
    let index: BTreeMap<CausalCellId, usize> = vertices
        .iter()
        .enumerate()
        .map(|(slot, id)| (*id, slot))
        .collect();
    let mut parent: Vec<usize> = (0..vertices.len()).collect();

    fn root(parent: &mut [usize], mut node: usize) -> usize {
        while parent[node] != node {
            parent[node] = parent[parent[node]];
            node = parent[node];
        }
        node
    }

    let mut tree = Vec::new();
    let mut non_tree = Vec::new();
    for cell in complex.cells().values() {
        if cell.grade != 1 {
            continue;
        }
        let endpoints: Vec<usize> = cell
            .boundary
            .support()
            .into_iter()
            .filter_map(|endpoint| index.get(&endpoint).copied())
            .collect();
        let mut joined = false;
        if endpoints.len() == 2 {
            let left = root(&mut parent, endpoints[0]);
            let right = root(&mut parent, endpoints[1]);
            if left != right {
                parent[right] = left;
                joined = true;
            }
        }
        if joined {
            tree.push(cell.id);
        } else {
            non_tree.push(cell.id);
        }
    }
    FundamentalCycleBasis { tree, non_tree }
}

/// The rank of a population of exact rational column vectors, by elimination.
///
/// Nothing is compared for magnitude to choose a pivot: the first nonzero coordinate of the reduced
/// column is taken, which is a position and not a size.
pub fn exact_rational_rank(columns: &[Vec<Rat>], height: usize) -> usize {
    let mut pivots: Vec<(usize, Vec<Rat>)> = Vec::new();
    for column in columns {
        let mut reduced = column.clone();
        if reduced.len() != height {
            reduced.resize(height, Rat::zero());
        }
        for (at, basis) in &pivots {
            if reduced[*at].is_zero() {
                continue;
            }
            let factor = reduced[*at].clone();
            for slot in 0..height {
                if basis[slot].is_zero() {
                    continue;
                }
                reduced[slot] = &reduced[slot] - &(&factor * &basis[slot]);
            }
        }
        let Some(at) = (0..height).find(|slot| !reduced[*slot].is_zero()) else {
            continue;
        };
        let scale = reduced[at].clone();
        for value in &mut reduced {
            if !value.is_zero() {
                *value = &*value / &scale;
            }
        }
        pivots.push((at, reduced));
    }
    pivots.len()
}

/// The grade-1 Betti number a reading carries, or zero when the grade is absent.
pub fn betti_at(invariants: &RebaseInvariants, grade: u32) -> usize {
    invariants
        .grades
        .iter()
        .find(|carried| carried.grade == grade)
        .map_or(0, |carried| carried.betti)
}

/// The torsion a reading carries at one grade.
pub fn torsion_at(invariants: &RebaseInvariants, grade: u32) -> Vec<BigInt> {
    invariants
        .grades
        .iter()
        .find(|carried| carried.grade == grade)
        .map(|carried| carried.torsion.clone())
        .unwrap_or_default()
}

/// Whether a torsion population carries anything above one.
pub fn torsion_is_nontrivial(torsion: &[BigInt]) -> bool {
    torsion.iter().any(|factor| factor.abs() > BigInt::from(1))
}

/// Why a filling was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TwoCellRefusal {
    /// A statement-blind aperture founds no reach 1-cell, so the square has no two sides to close
    /// on and "two routes to one result" is not a question the reading can ask.
    StatementsWithheld,
    /// The declared square aperture was exceeded. The population is named rather than truncated.
    SquarePopulationExceedsAperture { squares: usize, declared: usize },
    /// The declared triple aperture was exceeded.
    TriplePopulationExceedsAperture { triples: usize, declared: usize },
    Elaboration(ElaborationRefusal),
    Atlas(DerivationAtlasRefusal),
    Algebra(CausalAlgebraicError),
}

impl std::fmt::Display for TwoCellRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::StatementsWithheld => write!(
                formatter,
                "a statement-blind aperture founds no reach 1-cell, so no route square has two \
                 sides to close on"
            ),
            Self::SquarePopulationExceedsAperture { squares, declared } => write!(
                formatter,
                "the agreeing pairs would found {squares} squares and the declared aperture is \
                 {declared}; refused rather than truncated"
            ),
            Self::TriplePopulationExceedsAperture { triples, declared } => write!(
                formatter,
                "the statements carry {triples} triples and the declared aperture is {declared}; \
                 refused rather than truncated"
            ),
            Self::Elaboration(refusal) => write!(formatter, "{refusal}"),
            Self::Atlas(refusal) => write!(formatter, "{refusal}"),
            Self::Algebra(error) => write!(formatter, "{error}"),
        }
    }
}

impl std::error::Error for TwoCellRefusal {}

impl From<ElaborationRefusal> for TwoCellRefusal {
    fn from(refusal: ElaborationRefusal) -> Self {
        Self::Elaboration(refusal)
    }
}

impl From<DerivationAtlasRefusal> for TwoCellRefusal {
    fn from(refusal: DerivationAtlasRefusal) -> Self {
        Self::Atlas(refusal)
    }
}

impl From<CausalAlgebraicError> for TwoCellRefusal {
    fn from(error: CausalAlgebraicError) -> Self {
        Self::Algebra(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::derivation_atlas::read_derivation;

    const SQUARES: usize = 100_000;
    const TRIPLES: usize = 100_000;

    fn derivation(name: &str, statement: &str, recruited: &[(&str, u32)]) -> Derivation {
        Derivation {
            name: name.to_owned(),
            statement: statement.to_owned(),
            recruited: recruited
                .iter()
                .map(|(symbol, count)| ((*symbol).to_owned(), *count))
                .collect(),
        }
    }

    fn fill(
        derivations: &[Derivation],
        criterion: AgreementCriterion,
    ) -> RouteFilling {
        fill_routes(
            derivations,
            CircuitAperture::STATEMENT_INCIDENT,
            criterion,
            ElaborationAperture::Exhausted,
            SQUARES,
            TRIPLES,
        )
        .expect("the aperture admits this population")
    }

    /// Two declarations reaching one statement with identical recruitment. One proof, two names.
    fn identical_routes() -> Vec<Derivation> {
        vec![
            derivation("alpha", "S", &[("shared", 1), ("also", 1)]),
            derivation("beta", "S", &[("shared", 1), ("also", 1)]),
        ]
    }

    /// The same pair with one private symbol each. The meanings agree where they meet and are not
    /// the same population.
    fn overlapping_routes() -> Vec<Derivation> {
        vec![
            derivation("alpha", "S", &[("shared", 1), ("only_alpha", 1)]),
            derivation("beta", "S", &[("shared", 1), ("only_beta", 1)]),
        ]
    }

    /// One declaration whose meaning contains the other's root. They are not the same proof under
    /// either criterion, and the disagreement is a depth.
    fn nested_routes() -> Vec<Derivation> {
        vec![
            derivation("outer", "S", &[("inner", 1), ("shared", 1)]),
            derivation("inner", "S", &[("shared", 1)]),
        ]
    }

    // ------------------------------------------------------------------------ the two criteria

    #[test]
    fn identical_meanings_fill_the_loop_under_both_criteria() {
        for criterion in AgreementCriterion::DECLARED {
            let filling = fill(&identical_routes(), criterion);
            assert!(filling.held_open().is_empty(), "{criterion:?}");
            // Two shared symbols, so two squares over the one pair.
            assert_eq!(filling.squares().len(), 2, "{criterion:?}");
            assert_eq!(filling.filled_pairs().len(), 1, "{criterion:?}");
        }
    }

    #[test]
    fn a_private_constituent_holds_the_loop_open_under_exact_and_fills_it_on_overlap() {
        let exact = fill(&overlapping_routes(), AgreementCriterion::Exact);
        assert_eq!(exact.squares().len(), 0);
        assert_eq!(exact.held_open().len(), 1);
        let held = &exact.held_open()[0];
        assert_eq!(held.disagreement.only_left.keys().collect::<Vec<_>>(), vec!["only_alpha"]);
        assert_eq!(held.disagreement.only_right.keys().collect::<Vec<_>>(), vec!["only_beta"]);
        assert!(held.disagreement.depth_disagreement.is_empty());
        // The square it refused is named, not merely absent.
        assert_eq!(held.refused_symbols, BTreeSet::from(["shared".to_owned()]));

        let overlap = fill(&overlapping_routes(), AgreementCriterion::OnOverlap);
        assert_eq!(overlap.held_open().len(), 0);
        assert_eq!(overlap.squares().len(), 1);
        assert_eq!(overlap.squares()[0].shared_symbol, "shared");
    }

    #[test]
    fn a_meaning_that_contains_the_other_root_refuses_agreement_under_both_criteria() {
        for criterion in AgreementCriterion::DECLARED {
            let filling = fill(&nested_routes(), criterion);
            assert_eq!(filling.squares().len(), 0, "{criterion:?}");
            assert_eq!(filling.held_open().len(), 1, "{criterion:?}");
            let held = &filling.held_open()[0];
            assert_eq!(
                held.disagreement.contains_other_root,
                BTreeMap::from([("inner".to_owned(), 1usize)]),
                "{criterion:?}"
            );
        }
    }

    #[test]
    fn two_names_for_one_meaning_are_not_made_to_differ_by_being_two_names() {
        // The whole reason the roots are set aside: `alpha` and `beta` are different strings and
        // that is the hypothesis, not a finding. A comparison that counted it would make `Exact`
        // vacuous for every deposit.
        let disagreement = {
            let population = identical_routes();
            let deposit = ElaborationDeposit::read(&population);
            compare(
                &deposit
                    .elaborate("alpha", ElaborationAperture::Exhausted)
                    .expect("declared"),
                &deposit
                    .elaborate("beta", ElaborationAperture::Exhausted)
                    .expect("declared"),
            )
        };
        assert!(disagreement.only_left.is_empty(), "{disagreement:?}");
        assert!(disagreement.only_right.is_empty(), "{disagreement:?}");
        assert!(disagreement.contains_other_root.is_empty());
        assert_eq!(disagreement.overlap(), 2);
        assert!(disagreement.agrees(AgreementCriterion::Exact));
    }

    #[test]
    fn agreeing_routes_that_share_no_symbol_found_no_square_and_are_returned_by_name() {
        // Identical meanings would need identical recruitment, so the only way to agree with an
        // empty overlap is the on-overlap criterion over disjoint recruitment.
        let population = vec![
            derivation("alpha", "S", &[("only_alpha", 1)]),
            derivation("beta", "S", &[("only_beta", 1)]),
        ];
        let filling = fill(&population, AgreementCriterion::OnOverlap);
        assert!(filling.squares().is_empty());
        assert!(filling.held_open().is_empty());
        assert_eq!(filling.agreeing_without_square().len(), 1);
        assert_eq!(filling.agreeing_without_square()[0].left, "alpha");
    }

    // ---------------------------------------------------------------------------- the homology

    #[test]
    fn filling_lowers_betti_one_and_both_populations_are_returned_beside_the_two_numbers() {
        let filling = fill(&identical_routes(), AgreementCriterion::Exact);
        let before = filling.invariants_before(PivotRule::FirstNonzero).expect("reads");
        let after = filling.invariants_after(PivotRule::FirstNonzero).expect("reads");
        // alpha, beta, shared, also, |- S  == 5 vertices; 4 recruitments + 2 reaches == 6 edges.
        assert_eq!(betti_at(&before, 1), 2);
        assert_eq!(betti_at(&after, 1), 0);
        // And the filled population is the evidence for the move, not the difference of two numbers.
        assert_eq!(filling.squares().len(), 2);
        assert!(filling.held_open().is_empty());
    }

    #[test]
    fn the_independent_rank_agrees_with_the_smith_normal_form_on_every_declared_criterion() {
        for population in [identical_routes(), overlapping_routes(), nested_routes()] {
            for criterion in AgreementCriterion::DECLARED {
                let filling = fill(&population, criterion);
                let before = filling.invariants_before(PivotRule::FirstNonzero).expect("reads");
                let after = filling.invariants_after(PivotRule::FirstNonzero).expect("reads");
                let moved = betti_at(&before, 1) - betti_at(&after, 1);
                assert_eq!(
                    moved,
                    filling.independent_filling_rank(),
                    "{criterion:?} on {} squares",
                    filling.squares().len()
                );
            }
        }
    }

    #[test]
    fn the_spanning_forest_and_the_smith_normal_form_agree_on_betti_one_before_filling() {
        let filling = fill(&overlapping_routes(), AgreementCriterion::OnOverlap);
        let before = filling.invariants_before(PivotRule::FirstNonzero).expect("reads");
        assert_eq!(betti_at(&before, 1), filling.spanning_forest().betti_1());
    }

    #[test]
    fn a_statement_blind_aperture_is_refused_rather_than_filled_with_nothing() {
        assert_eq!(
            fill_routes(
                &identical_routes(),
                CircuitAperture::DEPOSITED_READER,
                AgreementCriterion::Exact,
                ElaborationAperture::Exhausted,
                SQUARES,
                TRIPLES,
            )
            .unwrap_err(),
            TwoCellRefusal::StatementsWithheld
        );
    }

    #[test]
    fn a_square_population_past_the_declared_aperture_is_refused_with_its_size() {
        assert_eq!(
            fill_routes(
                &identical_routes(),
                CircuitAperture::STATEMENT_INCIDENT,
                AgreementCriterion::Exact,
                ElaborationAperture::Exhausted,
                1,
                TRIPLES,
            )
            .unwrap_err(),
            TwoCellRefusal::SquarePopulationExceedsAperture {
                squares: 2,
                declared: 1,
            }
        );
    }

    // ------------------------------------------------------------------------- higher overlaps

    /// Three declarations reaching one statement, all with identical recruitment.
    fn three_identical_routes() -> Vec<Derivation> {
        vec![
            derivation("alpha", "S", &[("shared", 1)]),
            derivation("beta", "S", &[("shared", 1)]),
            derivation("gamma", "S", &[("shared", 1)]),
        ]
    }

    #[test]
    fn three_pairwise_fillings_over_one_common_symbol_are_dependent_and_the_relation_is_verified() {
        let filling = fill(&three_identical_routes(), AgreementCriterion::Exact);
        assert_eq!(filling.squares().len(), 3);
        assert_eq!(filling.triples().len(), 1);
        let triple = &filling.triples()[0];
        assert!(triple.pairwise_agrees());
        assert_eq!(triple.common_symbols, BTreeSet::from(["shared".to_owned()]));
        assert_eq!(triple.verified_relations, triple.common_symbols);

        // The dependency is grade-2 homology, and a graph betti-1 cannot carry it.
        let after = filling.invariants_after(PivotRule::FirstNonzero).expect("reads");
        assert_eq!(betti_at(&after, 2), 1);
        // Two of the three squares already killed everything the third could.
        let before = filling.invariants_before(PivotRule::FirstNonzero).expect("reads");
        assert_eq!(betti_at(&before, 1) - betti_at(&after, 1), 2);
        assert_eq!(filling.independent_filling_rank(), 2);
    }

    /// **The non-transitive triple, on constructed material.** `alpha` and `beta` overlap only on
    /// `p`; `beta` and `gamma` only on `q`; `alpha` and `gamma` meet on `r`, which `alpha` reaches
    /// directly and `gamma` reaches through `bridge`. So two pairs agree on overlap and the third
    /// does not, and the agreement relation is not transitive.
    fn non_transitive_triple() -> Vec<Derivation> {
        vec![
            derivation("alpha", "S", &[("p", 1), ("r", 1)]),
            derivation("beta", "S", &[("p", 1), ("q", 1)]),
            derivation("gamma", "S", &[("q", 1), ("bridge", 1)]),
            derivation("bridge", "T", &[("r", 1)]),
        ]
    }

    #[test]
    fn a_pairwise_agreement_that_is_not_transitive_is_found_and_named_as_a_triple() {
        let filling = fill(&non_transitive_triple(), AgreementCriterion::OnOverlap);
        let triple = filling
            .triples()
            .iter()
            .find(|triple| triple.members.contains(&"alpha".to_owned()))
            .expect("the triple reaching S");
        assert_eq!(triple.agreeing_pairs, 2, "{:?}", triple);
        assert!(triple.is_non_transitive());
        assert!(!triple.pairwise_agrees());

        // And the pair that broke it names the depth it broke on: `r` at one from alpha, two from
        // gamma through `bridge`.
        let held = filling
            .held_open()
            .iter()
            .find(|held| held.left == "alpha" && held.right == "gamma")
            .expect("the disagreeing pair");
        assert_eq!(
            held.disagreement.depth_disagreement.get("r"),
            Some(&(1usize, 2usize))
        );
    }

    /// **The material built to break the joint section, which cannot.** `alpha` reaches `late`
    /// through `opener`; `gamma` reaches it through a two-step chain, so the two would place it at
    /// depths two and three. That is exactly the shape a `NotRecruitmentClosed` obstruction needs —
    /// and the pair `(alpha, gamma)` sees the conflict itself, so the triple never becomes pairwise
    /// agreeing. This is the theorem in the module documentation, exercised on material chosen to
    /// falsify it.
    fn material_built_to_break_the_joint_section() -> Vec<Derivation> {
        vec![
            derivation("alpha", "S", &[("opener", 1)]),
            derivation("beta", "S", &[("quiet", 1)]),
            derivation("gamma", "S", &[("chain", 1)]),
            derivation("chain", "T", &[("second", 1)]),
            derivation("second", "U", &[("late", 1)]),
            derivation("opener", "V", &[("late", 1)]),
        ]
    }

    #[test]
    fn a_depth_conflict_a_triple_would_carry_is_already_a_pairwise_disagreement() {
        let population = material_built_to_break_the_joint_section();
        let filling = fill(&population, AgreementCriterion::OnOverlap);
        let triple = filling
            .triples()
            .iter()
            .find(|triple| triple.statement == "S")
            .expect("the triple reaching S");

        // The conflict the triple was built to hide is visible to the pair that carries it.
        assert!(!triple.pairwise_agrees(), "{triple:?}");
        let held = filling
            .held_open()
            .iter()
            .find(|held| held.left == "alpha" && held.right == "gamma")
            .expect("the pair carrying `late` at two depths");
        assert_eq!(
            held.disagreement.depth_disagreement.get("late"),
            Some(&(2usize, 3usize))
        );

        // And so no pairwise-agreeing triple anywhere in this population lacks a joint section.
        for triple in filling.triples() {
            if triple.pairwise_agrees() {
                assert_eq!(triple.joint_obstruction, None, "{triple:?}");
            }
        }
    }

    #[test]
    fn no_pairwise_agreeing_triple_in_any_declared_fixture_lacks_a_joint_section() {
        // The theorem, run against every fixture this module carries and both criteria. It is
        // stated as a proof in the module documentation; this is what would catch the proof being
        // wrong.
        let populations = [
            three_identical_routes(),
            non_transitive_triple(),
            material_built_to_break_the_joint_section(),
        ];
        let mut pairwise_agreeing_triples = 0usize;
        for population in populations {
            for criterion in AgreementCriterion::DECLARED {
                let filling = fill(&population, criterion);
                for triple in filling.triples() {
                    if triple.pairwise_agrees() {
                        pairwise_agreeing_triples += 1;
                        assert_eq!(triple.joint_obstruction, None, "{criterion:?} {triple:?}");
                    }
                }
            }
        }
        // And the check saw material: a run in which no triple ever agreed pairwise would have
        // proved nothing about itself.
        assert!(pairwise_agreeing_triples > 0);
    }

    // ------------------------------------------------------------------------ deposited material

    /// `standing/output/lean-kernel-witness/carrier_transport-00000.lean`, verbatim.
    const WITNESS: &str = "namespace Soma\ndef exactCarrier (P : Prop) : Prop := P\nvariable (P : Prop)\ntheorem carrier_transport (h : P) : exactCarrier P := h\nend Soma\n";

    /// `standing/output/agentic-research-kernel/formal_carry-00000.lean`, verbatim. A **different
    /// declaration** carrying the **same normalized statement**.
    const RESEARCH: &str = "namespace Soma\ndef exactCarrier (P : Prop) : Prop := P\nvariable (P : Prop)\ntheorem formal_carry (h : P) : exactCarrier P := by\n  assumption\nend Soma\n";

    /// `standing/output/lean-proof-production/carrier-transport-00016.lean`, verbatim. It names
    /// `formal_carry`, which is what puts one declaration inside the other's meaning.
    const PRODUCTION: &str = "import KernelWitness\nnamespace Soma\ntheorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by\n  rw [formal_carry]\n  assumption\nend Soma\n";

    #[test]
    fn on_deposited_material_the_two_routes_to_one_statement_hold_their_loop_open() {
        let population = vec![
            read_derivation(WITNESS).expect("declares"),
            read_derivation(RESEARCH).expect("declares"),
            read_derivation(PRODUCTION).expect("declares"),
        ];
        // `carrier_transport` and `formal_carry` both reach `(h : P) : exactCarrier P`, and the
        // production artifact puts `formal_carry` inside `carrier_transport`'s meaning at depth one
        // while it is its own root at depth zero.
        let filling = fill(&population, AgreementCriterion::OnOverlap);
        let held = filling
            .held_open()
            .iter()
            .find(|held| held.statement == "(h : P) : exactCarrier P")
            .expect("the two routes to that statement");
        assert_eq!(held.left, "carrier_transport");
        assert_eq!(held.right, "formal_carry");
        assert_eq!(
            held.disagreement.contains_other_root,
            BTreeMap::from([("formal_carry".to_owned(), 1usize)])
        );
        assert!(!held.refused_symbols.is_empty());
        // And it is genuinely elaboration that refused it: the two share recruited symbols, so a
        // reading that filled every loop it could would have filled this one.
        assert!(held.disagreement.overlap() > 0);
    }
}
