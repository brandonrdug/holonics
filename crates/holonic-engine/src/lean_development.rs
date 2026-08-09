//! A human-written formal development, read at the grain of its own declarations.
//!
//! [`crate::derivation_atlas::read_derivation`] reads **one artifact as one declaration**, and on
//! the material it was built for — the machine's generated proof candidates, one `theorem` per
//! file — that is exact. Pointed at a development a person wrote, it is an organ used past its
//! declared aperture, which `CLAUDE.md` §8 convicts *"even when it appears to return"*. It does
//! appear to return. Run against `soma/formal` it reads 13 files, emits 11 derivations named by
//! whichever `theorem` happened to be **last** in each file, hands each of them the whole file's
//! tokens as its recruitment, and reports **zero** recruited-and-declared names — a deposit in which
//! nothing can be opened, from material carrying 80 declared-to-declared recruitment edges.
//!
//! That number was the evidence behind a wall.
//! `research/records/2026-08-09_FOUR_RELATIONS_SEPARATE_THE_ATOM_AND_EACH_REFUTED_ITSELF_FIRST.md`
//! §7 closed with *"exactly one recruited identifier in 103 artifacts is declared… a **material**
//! constraint rather than a construction one."* The material was in the tree. The instrument could
//! not resolve it, and an instrument's blindness reported as a property of the world is the failure
//! `papers/source/synopsis/AUDIT.md:49-68` names.
//!
//! ## The three resolutions, and each is a separate defect
//!
//! 1. **Every top-level declaration is its own derivation.** All twelve
//!    [`crate::derivation_atlas::DECLARATION_FORMERS`] found, not only `theorem`. The existing
//!    reader already carries that list and uses it *only* to suppress the token after a former,
//!    never to open a declaration — so `def crossRatio` binds the name out of the recruitment
//!    population without ever entering the declared population, and `crossRatio` returns an **atom
//!    in the same file that defines it**. Every object a theorem is about was an atom by
//!    construction.
//!
//! 2. **Comment text is not recruitment, and what was dropped is returned.** Doc comments in a
//!    real development are English. Read as recruitment they deposit `An`, `At`, `Consequently`,
//!    `Different`, `Every`, `For`, `If`, `It`, `No` into the multiset — measured, not supposed —
//!    and two theorems then "co-present" `Every`, which is the exact species of tautology
//!    [`crate::collocation`] caught in its own null-bind (`Prop` sits in 101 of 103 regions, so
//!    anything lands inside it whatever the pairing). The population is **returned** as
//!    [`DevelopmentReading::commentary`] rather than silently discarded, because a reading that
//!    drops material without exhibiting it cannot be audited.
//!
//! 3. **File preamble is file-scope, not per-declaration recruitment.** `import`, `open`,
//!    `variable`, `universe`, `set_option`, `attribute` are how a file is *situated*; charging
//!    `Mathlib.Tactic.Ring` to every theorem in the file manufactures a symbol co-present in
//!    100% of that file's declarations, which is the same tautology one level up. Returned as
//!    [`DevelopmentReading::preamble`].
//!
//! A fourth follows from the third and closes a defect the existing reader convicted **and then
//! only half-repaired**. Its own documentation records that reading `end Soma` as a second naming of
//! `Soma` *"made the only nonzero torsion in the entire deposit be the `end` keyword — a
//! receiver-visible coordinate of the file layout promoted into a homological invariant"*. It skips
//! `end` lines and still charges `namespace Soma` as a recruitment of `Soma`, which is the identical
//! coordinate arriving through the other half of the same construct. Scoping tokens are returned as
//! [`DevelopmentReading::scoping`] and recruited by nothing.
//!
//! ## The aperture is declared, so that using it wrongly is detectable
//!
//! [`DeclarationGrain`] is the point of this module as much as the parsing is.
//! [`DeclarationGrain::OneArtifactOneDeclaration`] reproduces the historical aperture **and reports
//! every top-level former it did not open** as [`DevelopmentReading::unopened`]. That is the defect
//! above made visible: the old reader absorbed 55 declarations in silence and returned a plausible
//! answer. This one returns the same answer and hands back the 55.
//!
//! ## What is joined on, and the ambiguity that is returned rather than resolved
//!
//! A declaration is retained with the namespace path it was written under, but **the join is on the
//! short name as the source writes it** — inside `namespace Soma`, a body writes `congestion`, not
//! `Soma.congestion`, so qualifying the declaration while leaving the recruitment unqualified would
//! break every edge the material actually carries. Where two top-level declarations in one
//! development share a short name under different namespaces, that is a real ambiguity of the
//! material and is returned as [`DevelopmentReading::ambiguous_short_names`]. It is not resolved by
//! fiat: `OPEN` may not be closed by choosing.
//!
//! ## Position, and the sub-illicium
//!
//! **Depth is a chart index, not a distance.** `FORMULA.md` §XVI: *"the moving origin grown to full
//! rank, emanated by each relating and receiving the next infall — **`frame(n+1)` is the emanation
//! of the relating in `frame(n)`**."* And `soma/body/src/manifold.rs`: *"depth 0 is the word grain;
//! **a completion at depth k is an arrival at depth k+1 — the same node, the same verb** … the
//! illicium is depth-recursive; the hourglass nests."*
//!
//! Two consequences are implemented here and one is not.
//!
//! **Every name carries a [`NamePosition`], read from the material's grammar.** Inside a binder
//! group the names before the `:` are *founded* and the type after it is *recruited*, so
//! `(hz : ∀ n, descendantCapacity capacity incident n ≠ 0)` founds `hz` and recruits
//! `descendantCapacity`. That rule removes **five of six** measured contaminants — `hc`, `hcong`,
//! `hm`, `hn`, `hz` — with no authored list of names. The sixth, `hnm`, comes from `by_cases hnm :`
//! and leaves only because `by_cases` is in [`BINDING_TACTICS`]; stating "one rule removes all six"
//! overclaimed and is corrected here. The head of a tactic step is
//! [`NamePosition::Tactic`] and is **returned beside** the terms rather than deleted, because a
//! route's tactic choice is real production — the generated deposit carries its whole plurality
//! there. [`ConductGrain`] is the declared aperture over the two.
//!
//! **A proof body's binding steps are its own declarations, one grain down** — [`ProofStep`].
//! `have hcap : … := by …` founds an object the next step recruits, which is a leader *inside* one
//! declaration: each step changes the material the next step reads. [`DeclaredForm::internal_arrivals`]
//! returns those, and [`DeclaredForm::internal_depth`] the longest chain. The flat reading charged
//! the whole body to the theorem as a depth-one star, so the declaration's own depth was zero by
//! construction.
//!
//! **Not implemented, and named so it is not mistaken for done:** the walk over these arrivals does
//! not yet *rebase*. [`crate::name_elaboration`] reads the same global recruitment map at every
//! depth, so its jet never moves — dead reckoning, which is exactly what W9's living boundary rules
//! out — and a constituent reached at two depths is merged onto one vertex although two depths are
//! two frames. Splitting that vertex and depositing the disagreement as holonomy through
//! [`crate::temper`]/[`crate::derivation_integral`] is the remaining construction.
//!
//! ## Declared bounds
//!
//! - **Top level only.** A declaration is a former at column zero. Structure fields, `where` blocks,
//!   `let rec`, and declarations nested inside a `section` body at an indent are not opened. A
//!   deeper grain is a different aperture and would need its own control.
//! - **Strings are not tracked.** A `--` inside a string literal is read as a comment opener. The
//!   present material contains no such literal; material that did would need the lexer to carry
//!   string state, which is a change to what the reading means.
//! - **The binding-tactic vocabulary is [`BINDING_TACTICS`]**, which is Lean's and not a judgement
//!   about which names matter. A binding tactic absent from it has its pattern read as terms, and
//!   [`DevelopmentReading::single_occurrence_terms`] is the distributional instrument that exhibits
//!   the residue.
//! - **A step head is a line the previous line did not demand.** A tactic-mode line whose head is
//!   genuinely a term, after a predecessor not ending in [`DEMANDS_CONTINUATION`], is read as a
//!   tactic; [`DevelopmentReading::tactic_position_declared`] exhibits that residue.
//! - **The statement is the header up to `:=` or the end of the header**, normalized to single
//!   spaces, exactly as the existing reader normalizes it, so the two apertures produce comparable
//!   statement text on material where both apply.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::derivation_atlas::{Derivation, CODEC_KEYWORDS, DECLARATION_FORMERS};

/// Lines that situate a file rather than found anything in it.
///
/// Their tokens are returned as [`DevelopmentReading::preamble`] and charged to no declaration.
pub const PREAMBLE_FORMS: [&str; 6] = [
    "attribute",
    "import",
    "open",
    "set_option",
    "universe",
    "variable",
];

/// What one artifact is taken to carry.
///
/// Declared rather than assumed, because the two answers are each exact on their own material and
/// the wrong one returns a plausible reading instead of an error.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum DeclarationGrain {
    /// One artifact declares one theorem — the machine's own generated deposit. Every later
    /// top-level former in the same text is reported unopened rather than absorbed.
    OneArtifactOneDeclaration,
    /// Every top-level declaration is its own derivation — a development a person wrote.
    EveryTopLevelDeclaration,
}

/// A top-level declaration the aperture did not open.
///
/// Under [`DeclarationGrain::OneArtifactOneDeclaration`] this population is the historical reader's
/// silent loss, made returnable.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct UnopenedDeclaration {
    /// The former that opened it: `theorem`, `def`, `structure`, …
    pub former: String,
    /// The name it founds, as written.
    pub name: String,
    /// One-based line in the text.
    pub line: usize,
}

/// One founded step of a proof body — **the sub-illicium**.
///
/// `soma/body/src/manifold.rs`, W9 · THE LIVING BOUNDARY: *"the sub-illicium — the atom-grain
/// traversal given the SAME live law (sub-stance, sub-groove), so the walk FEELS the standing
/// terrain (the tire on the road) instead of dead reckoning. **Its completions are THE FOLDS — the
/// cohered segments, found never listed — handed up as the word grain's arrivals.**"* And the
/// carrier law it implements: *"**a completion at depth k is an arrival at depth k+1 — the same
/// node, the same verb.**"*
///
/// `have hcap : 0 ≤ descendantCapacity … := by …` founds an object; the next step recruits it. That
/// is a leader **inside one declaration** — each step changes the material the next step reads —
/// and the flat reading charged the whole body to the theorem as a depth-one star.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofStep {
    /// The binding tactic that founds it: `have`, `obtain`, `set`, …
    pub former: String,
    /// Which single tactic founded it. `rintro ⟨c, ⟨b, hab, hbc⟩, hcd⟩` founds five names in **one
    /// act**, so they share a cohort and none of them arrives at another: they are simultaneous, and
    /// reading their token order as a causal chain promotes source layout into an invariant.
    pub cohort: usize,
    /// The `·` focus block this step was founded inside, as the stack of marker columns. A name
    /// founded in one focus block is **not in scope** in its sibling; Lean's goal scopes are
    /// disjoint and an arrival across them is a leak.
    pub focus: Vec<(usize, usize)>,
    /// The name it founds. A destructuring pattern founds several; each becomes its own step
    /// sharing one statement and one recruitment, because the material founds them together.
    pub binder: String,
    /// The step's own statement, between the binder and its `:=`, normalized to single spaces.
    /// Empty when the step carries no ascription.
    pub statement: String,
    /// Terms this step named, its own sub-body included.
    pub recruited: BTreeMap<String, u32>,
    /// Indentation of the step's head, in columns. The body's own grain.
    pub column: usize,
    /// One-based line in the file.
    pub line: usize,
}

/// One top-level declaration, with the namespace it was written under retained as lineage.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeclaredForm {
    /// The former that opened it.
    pub former: String,
    /// The name as the source writes it, which is also what a body in the same namespace recruits.
    pub name: String,
    /// The enclosing `namespace`/`section` path at the point of declaration, outermost first.
    pub namespace_path: Vec<String>,
    /// The header up to `:=`, normalized to single spaces.
    pub statement: String,
    /// Every symbol named in **term position**, with the exact number of times it named it.
    /// What the declaration is *about*.
    pub recruited: BTreeMap<String, u32>,
    /// Every symbol named in **tactic position** — the leading identifier of a proof step. How the
    /// declaration was *conducted*. Returned beside the terms and never merged into them, because
    /// a route's tactic choice is real production and a tactic is not a mathematical object.
    pub tactics: BTreeMap<String, u32>,
    /// Names this declaration's own text founds: binder-group names and binding-tactic patterns.
    /// Recruitment of nothing, returned so the exclusion is auditable.
    pub local_bindings: BTreeMap<String, u32>,
    /// The proof body's own founded steps, in source order. The sub-illicium.
    pub steps: Vec<ProofStep>,
    /// One-based line the former sits on.
    pub line: usize,
}

/// Which populations a [`DeclaredForm`] contributes to a [`Derivation`].
///
/// Declared at the point of use rather than at the reading, because the two answers are each
/// correct for a different question and neither is a default. The machine's generated deposit
/// carries its route plurality **in its tactic choice** — `assumption` against `exact` against
/// `simpa` — so a reading of that production must take [`ConductGrain::TermsAndTactics`]; a reading
/// of what a development is *about* must take [`ConductGrain::TermsOnly`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ConductGrain {
    /// Term position only.
    TermsOnly,
    /// Term and tactic position, summed — the historical reading's population minus the local
    /// bindings it could not see.
    TermsAndTactics,
}

impl DeclaredForm {
    /// The fully qualified name, for provenance. **Not** the join key — see the module note.
    pub fn qualified(&self) -> String {
        if self.namespace_path.is_empty() {
            return self.name.clone();
        }
        format!("{}.{}", self.namespace_path.join("."), self.name)
    }

    /// This declaration as the atlas's carrier, at a declared conduct grain.
    pub fn derivation(&self, grain: ConductGrain) -> Derivation {
        let mut recruited = self.recruited.clone();
        if grain == ConductGrain::TermsAndTactics {
            for (name, count) in &self.tactics {
                let slot = recruited.entry(name.clone()).or_insert(0u32);
                *slot = slot.saturating_add(*count);
            }
        }
        Derivation {
            name: self.name.clone(),
            statement: self.statement.clone(),
            recruited,
        }
    }

    /// The proof body's internal arrivals: a step recruiting a name an **earlier** step founded.
    ///
    /// Returned as `(from_step, to_step)` **indices into [`Self::steps`]**, never as names. A name
    /// is not an identity here: Lean shadows, and `· rintro ⟨b', hab', rfl⟩` beside `· intro hab`
    /// founds two different objects in one body. Indexing by step keeps them apart, and the
    /// most recent founding of a name is the one a later step arrives at — which is the scope rule
    /// the material itself obeys.
    pub fn internal_arrivals(&self) -> Vec<(usize, usize)> {
        let mut latest: BTreeMap<&str, usize> = BTreeMap::new();
        let mut arrivals = Vec::new();
        for (index, step) in self.steps.iter().enumerate() {
            for (name, earlier) in &latest {
                if !step.recruited.contains_key(*name) {
                    continue;
                }
                let from = &self.steps[*earlier];
                // Simultaneous founding is not an arrival.
                if from.cohort == step.cohort {
                    continue;
                }
                // A name founded in a sibling focus block is out of scope here.
                if !step.focus.starts_with(&from.focus) {
                    continue;
                }
                arrivals.push((*earlier, index));
            }
            latest.insert(step.binder.as_str(), index);
        }
        arrivals
    }

    /// The longest chain of internal arrivals, as step indices in order. The declaration's own
    /// depth — the leader inside it — invisible to any reading that charges the body flat.
    pub fn internal_depth(&self) -> Vec<usize> {
        let arrivals = self.internal_arrivals();
        let mut longest: Vec<Vec<usize>> = Vec::with_capacity(self.steps.len());
        let mut best: Vec<usize> = Vec::new();
        for index in 0..self.steps.len() {
            let mut carried: Vec<usize> = vec![index];
            for (from, to) in &arrivals {
                if *to != index {
                    continue;
                }
                let prefix = &longest[*from];
                if prefix.len() + 1 > carried.len() {
                    carried = prefix.clone();
                    carried.push(index);
                }
            }
            if carried.len() > best.len() {
                best = carried.clone();
            }
            longest.push(carried);
        }
        best
    }

    /// [`Self::internal_depth`] as the binders it passes through, each with the line it was founded
    /// on so a shadowed name is still distinguishable in the return.
    pub fn internal_depth_named(&self) -> Vec<String> {
        self.internal_depth()
            .into_iter()
            .map(|index| {
                let step = &self.steps[index];
                format!("{}@{}", step.binder, step.line)
            })
            .collect()
    }
}

/// One development text, read at a declared grain, with everything the reading set aside.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DevelopmentReading {
    /// The grain this reading was taken at.
    pub grain: DeclarationGrain,
    /// The declarations opened, in source order.
    pub declarations: Vec<DeclaredForm>,
    /// Top-level formers the grain did not open.
    pub unopened: Vec<UnopenedDeclaration>,
    /// Tokens occurring only inside comments, with counts. Returned, never silently dropped.
    pub commentary: BTreeMap<String, u32>,
    /// Tokens on file-scope preamble lines, with counts.
    pub preamble: BTreeMap<String, u32>,
    /// Tokens naming a `namespace`/`section` scope, with counts. File layout, never recruitment —
    /// see the module note on the half-repaired `end Soma` defect.
    pub scoping: BTreeMap<String, u32>,
    /// Short names declared more than once at top level, with the namespace path of each.
    pub ambiguous_short_names: BTreeMap<String, Vec<Vec<String>>>,
}

impl DevelopmentReading {
    /// The opened declarations as the atlas's carrier, at a declared conduct grain.
    pub fn derivations(&self, grain: ConductGrain) -> Vec<Derivation> {
        self.declarations
            .iter()
            .map(|form| form.derivation(grain))
            .collect()
    }

    /// Dot projections whose last segment is declared here: candidate edges the reading cannot
    /// certify without the receiver's type. Returned `OPEN`, never joined. See [`resolve_projection`].
    pub fn open_projections(&self) -> BTreeMap<&str, BTreeSet<(&str, &str)>> {
        let declared = self.declared_names();
        let mut found: BTreeMap<&str, BTreeSet<(&str, &str)>> = BTreeMap::new();
        for form in &self.declarations {
            for symbol in form.recruited.keys() {
                if declared.contains(symbol.as_str()) {
                    continue;
                }
                let Some(tail) = symbol.rsplit('.').next() else {
                    continue;
                };
                if tail == symbol || tail == form.name || !declared.contains(tail) {
                    continue;
                }
                found
                    .entry(form.name.as_str())
                    .or_default()
                    .insert((symbol.as_str(), tail));
            }
        }
        found
    }

    /// **A declared name the position rule sent to `local_bindings`.**
    ///
    /// The dual of [`Self::tactic_position_declared`], and it did not exist: position provably
    /// deletes an edge when a declared name lands here, and nothing looked. `fun (x : Carrier) => …`
    /// founds `Carrier` as a binder because the lambda rule takes everything before the arrow.
    pub fn binding_position_declared(&self) -> BTreeMap<&str, Vec<&str>> {
        let declared = self.declared_names();
        let mut found: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        for form in &self.declarations {
            for name in form.local_bindings.keys() {
                if declared.contains(name.as_str()) {
                    found.entry(name.as_str()).or_default().push(&form.name);
                }
            }
        }
        found
    }

    /// **First bounding instrument on the position rule, and it is structural.**
    ///
    /// A name in tactic position that the development *declares* is a name the step-head rule
    /// probably misread — a term continuation whose predecessor did not end in
    /// [`DEMANDS_CONTINUATION`]. Returned with the declarations that put it there, never silently
    /// re-assigned: re-assigning would make the rule unfalsifiable.
    pub fn tactic_position_declared(&self) -> BTreeMap<&str, Vec<&str>> {
        let declared = self.declared_names();
        let mut found: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        for form in &self.declarations {
            for name in form.tactics.keys() {
                if declared.contains(name.as_str()) {
                    found.entry(name.as_str()).or_default().push(&form.name);
                }
            }
        }
        found
    }

    /// **Second bounding instrument, and it is distributional — it shares nothing with the first.**
    ///
    /// A genuine mathematical recruitment is either declared here or arrives from the environment
    /// and recurs across declarations. **A proof-local name occurs in exactly one declaration and
    /// is declared nowhere.** So this population is the residue of the structural binder rule: what
    /// it should have caught and did not, together with the legitimately singular environment
    /// lemmas it cannot be distinguished from without a second frame.
    ///
    /// It is returned rather than subtracted. Subtracting it would delete environment recruitments
    /// used once, which is a receiver decision this reading may not make.
    pub fn single_occurrence_terms(&self) -> BTreeMap<&str, &str> {
        let declared = self.declared_names();
        let mut seen: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        for form in &self.declarations {
            for name in form.recruited.keys() {
                seen.entry(name.as_str()).or_default().push(&form.name);
            }
        }
        seen.into_iter()
            .filter(|(name, holders)| holders.len() == 1 && !declared.contains(*name))
            .map(|(name, holders)| (name, holders[0]))
            .collect()
    }

    /// Every declaration's own internal depth — its longest chain of proof-step arrivals — keyed by
    /// declaration name, omitting the declarations whose bodies found no chain at all.
    pub fn internal_depths(&self) -> BTreeMap<&str, Vec<String>> {
        self.declarations
            .iter()
            .filter_map(|form| {
                let chain = form.internal_depth_named();
                (chain.len() > 1).then(|| (form.name.as_str(), chain))
            })
            .collect()
    }

    /// Every short name this reading declares.
    pub fn declared_names(&self) -> BTreeSet<&str> {
        self.declarations
            .iter()
            .map(|form| form.name.as_str())
            .collect()
    }

    /// Declarations that recruit another declaration of the same reading, with the names recruited.
    ///
    /// This is the population the elaboration organ can open, and on the generated deposit it has
    /// exactly one member.
    pub fn declared_recruitment(&self) -> BTreeMap<&str, BTreeSet<&str>> {
        let declared = self.declared_names();
        let mut found: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
        for form in &self.declarations {
            let reached: BTreeSet<&str> = form
                .recruited
                .keys()
                .map(String::as_str)
                .filter(|symbol| *symbol != form.name && declared.contains(symbol))
                .collect();
            if !reached.is_empty() {
                found.insert(form.name.as_str(), reached);
            }
        }
        found
    }
}

/// A dot projection whose last segment this development declares — **a candidate edge, never an
/// asserted one.**
///
/// `htrace.map` resolves to the declared `Trace.map` and `(A.rebase e).Semantics` to the declared
/// `Semantics`; both are real. `(hxy i).trans` resolves to mathlib's `Eq.trans` and **not** to this
/// development's `Trace.trans`, though the spelling is identical. Telling them apart needs the
/// receiver's *type*, which an orthographic reading does not have — so the population is returned
/// `OPEN` rather than joined. `OPEN` may not be resolved by choosing.
///
/// This is why the headline edge figure is **80 asserted with 4 open**, not 84. An earlier form of
/// this module asserted all four, and the driver's own reconciliation text called
/// `semantics_rebase_iff → Semantics` a projection "to another namespace" when both sit in
/// `Soma.Holonics.SituatedAlgorithm`.
///
/// **This was the intake's largest single loss and it produced a wrong headline figure.** The term
/// population keeps what the source wrote — `A.Semantics` stays `A.Semantics`, which is provenance —
/// but the **join** must see through the projection, or `semantics_rebase_iff → Semantics` is invisible
/// and the development reads as one edge poorer than it is. The driver's own printed reconciliation
/// called that pair a projection "to another namespace"; both sit in `Soma.Holonics.SituatedAlgorithm`.

/// Join two readings of different texts into one development population.
///
/// Ambiguity is recomputed across the whole population, because a short name declared once per file
/// in two files is ambiguous in the development and in neither file.
pub fn join(readings: Vec<DevelopmentReading>) -> DevelopmentReading {
    let grain = readings
        .first()
        .map_or(DeclarationGrain::EveryTopLevelDeclaration, |first| {
            first.grain
        });
    let mut joined = DevelopmentReading {
        grain,
        declarations: Vec::new(),
        unopened: Vec::new(),
        commentary: BTreeMap::new(),
        preamble: BTreeMap::new(),
        scoping: BTreeMap::new(),
        ambiguous_short_names: BTreeMap::new(),
    };
    for reading in readings {
        joined.declarations.extend(reading.declarations);
        joined.unopened.extend(reading.unopened);
        accumulate(&mut joined.commentary, reading.commentary);
        accumulate(&mut joined.preamble, reading.preamble);
        accumulate(&mut joined.scoping, reading.scoping);
    }
    joined.ambiguous_short_names = ambiguity(&joined.declarations);
    joined
}

fn accumulate(into: &mut BTreeMap<String, u32>, from: BTreeMap<String, u32>) {
    for (token, count) in from {
        let slot = into.entry(token).or_insert(0u32);
        *slot = slot.saturating_add(count);
    }
}

fn ambiguity(declarations: &[DeclaredForm]) -> BTreeMap<String, Vec<Vec<String>>> {
    let mut by_name: BTreeMap<String, Vec<Vec<String>>> = BTreeMap::new();
    for form in declarations {
        by_name
            .entry(form.name.clone())
            .or_default()
            .push(form.namespace_path.clone());
    }
    by_name.retain(|_, paths| paths.len() > 1);
    by_name
}

// -------------------------------------------------------------------------------------------------
// The lexer
// -------------------------------------------------------------------------------------------------

/// One source line with its comment text separated from its code text.
struct SplitLine {
    code: String,
    comment: String,
}

/// Separate comment text from code, carrying nested block-comment depth across lines.
///
/// Lean's `/- … -/` nests and `/-- … -/` is a doc comment, which is the same opener. `--` runs to
/// end of line. String literals are a declared bound and are not tracked.
fn split_comments(text: &str) -> Vec<SplitLine> {
    let mut split = Vec::new();
    let mut depth = 0usize;
    for line in text.lines() {
        let mut code = String::new();
        let mut comment = String::new();
        let bytes: Vec<char> = line.chars().collect();
        let mut index = 0usize;
        while index < bytes.len() {
            let two = if index + 1 < bytes.len() {
                (bytes[index], bytes[index + 1])
            } else {
                (bytes[index], '\0')
            };
            if two == ('/', '-') {
                depth += 1;
                comment.push(' ');
                index += 2;
                continue;
            }
            if two == ('-', '/') && depth > 0 {
                depth -= 1;
                comment.push(' ');
                index += 2;
                continue;
            }
            if depth == 0 && two == ('-', '-') {
                comment.push_str(&bytes[index..].iter().collect::<String>());
                index = bytes.len();
                continue;
            }
            if depth > 0 {
                comment.push(bytes[index]);
            } else {
                code.push(bytes[index]);
            }
            index += 1;
        }
        split.push(SplitLine { code, comment });
    }
    split
}

/// The identifier tokens of one line, in source order.
///
/// [`crate::derivation_atlas`]'s rule, **widened by one character**: a token begins with a letter or
/// `_` and continues through letters, digits, `_`, `.` and `'`, so `Nat.zero` is one token,
/// `mul_div_cancel'` is one token, and `00012` is none.
///
/// **The prime is load-bearing and its absence was a defect.** Lean primes a shadowing binder —
/// `rintro ⟨b', hab', rfl⟩` beside `intro hab` in the *same* proof — and the narrower rule cut at
/// the `'`, so `hab'` and `hab` became **one name**. Two distinct objects merged onto one vertex is
/// the defect this whole module exists to remove, arriving one grain further down. `soma/formal`
/// carries twelve primed identifiers; the generated deposit carries none, so widening moves no
/// parity figure.
fn identifier_tokens(line: &str) -> impl Iterator<Item = &str> {
    line.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '.' || c == '\''))
        .filter(|token| {
            token
                .chars()
                .next()
                .is_some_and(|first| first.is_alphabetic() || first == '_')
        })
}

/// The former opening this line, if it is a top-level declaration.
///
/// Column zero, and `noncomputable`/`private`/`protected`/`partial`/`unsafe`/`@[…]` modifiers are
/// stepped over so the former under them is found.
fn top_level_former(line: &str) -> Option<(&'static str, String)> {
    if line.starts_with(char::is_whitespace) || line.is_empty() {
        return None;
    }
    let mut rest = line.trim_end();
    // A leading attribute bracket is a modifier of the declaration under it.
    if let Some(after) = rest.strip_prefix('@') {
        let Some(close) = after.find(']') else {
            return None;
        };
        rest = after[close + 1..].trim_start();
    }
    loop {
        let stepped = ["noncomputable", "private", "protected", "partial", "unsafe"]
            .iter()
            .find_map(|modifier| {
                rest.strip_prefix(modifier)
                    .filter(|after| after.starts_with(char::is_whitespace))
            });
        match stepped {
            Some(after) => rest = after.trim_start(),
            None => break,
        }
    }
    for former in DECLARATION_FORMERS {
        // `variable` and `example` found nothing joinable: `variable` is preamble, `example` is
        // anonymous. Both are declared out here rather than filtered downstream.
        if former == "variable" || former == "example" {
            continue;
        }
        if let Some(after) = rest.strip_prefix(former) {
            if !after.starts_with(char::is_whitespace) {
                continue;
            }
            let name = after
                .trim_start()
                .split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '.' || c == '\''))
                .next()
                .unwrap_or_default()
                .to_owned();
            if name.is_empty() {
                continue;
            }
            return Some((former, name));
        }
    }
    None
}

/// Is this a file-scope preamble line?
fn is_preamble(line: &str) -> bool {
    let trimmed = line.trim_start();
    PREAMBLE_FORMS.iter().any(|form| {
        trimmed
            .strip_prefix(form)
            .is_some_and(|after| after.is_empty() || after.starts_with(char::is_whitespace))
    })
}

// -------------------------------------------------------------------------------------------------
// Position — where a name stood when the reading met it
// -------------------------------------------------------------------------------------------------

/// Modifiers that may precede a top-level former. Declaration syntax, recruited by nothing —
/// measured as terms of `proportionalFlow` and `congestion` before this exclusion existed.
pub const DECLARATION_MODIFIERS: [&str; 5] =
    ["noncomputable", "private", "protected", "partial", "unsafe"];

/// Top-level commands that scope the declaration *after* them. `omit [Fintype Old] in` is neither a
/// former nor preamble, so it was appended to the PREVIOUS declaration's lines: measured, `congestion`
/// recruited `omit`.
pub const SCOPING_COMMANDS: [&str; 2] = ["omit", "attribute"];

/// Tactics that found a name, as exercised by the declared material.
///
/// `crate::derivation_atlas`'s own documentation declares the widening this list performs:
/// *"`have` is the only binding tactic this reading knows. `obtain`, `rcases`, `intro` and `set`
/// also bind names, and a corpus containing them would have those names read as recruitments. The
/// present corpus contains none; widening the rule is a change to what the reading means and
/// belongs with a test on material that exercises it."* The present corpus contains all of them,
/// so this is that widening, with that test.
///
/// **This is Lean's binder vocabulary and not an authored judgement about which names matter.** A
/// binding tactic absent from it has its pattern read as terms, and the instrument that catches
/// that is distributional rather than structural — see [`DevelopmentReading::single_occurrence_terms`].
pub const BINDING_TACTICS: [&str; 10] = [
    "by_cases", "cases", "have", "intro", "let", "obtain", "rcases", "rintro", "set", "suffices",
];

/// Where a name stood when the reading met it, from the material's own grammar.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NamePosition {
    /// Term position — what the declaration is **about**.
    Term,
    /// The leading identifier of a tactic step — how the proof was **conducted**.
    Tactic,
    /// Founded by this declaration's own text: a binder group name before its `:`, or a binding
    /// tactic's pattern. Recruitment of nothing.
    LocalBinding,
}

/// Names founded by one declaration's own text, collected before anything is recruited.
///
/// Two structural sources, both read from Lean's grammar rather than from a vocabulary:
///
/// 1. **Binder groups.** Inside `(…)`, `{…}`, `[…]` or `⦃…⦄`, the names *before* the group's `:`
///    are founded and the type *after* it is recruited. `(hz : ∀ n, descendantCapacity capacity
///    incident n ≠ 0)` founds `hz` and recruits `descendantCapacity`, `capacity`, `incident`. A
///    group with no `:` — `[Fintype Old]` — is an instance binder and founds nothing.
/// 2. **Binding tactics.** The pattern between a [`BINDING_TACTICS`] head and its `:`, `:=` or
///    `with` is founded.
///
/// The collection is per **declaration**, not per line, so a header binder used far down a proof
/// body is still recognised where it is used.
fn founded_names(lines: &[String]) -> BTreeSet<String> {
    let mut founded: BTreeSet<String> = BTreeSet::new();

    for line in lines {
        // ---------------------------------------------------------------- 1. binder groups
        let mut depth = 0usize;
        let mut group = String::new();
        for character in line.chars() {
            match character {
                '(' | '{' | '[' | '⦃' => {
                    if depth == 0 {
                        group.clear();
                    }
                    depth += 1;
                }
                ')' | '}' | ']' | '⦄' => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 {
                        if let Some((bound, _)) = group.split_once(':') {
                            // `⟨a, b⟩` destructuring and `x : T` binders read the same way here.
                            for token in identifier_tokens(bound) {
                                founded.insert(token.to_owned());
                            }
                        }
                        group.clear();
                    }
                }
                _ if depth > 0 => group.push(character),
                _ => {}
            }
        }

        // ---------------------------------------------------------------- 2. lambda binders
        // `fun m hm =>` and `fun {_ _} hstep ↦` found their names. Structural, from the arrow.
        let mut rest = line.as_str();
        while let Some(at) = rest.find("fun ") {
            let after = &rest[at + 4..];
            let head = after
                .split("=>")
                .next()
                .unwrap_or(after)
                .split('↦')
                .next()
                .unwrap_or(after);
            for token in identifier_tokens(head) {
                founded.insert(token.to_owned());
            }
            rest = after;
        }

        // ---------------------------------------------------------------- 3. binding tactics
        let trimmed = line.trim_start_matches([' ', '·', '.', '\t']).trim();
        let Some(head) = identifier_tokens(trimmed).next() else {
            continue;
        };
        if !BINDING_TACTICS.contains(&head) {
            continue;
        }
        let after = trimmed[head.len()..].trim_start();
        // The pattern runs to the first `:`, `:=` or `with`, whichever comes first.
        let pattern = split_before_with(after)
            .split(":=")
            .next()
            .unwrap_or(after);
        let pattern = pattern.split(':').next().unwrap_or(pattern);
        for token in identifier_tokens(pattern).filter(|name| *name != "with") {
            founded.insert(token.to_owned());
        }
    }

    founded
}

/// Endings that **open a block**, so the next line begins a step whatever else the ending looks
/// like. Checked before [`DEMANDS_CONTINUATION`], and the order is load-bearing.
///
/// `<;>` is here because it *sequences* tactics: the line after it is another tactic, not a term.
/// It ends with `>`, and `>` is a real binary operator that does demand a continuation, so without
/// this `simp only [swingPair, …]` under `apply RatioPresentation.ext <;>` was read as a term named
/// `simp`. Measured, not supposed.
const OPENS_BLOCK: [&str; 4] = ["by", "do", "<;>", ";"];

/// A match-alternative arrow opens its body exactly as `by` does; a **lambda** arrow does not — the
/// line after `exact Finset.sum_le_sum fun m hm =>` is the lambda's body and is a term.
///
/// The two are told apart by where the line *began*: a match alternative begins with `|`. Reading
/// every trailing `=>` as an opener put `proportionalFlow_respects_capacity` — a declared name —
/// into tactic position, which is precisely what [`DevelopmentReading::tactic_position_declared`]
/// exists to catch, and it did.
fn opens_alternative(trimmed: &str) -> bool {
    trimmed.starts_with('|') && (trimmed.ends_with("=>") || trimmed.ends_with('↦'))
}

/// Endings that demand a continuation, so the next line is **not** a new tactic step.
///
/// `have hcap_pos : 0 < descendantCapacity … :=` ends with `:=`, so `lt_of_le_of_ne hcap …` on the
/// next line is a **term** and not a tactic named `lt_of_le_of_ne`.
const DEMANDS_CONTINUATION: [&str; 23] = [
    ":=", ":", ",", "(", "[", "⟨", "=", "↔", "→", "⊢", "+", "-", "*", "/", "<", ">", "≤", "≥", "∣",
    "fun", "with", "from", "using",
];

fn demands_continuation(trimmed: &str) -> bool {
    if OPENS_BLOCK.iter().any(|opener| trimmed.ends_with(opener)) || opens_alternative(trimmed) {
        return false;
    }
    DEMANDS_CONTINUATION
        .iter()
        .any(|ending| trimmed.ends_with(ending))
}

/// The part of a tactic's argument before its `with` clause.
///
/// `induction n with` ends the line, so a ` with ` split with a trailing space never fired and the
/// binder came back as the literal string `with` — which then appeared as a **term** of `map`,
/// `trans`, `faceEq_of_carrierEq` and `finite_telescoping`.
fn split_before_with(after: &str) -> &str {
    if let Some(rest) = after.strip_suffix(" with") {
        return rest;
    }
    after.split(" with ").next().unwrap_or(after)
}

/// Strip a focus dot, a `<;>` combinator, or a case bar from the head of a tactic line.
fn strip_step_marker(trimmed: &str) -> &str {
    for marker in ["<;>", "·", "|"] {
        if let Some(rest) = trimmed.strip_prefix(marker) {
            if rest.is_empty() || rest.starts_with(char::is_whitespace) {
                return rest.trim_start();
            }
        }
    }
    trimmed
}

/// Decide position for every name of one declaration, and found its proof body's own steps.
///
/// Position is read from the material's grammar, per **declaration** rather than per line:
///
/// ```text
///   founded_names          binder-group names and binding-tactic patterns  -> LocalBinding
///   the head of a step     the first identifier of a line that opens one   -> Tactic
///   everything else                                                        -> Term
/// ```
///
/// **Declared bound.** A line opens a step when the declaration is in tactic mode and the previous
/// line did not demand a continuation. A tactic-mode line whose head is genuinely a term, and whose
/// predecessor happens not to end in [`DEMANDS_CONTINUATION`], is read as a tactic. Two instruments
/// bound that error and neither grades the other:
/// [`DevelopmentReading::tactic_position_declared`] exhibits every name in tactic position that the
/// development *declares*, and [`DevelopmentReading::single_occurrence_terms`] exhibits every term
/// occurring in exactly one declaration — the distributional signature of a proof-local name the
/// structural rule missed.
fn classify(mut form: DeclaredForm, lines: &[String]) -> DeclaredForm {
    let founded = founded_names(lines);
    let own = form.name.clone();

    let mut in_tactic = false;
    let mut previous_demands = false;
    // (column, index into form.steps) — the open steps, innermost last.
    let mut open_steps: Vec<(usize, usize)> = Vec::new();
    // One cohort per binding tactic: every name a single `rintro ⟨…⟩` founds shares it.
    let mut cohort = 0usize;
    // Inside a `calc` block every relation step is a TERM line, even when it opens with an
    // identifier: `n * ell = (n * ell * k) / k := by` was read as a tactic named `n`. The block
    // runs to the end of the declaration, which is the aperture this reading declares.
    let mut in_calc = false;
    // The open `·` focus blocks, outermost first, as (column, unique id). The id matters: two
    // SIBLING blocks sit at the same column, and a name founded in one is out of scope in the
    // other. Keying on column alone made siblings indistinguishable and leaked `rfl` across them.
    let mut focus: Vec<(usize, usize)> = Vec::new();
    let mut focus_id = 0usize;

    for (offset, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        let column = line.len() - line.trim_start().len();
        let opens_step = in_tactic && !previous_demands;
        let stripped = strip_step_marker(trimmed);

        // A step head closes every open step at or inside its own column.
        if opens_step {
            open_steps.retain(|(held, _)| *held < column);
            focus.retain(|(held, _)| *held < column);
            if trimmed.starts_with('·') {
                focus_id += 1;
                focus.push((column, focus_id));
            }
        }

        let mut head: Option<&str> = None;
        // A tactic head is the FIRST thing on its line. `(∑ n : Old, demand n)` opens a `calc`
        // relation and begins with `(`, so its first identifier `n` is a bound variable and not a
        // tactic; `_ = ∑ m : New, …` begins with Lean's placeholder and heads every later `calc`
        // step. Reading either as a head put `calc`'s own relation steps into tactic position.
        if opens_step && stripped.starts_with(char::is_alphabetic) && !in_calc {
            head = identifier_tokens(stripped).next().filter(|name| !SCOPING_COMMANDS.contains(name));
            if let Some(name) = head {
                let slot = form.tactics.entry(name.to_owned()).or_insert(0u32);
                *slot = slot.saturating_add(1);

                if BINDING_TACTICS.contains(&name) {
                    let after = stripped[name.len()..].trim_start();
                    let pattern = split_before_with(after)
                        .split(":=")
                        .next()
                        .unwrap_or(after);
                    let pattern = pattern.split(':').next().unwrap_or(pattern);
                    let statement = statement_of(after, pattern.trim());
                    // A destructuring pattern founds several names together; each becomes its own
                    // step over the one statement, because the material founds them together and
                    // choosing one would be a receiver decision this reading may not make.
                    // Single-character binders are Lean's binder convention and are dropped from
                    // every recruitment population, so a step for one could never be arrived at.
                    cohort += 1;
                    for binder in identifier_tokens(pattern).filter(|name| name.chars().count() > 1)
                    {
                        form.steps.push(ProofStep {
                            former: name.to_owned(),
                            cohort,
                            focus: focus.clone(),
                            binder: binder.to_owned(),
                            statement: statement.clone(),
                            recruited: BTreeMap::new(),
                            column,
                            line: form.line + offset,
                        });
                        open_steps.push((column, form.steps.len() - 1));
                    }
                }
            }
        }

        // Everything after the head is read for position.
        let read = match head {
            Some(name) => &stripped[name.len()..],
            None => trimmed,
        };
        // `have <bound> := <recruitment>` still binds on the left; the pattern is already founded.
        let mut founds_next = false;
        for token in identifier_tokens(read) {
            if founds_next {
                founds_next = false;
                continue;
            }
            if DECLARATION_FORMERS.contains(&token) {
                founds_next = true;
                continue;
            }
            if token.chars().count() <= 1
                || token == own
                || DECLARATION_MODIFIERS.contains(&token)
                || SCOPING_COMMANDS.contains(&token)
            {
                continue;
            }
            // The innermost open step carries the token whatever its position at the DECLARATION
            // grain, because a name local to the declaration is exactly what an earlier step
            // founded — `hcap` is not a recruitment of the environment and *is* the arrival
            // `hcap_pos` takes. A position is relative to a frame; this is the other frame.
            if let Some((_, index)) = open_steps.last() {
                if form.steps[*index].binder != token {
                    let held = form.steps[*index]
                        .recruited
                        .entry(token.to_owned())
                        .or_insert(0u32);
                    *held = held.saturating_add(1);
                }
            }
            if founded.contains(token) {
                let slot = form.local_bindings.entry(token.to_owned()).or_insert(0u32);
                *slot = slot.saturating_add(1);
                continue;
            }
            if CODEC_KEYWORDS.contains(&token) || token == "with" {
                continue;
            }
            let slot = form.recruited.entry(token.to_owned()).or_insert(0u32);
            *slot = slot.saturating_add(1);
        }

        if trimmed.contains("by") && identifier_tokens(trimmed).any(|token| token == "by") {
            in_tactic = true;
        }
        // A `calc` block alternates RELATION steps (terms) with nested `:= by` tactic blocks. The
        // flag arms at `calc` and at every `_`-headed relation step, and disarms the moment a nested
        // `by` opens — sticky to the end of the declaration would have made every tactic in the
        // block a term.
        if identifier_tokens(trimmed).next() == Some("calc") || stripped.starts_with('_') {
            in_calc = true;
        }
        // Order matters and the two are NOT exclusive: `_ ≤ ∑ m : New, capacity m := by` both opens
        // a relation step and opens its tactic block, so the disarm must run after the arm.
        if OPENS_BLOCK.iter().any(|opener| trimmed.ends_with(opener)) {
            in_calc = false;
        }
        previous_demands = demands_continuation(trimmed);
    }

    form
}

/// Read every token of one code line into a recruitment multiset, under the existing reader's
/// three exclusion rules: codec vocabulary, the token a former founds, single characters.
fn recruit_line(line: &str, into: &mut BTreeMap<String, u32>) {
    let trimmed = line.trim();
    if trimmed == "end" || trimmed.starts_with("end ") {
        return;
    }
    // `have <bound> := <recruitment>` binds on the left.
    let read = if trimmed == "have" || trimmed.starts_with("have ") {
        match trimmed.split_once(":=") {
            Some((_, right)) => right,
            None => return,
        }
    } else {
        trimmed
    };
    let mut founds_next = false;
    for token in identifier_tokens(read) {
        if founds_next {
            founds_next = false;
            continue;
        }
        if DECLARATION_FORMERS.contains(&token) {
            founds_next = true;
            continue;
        }
        if CODEC_KEYWORDS.contains(&token) {
            continue;
        }
        if token.chars().count() <= 1 {
            continue;
        }
        let slot = into.entry(token.to_owned()).or_insert(0u32);
        *slot = slot.saturating_add(1);
    }
}

/// The statement of a declaration: its header up to `:=`, normalized to single spaces.
fn statement_of(header: &str, name: &str) -> String {
    let after_name = header
        .split_once(name)
        .map_or(header, |(_, right)| right)
        .split(":=")
        .next()
        .unwrap_or_default();
    after_name.split_whitespace().collect::<Vec<_>>().join(" ")
}

// -------------------------------------------------------------------------------------------------
// The reading
// -------------------------------------------------------------------------------------------------

/// Read one development text at a declared grain.
pub fn read_development(text: &str, grain: DeclarationGrain) -> DevelopmentReading {
    let split = split_comments(text);

    let mut commentary: BTreeMap<String, u32> = BTreeMap::new();
    for line in &split {
        for token in identifier_tokens(&line.comment) {
            if token.chars().count() <= 1 {
                continue;
            }
            let slot = commentary.entry(token.to_owned()).or_insert(0u32);
            *slot = slot.saturating_add(1);
        }
    }

    let mut preamble: BTreeMap<String, u32> = BTreeMap::new();
    let mut scoping: BTreeMap<String, u32> = BTreeMap::new();
    let mut declarations: Vec<DeclaredForm> = Vec::new();
    let mut unopened: Vec<UnopenedDeclaration> = Vec::new();
    let mut namespace_path: Vec<String> = Vec::new();

    // The declaration currently accumulating: its form, whether its header is still open, the
    // header text so far, and its own lines — collected whole so that position can be decided per
    // DECLARATION rather than per line. A header binder used far down a proof body is only
    // recognisable once the whole declaration is in hand.
    let mut open: Option<(DeclaredForm, bool, String, Vec<String>)> = None;

    for (index, line) in split.iter().enumerate() {
        let code = line.code.as_str();
        let trimmed = code.trim();

        if let Some((former, name)) = top_level_former(code) {
            if let Some((form, _, _, lines)) = open.take() {
                declarations.push(classify(form, &lines));
            }
            let already = declarations.len();
            let opens = match grain {
                DeclarationGrain::EveryTopLevelDeclaration => true,
                DeclarationGrain::OneArtifactOneDeclaration => already == 0,
            };
            if !opens {
                unopened.push(UnopenedDeclaration {
                    former: former.to_owned(),
                    name,
                    line: index + 1,
                });
                continue;
            }
            let mut form = DeclaredForm {
                former: former.to_owned(),
                name: name.clone(),
                namespace_path: namespace_path.clone(),
                statement: String::new(),
                recruited: BTreeMap::new(),
                tactics: BTreeMap::new(),
                local_bindings: BTreeMap::new(),
                steps: Vec::new(),
                line: index + 1,
            };
            let header_open = !code.contains(":=");
            let mut header = statement_of(code, &name);
            if !header_open {
                form.statement = header.clone();
                header.clear();
            }
            open = Some((form, header_open, header, vec![code.to_owned()]));
            continue;
        }

        if trimmed.is_empty() {
            continue;
        }

        if is_preamble(code) {
            recruit_line(code, &mut preamble);
            continue;
        }

        if let Some(rest) = trimmed.strip_prefix("namespace ") {
            if let Some(first) = rest.split_whitespace().next() {
                let slot = scoping.entry(first.to_owned()).or_insert(0u32);
                *slot = slot.saturating_add(1);
                namespace_path.push(first.to_owned());
            }
            if let Some((form, _, _, lines)) = open.take() {
                declarations.push(classify(form, &lines));
            }
            continue;
        }
        if trimmed == "end" || trimmed.starts_with("end ") {
            if let Some(first) = trimmed.strip_prefix("end ").and_then(|rest| rest.split_whitespace().next()) {
                let slot = scoping.entry(first.to_owned()).or_insert(0u32);
                *slot = slot.saturating_add(1);
            }
            namespace_path.pop();
            if let Some((form, _, _, lines)) = open.take() {
                declarations.push(classify(form, &lines));
            }
            continue;
        }
        if trimmed.starts_with("section") {
            if let Some(first) = trimmed.strip_prefix("section ").and_then(|rest| rest.split_whitespace().next()) {
                let slot = scoping.entry(first.to_owned()).or_insert(0u32);
                *slot = slot.saturating_add(1);
            }
            continue;
        }

        if let Some((form, header_open, header, lines)) = open.as_mut() {
            if *header_open {
                let extended = format!("{header} {}", trimmed.split(":=").next().unwrap_or(""));
                *header = extended.split_whitespace().collect::<Vec<_>>().join(" ");
                if code.contains(":=") {
                    *header_open = false;
                    form.statement = header.clone();
                }
            }
            lines.push(code.to_owned());
        }
    }

    if let Some((mut form, header_open, header, lines)) = open.take() {
        if header_open {
            form.statement = header.clone();
        }
        declarations.push(classify(form, &lines));
    }

    let ambiguous_short_names = ambiguity(&declarations);
    DevelopmentReading {
        grain,
        declarations,
        unopened,
        commentary,
        preamble,
        scoping,
        ambiguous_short_names,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const DEVELOPMENT: &str = r#"import Mathlib.Tactic.Ring
open Finset

namespace Soma

/-- Consequently every receiver agrees, if it is the same face. -/
abbrev Rel (a : Type u) (b : Type v) := a -> b -> Prop

def comp {a : Type u} (r : Rel a b) (s : Rel b c) : Rel a c :=
  fun x z => exists y, r x y

-- comp is associative, which nothing here needs.
theorem comp_assoc (r : Rel a b) :
    comp (comp r s) t = comp r (comp s t) := by
  ring

end Soma
"#;

    fn reading() -> DevelopmentReading {
        read_development(DEVELOPMENT, DeclarationGrain::EveryTopLevelDeclaration)
    }

    #[test]
    fn every_top_level_declaration_is_its_own_derivation() {
        let read = reading();
        let names: Vec<&str> = read
            .declarations
            .iter()
            .map(|form| form.name.as_str())
            .collect();
        assert_eq!(names, vec!["Rel", "comp", "comp_assoc"]);
    }

    #[test]
    fn the_former_is_retained_not_only_theorem() {
        let read = reading();
        let formers: Vec<&str> = read
            .declarations
            .iter()
            .map(|form| form.former.as_str())
            .collect();
        assert_eq!(formers, vec!["abbrev", "def", "theorem"]);
    }

    #[test]
    fn a_declaration_recruits_another_declaration_of_the_same_development() {
        let read = reading();
        let chain = read.declared_recruitment();
        // `comp` names `Rel`; `comp_assoc` names `comp` and `Rel`. That is the edge species the
        // one-artifact grain cannot carry at all.
        assert!(chain["comp"].contains("Rel"));
        assert!(chain["comp_assoc"].contains("comp"));
        assert!(chain["comp_assoc"].contains("Rel"));
    }

    #[test]
    fn comment_prose_is_returned_and_not_recruited() {
        let read = reading();
        assert!(read.commentary.contains_key("Consequently"));
        assert!(read.commentary.contains_key("every"));
        assert!(read.commentary.contains_key("associative"));
        for form in &read.declarations {
            assert!(!form.recruited.contains_key("Consequently"));
            assert!(!form.recruited.contains_key("associative"));
        }
    }

    #[test]
    fn preamble_is_file_scope_and_charged_to_no_declaration() {
        let read = reading();
        assert!(read.preamble.contains_key("Mathlib.Tactic.Ring"));
        assert!(read.preamble.contains_key("Finset"));
        for form in &read.declarations {
            assert!(!form.recruited.contains_key("Mathlib.Tactic.Ring"));
            assert!(!form.recruited.contains_key("Finset"));
        }
    }

    #[test]
    fn the_namespace_is_retained_as_lineage_and_the_join_is_the_short_name() {
        let read = reading();
        let comp = read
            .declarations
            .iter()
            .find(|form| form.name == "comp")
            .expect("comp is declared");
        assert_eq!(comp.namespace_path, vec!["Soma".to_owned()]);
        assert_eq!(comp.qualified(), "Soma.comp");
        // The body of `comp_assoc` writes `comp`, not `Soma.comp`, so the join key is the short one.
        assert!(read.declared_recruitment()["comp_assoc"].contains("comp"));
    }

    #[test]
    fn the_one_artifact_grain_reports_what_it_did_not_open() {
        let read = read_development(DEVELOPMENT, DeclarationGrain::OneArtifactOneDeclaration);
        assert_eq!(read.declarations.len(), 1);
        assert_eq!(read.declarations[0].name, "Rel");
        let unopened: Vec<&str> = read
            .unopened
            .iter()
            .map(|missed| missed.name.as_str())
            .collect();
        assert_eq!(unopened, vec!["comp", "comp_assoc"]);
    }

    #[test]
    fn a_namespace_name_is_scoping_and_recruited_by_nothing() {
        // `derivation_atlas` convicted `end Soma` as *"a receiver-visible coordinate of the file
        // layout promoted into a homological invariant"* and repaired only that half; `namespace
        // Soma` was still charged as a recruitment of `Soma`. Both halves are scoping here.
        let read = reading();
        assert_eq!(read.scoping.get("Soma"), Some(&2u32));
        for form in &read.declarations {
            assert!(!form.recruited.contains_key("Soma"));
        }
    }

    #[test]
    fn a_declaration_does_not_recruit_itself() {
        let read = reading();
        for form in &read.declarations {
            assert!(!form.recruited.contains_key(&form.name));
        }
    }

    #[test]
    fn a_nested_block_comment_closes_at_the_right_depth() {
        let text = "/- outer /- inner -/ still comment -/\ndef live : Nat := 0\n";
        let read = read_development(text, DeclarationGrain::EveryTopLevelDeclaration);
        assert_eq!(read.declarations.len(), 1);
        assert_eq!(read.declarations[0].name, "live");
        assert!(read.commentary.contains_key("outer"));
        assert!(read.commentary.contains_key("inner"));
        assert!(read.commentary.contains_key("still"));
    }

    #[test]
    fn a_modifier_does_not_hide_the_former() {
        let text = "@[simp]\nnoncomputable def held : Nat := 0\nprivate theorem kept : True := trivial\n";
        let read = read_development(text, DeclarationGrain::EveryTopLevelDeclaration);
        let names: Vec<&str> = read
            .declarations
            .iter()
            .map(|form| form.name.as_str())
            .collect();
        assert_eq!(names, vec!["held", "kept"]);
    }

    #[test]
    fn a_multi_line_header_is_one_statement() {
        let text = "theorem wide\n    (a : Nat)\n    (b : Nat) :\n    a = b := by\n  omega\n";
        let read = read_development(text, DeclarationGrain::EveryTopLevelDeclaration);
        assert_eq!(read.declarations.len(), 1);
        assert_eq!(read.declarations[0].statement, "(a : Nat) (b : Nat) : a = b");
    }

    #[test]
    fn an_indented_former_is_not_a_top_level_declaration() {
        let text = "theorem outer : True := by\n  have inner := trivial\n  exact inner\n";
        let read = read_development(text, DeclarationGrain::EveryTopLevelDeclaration);
        assert_eq!(read.declarations.len(), 1);
        assert_eq!(read.declarations[0].name, "outer");
    }

    #[test]
    fn ambiguity_across_a_joined_development_is_returned_not_resolved() {
        let one = read_development(
            "namespace A\ntheorem shared : True := trivial\nend A\n",
            DeclarationGrain::EveryTopLevelDeclaration,
        );
        let two = read_development(
            "namespace B\ntheorem shared : True := trivial\nend B\n",
            DeclarationGrain::EveryTopLevelDeclaration,
        );
        assert!(one.ambiguous_short_names.is_empty());
        assert!(two.ambiguous_short_names.is_empty());
        let joined = join(vec![one, two]);
        assert_eq!(
            joined.ambiguous_short_names["shared"],
            vec![vec!["A".to_owned()], vec!["B".to_owned()]]
        );
    }

    #[test]
    fn the_generated_deposit_shape_reads_identically_at_both_grains() {
        // One `theorem` per artifact is where the historical aperture is exact, and the two grains
        // must not disagree there — otherwise the plural reading is over-parsing.
        let artifact = "import KernelWitness\nnamespace Soma\ntheorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by\n  assumption\nend Soma\n";
        let one = read_development(artifact, DeclarationGrain::OneArtifactOneDeclaration);
        let every = read_development(artifact, DeclarationGrain::EveryTopLevelDeclaration);
        assert_eq!(
            one.derivations(ConductGrain::TermsAndTactics),
            every.derivations(ConductGrain::TermsAndTactics)
        );
        assert!(one.unopened.is_empty());
        assert_eq!(one.declarations[0].name, "carrier_transport");
        assert_eq!(
            one.declarations[0].statement,
            "(P : Prop) (h : P) : exactCarrier P"
        );
    }

    // ------------------------------------------------------------------ position and the sub-grain

    const PROOF: &str = r#"namespace Soma

def descendantCapacity (capacity : New) : Nat := capacity

theorem nonnegative
    (hd : Nat)
    (hz : descendantCapacity capacity ≠ 0)
    (n : Old) : True := by
  classical
  have hcap : 0 ≤ descendantCapacity capacity := by
    apply Finset.sum_nonneg
    intro m hm
  have hcap_pos : 0 < descendantCapacity capacity :=
    lt_of_le_of_ne hcap (Ne.symm hz)
  exact trivial

end Soma
"#;

    fn proof() -> DeclaredForm {
        read_development(PROOF, DeclarationGrain::EveryTopLevelDeclaration)
            .declarations
            .into_iter()
            .find(|form| form.name == "nonnegative")
            .expect("the theorem is declared")
    }

    #[test]
    fn a_binder_group_founds_before_its_colon_and_recruits_after() {
        let form = proof();
        // `hd`, `hz` are founded by their binder groups; `descendantCapacity` is the TYPE and is
        // recruited. This one structural rule is what removes hc/hcong/hm/hn/hz from the terms.
        assert!(form.local_bindings.contains_key("hd"));
        assert!(form.local_bindings.contains_key("hz"));
        assert!(form.recruited.contains_key("descendantCapacity"));
        assert!(!form.recruited.contains_key("hd"));
        assert!(!form.recruited.contains_key("hz"));
    }

    #[test]
    fn a_tactic_head_is_returned_beside_the_terms_and_never_inside_them() {
        let form = proof();
        for head in ["classical", "apply", "intro", "have", "exact"] {
            assert!(form.tactics.contains_key(head), "{head} is in tactic position");
            assert!(!form.recruited.contains_key(head), "{head} is not a term");
        }
        // A tactic's ARGUMENT stays a term: `apply Finset.sum_nonneg`.
        assert!(form.recruited.contains_key("Finset.sum_nonneg"));
    }

    #[test]
    fn a_continuation_line_is_not_read_as_a_tactic() {
        let form = proof();
        // `have hcap_pos : … :=` demands a continuation, so `lt_of_le_of_ne` on the next line is a
        // TERM. Without the rule it would be a tactic named after a mathlib lemma.
        assert!(form.recruited.contains_key("lt_of_le_of_ne"));
        assert!(!form.tactics.contains_key("lt_of_le_of_ne"));
    }

    #[test]
    fn the_proof_body_founds_its_own_steps() {
        let form = proof();
        let binders: Vec<&str> = form.steps.iter().map(|step| step.binder.as_str()).collect();
        assert_eq!(binders, vec!["hcap", "hm", "hcap_pos"]);
        assert_eq!(form.steps[0].former, "have");
        assert_eq!(form.steps[1].former, "intro");
    }

    #[test]
    fn a_completion_at_one_step_is_an_arrival_at_the_next() {
        let form = proof();
        // `hcap_pos` recruits `hcap`, which an EARLIER step founded. That is the leader inside one
        // declaration, and the flat reading charged both to the theorem as a depth-one star.
        let hcap = form.steps.iter().position(|step| step.binder == "hcap").unwrap();
        let hcap_pos = form.steps.iter().position(|step| step.binder == "hcap_pos").unwrap();
        assert!(form.internal_arrivals().contains(&(hcap, hcap_pos)));
        assert_eq!(form.internal_depth(), vec![hcap, hcap_pos]);
    }

    #[test]
    fn the_conduct_grain_decides_whether_a_tactic_is_a_recruitment() {
        let form = proof();
        let terms = form.derivation(ConductGrain::TermsOnly);
        let both = form.derivation(ConductGrain::TermsAndTactics);
        assert!(!terms.recruited.contains_key("classical"));
        assert!(both.recruited.contains_key("classical"));
        assert!(terms.recruited.contains_key("descendantCapacity"));
        assert!(both.recruited.contains_key("descendantCapacity"));
    }

    #[test]
    fn the_two_bounding_instruments_return_their_residue() {
        let read = read_development(PROOF, DeclarationGrain::EveryTopLevelDeclaration);
        // Structural: no declared name landed in tactic position here, and the instrument says so
        // rather than being absent.
        assert!(read.tactic_position_declared().is_empty());
        // Distributional: `Finset.sum_nonneg` occurs in exactly one declaration and is declared
        // nowhere -- a legitimately singular environment lemma, returned rather than subtracted,
        // because subtracting it would delete a real recruitment.
        let singular = read.single_occurrence_terms();
        assert_eq!(singular.get("Finset.sum_nonneg"), Some(&"nonnegative"));
    }

    #[test]
    fn declared_recruitment_is_empty_when_nothing_opens() {
        let text = "theorem alone : True := trivial\n";
        let read = read_development(text, DeclarationGrain::EveryTopLevelDeclaration);
        assert!(read.declared_recruitment().is_empty());
    }
}
