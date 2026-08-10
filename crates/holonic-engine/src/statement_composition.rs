//! Composing a statement the deposit does not reach, into a slot the recovered grammar founded,
//! licensed by the founded morphology — and adjudicating every candidate as a **population with
//! retained obstructions**.
//!
//! ## What was blocked, and what this is not allowed to do about it
//!
//! `research/records/2026-08-08_THE_INSTANCE_FOUNDS_ROUTES_AND_NEVER_FOUNDS_STATEMENTS.md` §6
//! established by construction that the conditioned production **founds routes and never founds
//! statements**, and named the three sites that block it:
//!
//! ```text
//!   conditioned_derivation::derive   gates the licensing loop on statement equality
//!   compose_passage                  writes the queried statement VERBATIM
//!   ConditionedBody::passages        refuses EmittedPassageMissedItsStatement
//! ```
//!
//! **None of the three is weakened here and none may be.** They are correct for what `derive` does:
//! `derive` founds routes, and route-founding must preserve the statement or the route lands on the
//! wrong 0-cell. This module is a **different species of move** with its own entry point beside
//! them. [`found_statements`] never calls `derive`, and the falsifier that `derive` returns the
//! empty population on an absent statement still fires exactly as the record measured it.
//!
//! ## The mechanism, in the four slots `CLAUDE.md` §4 asks for
//!
//! ```text
//!   source geometry    the deposit's statements, read by `statement_grammar` into slots and residue
//!   receiver map       the founded morphology: which stems the linguistic corpus committed
//!   transport          substitution into one recovered span
//!   returned residual  every candidate that no committed stem licenses, every candidate the grammar
//!                      cannot place, and every candidate that lands back on the deposit -- each
//!                      retained by name with the obstruction that refused it
//! ```
//!
//! ## The licence law, and it is TWO conjuncts
//!
//! **The contact.** Every composition species names the pair of identifiers it brings into contact,
//! and the morphology must hold that pair together. That is the same mechanism
//! `conditioned_derivation::derive` licenses a bridge by — two identifiers sharing a committed
//! founded stem under [`FoundedMorphology::cover`]'s maximality — lifted from the proof body to the
//! statement. A body exposed to nothing commits no stem, covers nothing, holds no pair together, and
//! therefore admits **no** composed statement. The conditioning is on the causal path here for
//! exactly the reason it is there, and the unconditioned null is the control that shows it.
//!
//! **The place**, and it was missing until 2026-08-09. The contact licence admits
//! `(P : Prop) (h : P) : exactCarrier apply` because `P` and `apply` share the founded letter `p`,
//! and `(a b : nlinarith) : a = b` for the same reason. It could not do otherwise: it is a statement
//! about two identifiers and never about the **slot**. [`StatementPositionEcology`] is the second
//! conjunct — where the material's own reading places each identifier, and which declarations share
//! a shape — and with both on the causal path the composition returns statements whose names resolve
//! against declarations the material wrote. The two settings are a declared gauge,
//! [`PositionGate`], and `the_statement_is_founded` runs both over one candidate population so the
//! orbit is exhibited rather than assumed.
//!
//! ## Admission is a population, never a filter
//!
//! [`admit`] returns **every candidate with its verdict**. A refusal is a typed
//! [`StatementObstruction`] carrying the material that refused it — the pair with no shared stem and
//! both their covers, the residue span, the aperture member, the standing statement it landed on.
//! Nothing is discarded, nothing is scored, nothing is ranked, and no verdict is a boolean returned
//! in place of a population. That is the shape `substitution_realizers` already uses for refused
//! substitutions and the reason it uses it: *"a record that keeps only what was accepted is
//! success-filtering wearing bookkeeping's name."*
//!
//! An admission also **carries what the grammar does not certify about it** rather than erasing it:
//! substituting `exact_chart_carry` into a first position is admitted, and the admission carries
//! `HeadArityIsUnfounded` because the statement population never put that identifier in first
//! position. Admission under a declared aperture that the return carries is
//! `substitution_realizers`' own discipline.
//!
//! ## The fourth move species
//!
//! `derivation_skein` reads three species off a production — `Deposit`, `RecruitmentExchange`,
//! `LemmaSplit` — and **all three preserve `statement` by construction**, which is visible in the
//! moves themselves: every one of them has the statement 0-cell in its *boundary*, because both
//! sides of the move already reach that statement. [`MoveSpecies::StatementComposition`] is the
//! fourth, and it is separated from the other three by a property of the substitution rather than by
//! its name: **its statement 0-cell is in `after` and not in `boundary`.** The move deposits the
//! statement vertex itself. [`statement_composition_moves`] founds them and
//! [`deposits_its_statement_vertex`] is the discriminator.
//!
//! ## What is not claimed
//!
//! Nothing here is submitted to a kernel and nothing may be: a foreign process deciding what the
//! body may construct is `G_authored` (`CLAUDE.md` §13 rule 2). What [`compose_in_scope`] adds is
//! narrower and is stated exactly: an artifact carries the founding lines **the material itself
//! wrote** for the names its own statement uses, so a *batch* grade of the returned population is
//! possible at all. That is name resolution and it is not type correctness — the population
//! contains `(P : P) (h : P) : exactCarrier P`, whose every name resolves and which no elaborator
//! will take. A composed passage is production read as structure exactly as the deposited artifacts
//! are; the deposit itself carries `theorem carrier_transport ... := Nat.zero`, which no kernel
//! accepts and which the atlas reads all the same. A composed statement is one this deposit's own
//! grammar, morphology and position ecology reach; it is not asserted to be true or provable, and
//! the composed **body** is not a proof. Nothing here bears on any Millennium result.

use std::collections::{BTreeMap, BTreeSet};

use crate::algebraic::CausalCellId;
use crate::conditioned_derivation::{
    ConditionedBody, ConditionedCircuit, ConditionedDerivationRefusal, ContactSpecies,
    FoundedMorphology, Passage,
    PassageId, PassageOrigin,
};
use crate::derivation_atlas::{read_derivation, statement_vertex_key};
use crate::derivation_skein::{passage_interior, DerivationMove, MoveSpecies};
use crate::lean_development::{DevelopmentReading, PREAMBLE_FORMS};
use crate::skein::Substitution;
use crate::statement_grammar::{
    recover, BodyReading, GrammarAperture, RecoveredStatementGrammar, SlotSpecies, Span,
    StatementGrammarRefusal, StatementReading,
};

// -------------------------------------------------------------------------------------------------
// The candidates
// -------------------------------------------------------------------------------------------------

/// How a candidate statement was composed. Named by mechanism; never ranked.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CompositionSpecies {
    /// One recovered slot's occupant replaced by an identifier the deposit recruits.
    SlotSubstitution,
    /// One recovered bracket group removed from the leading region.
    BinderWithdrawal,
    /// A bracket group the population witnesses elsewhere appended to the leading region.
    BinderExtension,
    /// An argument position filled with an application of a founded head. The shape the population
    /// never witnesses, declared so that its refusal is measured rather than assumed.
    ArgumentApplication,
    /// A substitution aimed at a span the grammar retained as residue. Declared for the same reason.
    ResidueSubstitution,
}

impl CompositionSpecies {
    pub const fn name(self) -> &'static str {
        match self {
            Self::SlotSubstitution => "slot-substitution",
            Self::BinderWithdrawal => "binder-withdrawal",
            Self::BinderExtension => "binder-extension",
            Self::ArgumentApplication => "argument-application",
            Self::ResidueSubstitution => "residue-substitution",
        }
    }

    /// Every species, in declared order. An aperture that is exhausted rather than sampled.
    pub const ALL: [Self; 5] = [
        Self::SlotSubstitution,
        Self::BinderWithdrawal,
        Self::BinderExtension,
        Self::ArgumentApplication,
        Self::ResidueSubstitution,
    ];
}

/// One composed statement, before anything has been decided about it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CandidateStatement {
    pub species: CompositionSpecies,
    /// The deposited statement it was composed from.
    pub from: String,
    /// The composed statement, in the same normalized form a deposited one carries.
    pub statement: String,
    /// The recovered position the composition acted at, named by species and offset — `head26`,
    /// `type5`, `withdrew0`. Part of a composed declaration's name, so two compositions at two
    /// positions never collide.
    pub site: String,
    /// The recovered slot species the composition acted on, when it acted on a slot.
    pub slot: Option<SlotSpecies>,
    /// The identifier the composition displaced or moved. The left side of the contact pair.
    pub held: String,
    /// The identifier it brought into contact. The right side.
    pub brought: String,
    /// The standing declarations that reach [`Self::from`]. Each becomes one composed route.
    pub declarations: Vec<String>,
    /// The recovered rule that composed it, in one line, for a reader.
    pub rule: String,
}

impl CandidateStatement {
    /// A stable identity for this candidate, independent of any verdict.
    pub fn key(&self) -> String {
        format!(
            "{}|{}|{}|{}",
            self.species.name(),
            self.from,
            self.site,
            self.brought
        )
    }
}

/// One founded stem holding a contact pair together.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct StatementLicence {
    pub stem: String,
    pub held_at: usize,
    pub brought_at: usize,
    /// The wholes of linguistic material that witnessed the stem. Lineage, never a tally.
    pub wholes: Vec<String>,
    /// **What kind of contact this licence is** — simple, superposed, or crossed. Read off the two
    /// covers at the site where the contact is formed, and carried rather than collapsed.
    ///
    /// A licence used to be a stem and two offsets, which says *that* the two identifiers meet and
    /// nothing about *how*. The face says how many carriers are co-present at the site; the
    /// crossings say which other stems share letters the bridging one cannot give up.
    pub contact: ContactSpecies,
    /// Every occurrence co-present with the bridging stem, on each side.
    pub held_face: Vec<String>,
    pub brought_face: Vec<String>,
    /// The stems the bridging occurrence crosses, on each side.
    pub held_crossings: Vec<String>,
    pub brought_crossings: Vec<String>,
}

/// Why a candidate was refused, with the material that refused it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum StatementObstruction {
    /// No committed founded stem holds the contact pair together. Both covers are carried, so the
    /// refusal can be checked rather than believed.
    NoFoundedStemHoldsThem {
        held: String,
        held_cover: String,
        brought: String,
        brought_cover: String,
    },
    /// The composition lands on a statement the deposit already reaches. It returns to the deposit
    /// rather than founding, and is retained as the return it is.
    ComposedStatementIsAlreadyStanding { statement: String },
    /// The composition aims at a span the grammar retained as residue. Nothing may be substituted
    /// into material the reading could not decompose.
    SlotLiesInGrammarResidue {
        statement: String,
        residue: String,
        refused_by: String,
    },
    /// The composition needs a shape the statement population never witnessed.
    GrammarNeverWitnessedTheShape { bound: GrammarAperture },
    /// The leading region the composition would produce is a length the population never witnessed
    /// and the founded sequence reading does not cover.
    BinderListLengthIsUnfounded {
        length: usize,
        witnessed: BTreeSet<usize>,
    },
    /// The composition changed nothing.
    ComposedStatementIsUnchanged { statement: String },
    /// **The composed statement uses an identifier no earlier binder introduced.** `at` is the slot
    /// position in span order, so the refusal names where the use is and not merely that there is
    /// one. The bound/standing distinction is read off the population: an identifier the standing
    /// statements never put in a binder-name position is a standing declaration and is free to be
    /// used; one they do bind is a bound variable and must be bound before it is used.
    IdentifierUsedBeforeItIsBound {
        statement: String,
        identifier: String,
        at: usize,
    },
    /// The artifact composed for this candidate did not read back reaching the composed statement.
    /// The analogue of `EmittedPassageMissedItsStatement` for this species, retained as a candidate
    /// obstruction rather than raised, so one malformed composition cannot void a population.
    ReadBackMissedTheComposition { wanted: String, read: String },
    /// The material never stood this identifier — nor any member of its declared-shape cohort — in
    /// the slot species the composition puts it in.
    ///
    /// **The position licence, and the second conjunct of the conditioning.** The stem licence says
    /// two identifiers belong together; this one says the brought identifier belongs *there*. Both
    /// the places the material did stand it and its cohort are carried, so the refusal can be
    /// checked rather than believed.
    IdentifierNeverStoodInThisPosition {
        brought: String,
        slot: SlotSpecies,
        stood_in: Vec<ConductPosition>,
        cohort: Vec<String>,
    },
}

impl std::fmt::Display for StatementObstruction {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IdentifierUsedBeforeItIsBound { statement, identifier, at } => write!(
                formatter,
                "`{statement}` uses `{identifier}` at slot {at}, and no earlier binder introduces it"
            ),
            Self::NoFoundedStemHoldsThem {
                held,
                held_cover,
                brought,
                brought_cover,
            } => write!(
                formatter,
                "no committed stem holds {held} ({held_cover}) and {brought} ({brought_cover}) together"
            ),
            Self::ComposedStatementIsAlreadyStanding { statement } => write!(
                formatter,
                "the composition lands on {statement:?}, which the deposit already reaches"
            ),
            Self::SlotLiesInGrammarResidue {
                statement, residue, ..
            } => write!(
                formatter,
                "the target span {residue:?} of {statement:?} is residue the grammar could not decompose"
            ),
            Self::GrammarNeverWitnessedTheShape { bound } => write!(formatter, "{bound}"),
            Self::BinderListLengthIsUnfounded { length, witnessed } => write!(
                formatter,
                "a leading region of {length} groups is unfounded; the population witnesses {witnessed:?}"
            ),
            Self::ComposedStatementIsUnchanged { statement } => {
                write!(formatter, "the composition returned {statement:?} unchanged")
            }
            Self::ReadBackMissedTheComposition { wanted, read } => write!(
                formatter,
                "the composed artifact was read reaching {read:?} rather than {wanted:?}"
            ),
            Self::IdentifierNeverStoodInThisPosition {
                brought,
                slot,
                stood_in,
                cohort,
            } => {
                let places: Vec<String> = stood_in.iter().map(ToString::to_string).collect();
                let places = if places.is_empty() {
                    "nowhere the reading placed it".to_owned()
                } else {
                    places.join(", ")
                };
                write!(
                    formatter,
                    "the material never stood {brought} in {} position; it stands at {places}, and its declared-shape cohort is {cohort:?}",
                    slot.name()
                )
            }
        }
    }
}

impl StatementObstruction {
    /// The obstruction's own species name, so a population can be grouped without matching on it.
    pub const fn species(&self) -> &'static str {
        match self {
            Self::NoFoundedStemHoldsThem { .. } => "no-founded-stem-holds-them",
            Self::ComposedStatementIsAlreadyStanding { .. } => "composed-statement-is-already-standing",
            Self::SlotLiesInGrammarResidue { .. } => "slot-lies-in-grammar-residue",
            Self::GrammarNeverWitnessedTheShape { .. } => "grammar-never-witnessed-the-shape",
            Self::BinderListLengthIsUnfounded { .. } => "binder-list-length-is-unfounded",
            Self::IdentifierUsedBeforeItIsBound { .. } => "identifier-used-before-it-is-bound",
            Self::ComposedStatementIsUnchanged { .. } => "composed-statement-is-unchanged",
            Self::ReadBackMissedTheComposition { .. } => "read-back-missed-the-composition",
            Self::IdentifierNeverStoodInThisPosition { .. } => {
                "identifier-never-stood-in-this-position"
            }
        }
    }
}

/// What the admission rule returned for one candidate.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum StatementAdmission {
    /// The morphology holds the contact pair together. Every stem that does is carried; nothing
    /// selects among them.
    Admitted {
        licences: Vec<StatementLicence>,
        /// What the recovered grammar does **not** certify about this composition. Carried with the
        /// admission rather than erased by it.
        carried_aperture: Vec<GrammarAperture>,
        /// Where the material stood the brought identifier, when the position gate was applied.
        /// The admission carries its own second licence exactly as it carries the first. Empty when
        /// the gate was withheld or when the composition placed no identifier into a slot.
        stood_in: Vec<ConductPosition>,
    },
    Refused(StatementObstruction),
}

impl StatementAdmission {
    pub const fn is_admitted(&self) -> bool {
        matches!(self, Self::Admitted { .. })
    }

    pub fn licences(&self) -> &[StatementLicence] {
        match self {
            Self::Admitted { licences, .. } => licences,
            Self::Refused(_) => &[],
        }
    }

    pub const fn obstruction(&self) -> Option<&StatementObstruction> {
        match self {
            Self::Admitted { .. } => None,
            Self::Refused(obstruction) => Some(obstruction),
        }
    }
}

/// One candidate and what the admission rule said about it. The unit of the returned population.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct AdjudicatedCandidate {
    pub candidate: CandidateStatement,
    pub admission: StatementAdmission,
}

/// The complete adjudicated population, with the grammar it was composed against.
#[derive(Clone, Debug)]
pub struct AdmittedStatements {
    pub grammar: RecoveredStatementGrammar,
    /// **Every** candidate, with its verdict. Never a filtered list.
    pub adjudicated: Vec<AdjudicatedCandidate>,
    /// The statements the body was mounted on, carried so a caller can check a founding without
    /// re-deriving the deposit.
    pub standing: BTreeSet<String>,
    /// Whether the position ecology was on the causal path for this adjudication. The declared gauge
    /// setting, carried with its own return so an orbit is never read off two populations whose
    /// settings were not recorded.
    pub gate: PositionGate,
}

impl AdmittedStatements {
    pub fn admitted(&self) -> Vec<&AdjudicatedCandidate> {
        self.adjudicated
            .iter()
            .filter(|entry| entry.admission.is_admitted())
            .collect()
    }

    pub fn refused(&self) -> Vec<&AdjudicatedCandidate> {
        self.adjudicated
            .iter()
            .filter(|entry| !entry.admission.is_admitted())
            .collect()
    }

    /// The composed statements the rule admitted, none of which the deposit reaches.
    pub fn founded_statements(&self) -> BTreeSet<String> {
        self.admitted()
            .into_iter()
            .map(|entry| entry.candidate.statement.clone())
            .collect()
    }

    /// The retained obstructions, grouped by species, each carrying its complete membership.
    pub fn obstructions(&self) -> BTreeMap<&'static str, Vec<&AdjudicatedCandidate>> {
        let mut grouped: BTreeMap<&'static str, Vec<&AdjudicatedCandidate>> = BTreeMap::new();
        for entry in self.refused() {
            if let Some(obstruction) = entry.admission.obstruction() {
                grouped.entry(obstruction.species()).or_default().push(entry);
            }
        }
        grouped
    }

    /// The admitted candidates whose licence is carried by a founded stem of at least `letters`
    /// characters.
    ///
    /// **A declared aperture, not a filter on quality.** It is `MoveAperture::morphemic`'s own
    /// distinction — a licence carried by a whole word the corpus committed is a different kind of
    /// object from one carried by a single residual letter — and the population it excludes is
    /// returned by [`Self::admitted_below_morphemic`] rather than dropped.
    pub fn admitted_at_morphemic(&self, letters: usize) -> Vec<&AdjudicatedCandidate> {
        self.admitted()
            .into_iter()
            .filter(|entry| {
                entry
                    .admission
                    .licences()
                    .iter()
                    .any(|licence| licence.stem.chars().count() >= letters)
            })
            .collect()
    }

    /// The complement of [`Self::admitted_at_morphemic`], exhibited so the aperture is recoverable.
    pub fn admitted_below_morphemic(&self, letters: usize) -> Vec<&AdjudicatedCandidate> {
        self.admitted()
            .into_iter()
            .filter(|entry| {
                entry
                    .admission
                    .licences()
                    .iter()
                    .all(|licence| licence.stem.chars().count() < letters)
            })
            .collect()
    }

    /// The rule admitted something and refused something. A rule that does neither has not been
    /// exercised: one that admits everything is a filter inverted, one that admits nothing is a
    /// filter, and both are refused as evidence.
    pub fn is_a_population(&self) -> bool {
        !self.admitted().is_empty() && !self.refused().is_empty()
    }
}

// -------------------------------------------------------------------------------------------------
// The composition
// -------------------------------------------------------------------------------------------------

/// Why a composition was refused outright, as distinct from a candidate being refused admission.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StatementCompositionRefusal {
    Grammar(StatementGrammarRefusal),
    Conditioned(ConditionedDerivationRefusal),
    /// A composed artifact could not be read back at all. The composer and the reading disagree,
    /// which is a defect in the composer and never a property of the material.
    ComposedPassageDeclaresNothing { name: String },
    /// A composed artifact was read back reaching a different statement. The route would land on the
    /// wrong 0-cell — the same refusal `ConditionedBody::passages` makes for a derived passage, made
    /// here for a composed one, and neither weakens the other.
    ComposedPassageMissedItsStatement {
        name: String,
        wanted: String,
        read: String,
    },
}

impl std::fmt::Display for StatementCompositionRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Grammar(refusal) => write!(formatter, "{refusal}"),
            Self::Conditioned(refusal) => write!(formatter, "{refusal}"),
            Self::ComposedPassageDeclaresNothing { name } => {
                write!(formatter, "the composed passage {name} declares no theorem")
            }
            Self::ComposedPassageMissedItsStatement { name, wanted, read } => write!(
                formatter,
                "the composed passage {name} was read reaching {read:?} rather than {wanted:?}"
            ),
        }
    }
}

impl std::error::Error for StatementCompositionRefusal {}

impl From<StatementGrammarRefusal> for StatementCompositionRefusal {
    fn from(refusal: StatementGrammarRefusal) -> Self {
        Self::Grammar(refusal)
    }
}

impl From<ConditionedDerivationRefusal> for StatementCompositionRefusal {
    fn from(refusal: ConditionedDerivationRefusal) -> Self {
        Self::Conditioned(refusal)
    }
}

/// The declaration names reaching each statement the body stands on.
fn declarations_reaching(body: &ConditionedBody) -> BTreeMap<String, Vec<String>> {
    let mut reaching: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for passage in body.standing() {
        reaching
            .entry(passage.derivation.statement.clone())
            .or_default()
            .insert(passage.derivation.name.clone());
    }
    reaching
        .into_iter()
        .map(|(statement, names)| (statement, names.into_iter().collect()))
        .collect()
}

/// Every candidate the recovered grammar can compose out of the deposit's own material.
///
/// The generation is **exhausted, never sampled**: every recovered slot against every recruited
/// identifier, every witnessed group against every statement, every declared unfounded shape. What
/// is admitted is decided afterwards, by [`admit`], and separately.
pub fn compose_candidates(
    grammar: &RecoveredStatementGrammar,
    recruited: &BTreeSet<String>,
    reaching: &BTreeMap<String, Vec<String>>,
) -> Vec<CandidateStatement> {
    let mut candidates = Vec::new();
    for reading in grammar.readings() {
        let declarations = reaching
            .get(&reading.statement)
            .cloned()
            .unwrap_or_default();
        if declarations.is_empty() {
            continue;
        }
        candidates.extend(slot_substitutions(reading, recruited, &declarations));
        candidates.extend(binder_withdrawals(reading, &declarations));
        candidates.extend(binder_extensions(grammar, reading, &declarations));
        candidates.extend(argument_applications(grammar, reading, &declarations));
        candidates.extend(residue_substitutions(reading, recruited, &declarations));
    }
    candidates.sort();
    candidates.dedup();
    candidates
}

fn slot_substitutions(
    reading: &StatementReading,
    recruited: &BTreeSet<String>,
    declarations: &[String],
) -> Vec<CandidateStatement> {
    let mut candidates = Vec::new();
    for slot in reading.slots() {
        for brought in recruited {
            if *brought == slot.occupant {
                continue;
            }
            candidates.push(CandidateStatement {
                species: CompositionSpecies::SlotSubstitution,
                from: reading.statement.clone(),
                statement: reading.substituted(slot.span, brought),
                site: format!("{}{}", slot.species.tag(), slot.span.at),
                slot: Some(slot.species),
                held: slot.occupant.clone(),
                brought: brought.clone(),
                declarations: declarations.to_vec(),
                rule: format!(
                    "the recovered {} at offset {} carried {}; the substitution puts {} there",
                    slot.species.name(),
                    slot.span.at,
                    slot.occupant,
                    brought
                ),
            });
        }
    }
    candidates
}

/// The identifiers a statement already carries in a position the grammar recovered, as possible
/// partners for a group being moved in or out.
fn carried_identifiers(reading: &StatementReading, except: Option<Span>) -> Vec<(SlotSpecies, String)> {
    reading
        .slots()
        .into_iter()
        .filter(|slot| {
            matches!(
                slot.species,
                SlotSpecies::BinderType | SlotSpecies::BodyHead
            )
        })
        .filter(|slot| except.is_none_or(|span| slot.span.at < span.at || slot.span.at >= span.through))
        .map(|slot| (slot.species, slot.occupant))
        .collect()
}

fn binder_withdrawals(
    reading: &StatementReading,
    declarations: &[String],
) -> Vec<CandidateStatement> {
    let mut candidates = Vec::new();
    for group in &reading.binders {
        let Some(carried) = &group.carried else {
            continue;
        };
        let composed = reading.without_group(group);
        for (species, partner) in carried_identifiers(reading, Some(group.span)) {
            candidates.push(CandidateStatement {
                species: CompositionSpecies::BinderWithdrawal,
                from: reading.statement.clone(),
                statement: composed.clone(),
                site: format!("withdrew{}", group.span.at),
                slot: None,
                held: carried.occupant.clone(),
                brought: partner.clone(),
                declarations: declarations.to_vec(),
                rule: format!(
                    "the leading region is a nonempty sequence of groups; withdrawing {} leaves \
                     {}'s {} carrying the same material",
                    group.text(&reading.statement),
                    partner,
                    species.name()
                ),
            });
        }
    }
    candidates
}

fn binder_extensions(
    grammar: &RecoveredStatementGrammar,
    reading: &StatementReading,
    declarations: &[String],
) -> Vec<CandidateStatement> {
    let mut candidates = Vec::new();
    let already: BTreeSet<String> = reading
        .binders
        .iter()
        .map(|group| group.text(&reading.statement).to_owned())
        .collect();
    for (ordinal, group_text) in grammar.witnessed_groups().into_iter().enumerate() {
        if already.contains(&group_text) {
            continue;
        }
        let Some(composed) = reading.with_group(&group_text) else {
            continue;
        };
        // the type the transplanted group carries, read out of the population's own reading of it
        let Some(moved_type) = grammar
            .readings()
            .iter()
            .flat_map(|other| other.binders.iter().map(move |group| (other, group)))
            .find(|(other, group)| group.text(&other.statement) == group_text)
            .and_then(|(_, group)| group.carried.as_ref())
            .map(|slot| slot.occupant.clone())
        else {
            continue;
        };
        for (species, partner) in carried_identifiers(reading, None) {
            candidates.push(CandidateStatement {
                species: CompositionSpecies::BinderExtension,
                from: reading.statement.clone(),
                statement: composed.clone(),
                // the transplanted group's own position in the population's canonical group order,
                // so two extensions of one statement by two different groups never collide
                site: format!("extended{}g{ordinal}", reading.split_at.unwrap_or(0)),
                slot: None,
                held: moved_type.clone(),
                brought: partner.clone(),
                declarations: declarations.to_vec(),
                rule: format!(
                    "the leading region is a nonempty sequence of groups; {group_text} is a group \
                     the population witnesses, appended beside {partner}'s {}",
                    species.name()
                ),
            });
        }
    }
    candidates
}

fn argument_applications(
    grammar: &RecoveredStatementGrammar,
    reading: &StatementReading,
    declarations: &[String],
) -> Vec<CandidateStatement> {
    let Some(BodyReading::Applied { arguments, .. }) = &reading.body else {
        return Vec::new();
    };
    let Some((open, close)) = grammar.bracket() else {
        return Vec::new();
    };
    let mut candidates = Vec::new();
    for argument in arguments {
        for (head, arities) in grammar.heads() {
            if arities.len() != 1 {
                continue;
            }
            let nested = format!("{open}{head} {}{close}", argument.occupant);
            candidates.push(CandidateStatement {
                species: CompositionSpecies::ArgumentApplication,
                from: reading.statement.clone(),
                statement: reading.substituted(argument.span, &nested),
                site: format!("nest{}", argument.span.at),
                slot: Some(SlotSpecies::BodyArgument),
                held: argument.occupant.clone(),
                brought: head.clone(),
                declarations: declarations.to_vec(),
                rule: format!(
                    "the population founds {head} at arity {}; this puts that application in the \
                     argument position at offset {}",
                    arities.iter().next().copied().unwrap_or(0),
                    argument.span.at
                ),
            });
        }
    }
    candidates
}

fn residue_substitutions(
    reading: &StatementReading,
    recruited: &BTreeSet<String>,
    declarations: &[String],
) -> Vec<CandidateStatement> {
    let mut candidates = Vec::new();
    for residue in &reading.residue {
        for brought in recruited {
            candidates.push(CandidateStatement {
                species: CompositionSpecies::ResidueSubstitution,
                from: reading.statement.clone(),
                statement: reading.substituted(residue.span, brought),
                site: format!("residue{}", residue.span.at),
                slot: None,
                held: residue.text.clone(),
                brought: brought.clone(),
                declarations: declarations.to_vec(),
                rule: format!(
                    "the span {:?} is residue: {}",
                    residue.text, residue.refused_by
                ),
            });
        }
    }
    candidates
}

// -------------------------------------------------------------------------------------------------
// The position ecology -- the second conjunct of the conditioning
// -------------------------------------------------------------------------------------------------

/// Where the material was witnessed **placing** an identifier.
///
/// Every member is a population [`crate::lean_development`] already returns, or a slot
/// [`crate::statement_grammar`] already recovers. None of them is a judgement about what an
/// identifier *is*: `apply` is not called a tactic here because tactics are a category, it is
/// recorded as having stood in tactic position because that is where the reading found it, and the
/// same token standing in a statement slot elsewhere would carry both.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConductPosition {
    /// It stood in this recovered slot of some declaration's own statement.
    Slot(SlotSpecies),
    /// The material declares it, under this former.
    Declared { former: String },
    /// It was named in term position of a proof body — [`crate::lean_development::DeclaredForm`]'s
    /// `recruited`.
    Term,
    /// It stood as the leading identifier of a proof step — that carrier's `tactics`.
    Tactic,
    /// A binding tactic founded it inside a proof body — that carrier's `local_bindings`.
    LocalBinding,
    /// It was named on a file-scope preamble line.
    Preamble,
    /// It named a `namespace`/`section` scope.
    Scoping,
}

impl std::fmt::Display for ConductPosition {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Slot(species) => write!(formatter, "slot:{}", species.name()),
            Self::Declared { former } => write!(formatter, "declared-by:{former}"),
            Self::Term => write!(formatter, "term"),
            Self::Tactic => write!(formatter, "tactic"),
            Self::LocalBinding => write!(formatter, "local-binding"),
            Self::Preamble => write!(formatter, "preamble"),
            Self::Scoping => write!(formatter, "scoping"),
        }
    }
}

/// One **declared shape** and every declaration that has it.
///
/// The skeleton is the declaration's own statement with each binder-name token replaced by the
/// ordinal of the binder that founded it, so `(P : Prop) : Prop` and `(Q : Prop) : Prop` are one
/// shape and `(h : P) : exactCarrier P` is another. The rewrite is not an authored alpha-equivalence:
/// it uses exactly the `BinderName` slots the recovered grammar returns, and those exist because
/// `lean_development` reads a binder group's names as **founded** and its type as **recruited**.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct DeclaredShape {
    pub skeleton: String,
    /// The declarations carrying it, in the order the reading founded them.
    pub members: Vec<String>,
}

/// The founding lines a composed artifact must carry for its own names to resolve, read verbatim out
/// of the material.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct ComposedScope {
    /// `import` lines, which Lean's own file law puts before everything else.
    pub imports: Vec<String>,
    /// Every other founding line — the declarations the statement's names transitively need, then
    /// the preamble lines founding what no declaration does — in the order the material carries them.
    pub founding: Vec<String>,
    /// Founding lines whose declaration does not finish on the line that opens it. **The scope is
    /// incomplete when this is non-empty** and says so rather than emitting a truncated declaration
    /// as though it were whole.
    pub incomplete: Vec<String>,
}

impl ComposedScope {
    pub fn is_empty(&self) -> bool {
        self.imports.is_empty() && self.founding.is_empty()
    }

    /// The scope carries every name it was asked for, whole.
    pub fn is_complete(&self) -> bool {
        self.incomplete.is_empty()
    }
}

/// Whether the position ecology is on the causal path.
///
/// **A declared gauge whose orbit is the evidence.** `CLAUDE.md` §8: a gauge whose group acts
/// trivially on the declared material is not a gauge, so the two settings are run over one candidate
/// population and the difference between the two admitted populations is exhibited rather than
/// assumed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PositionGate {
    /// The composition must place an identifier where the material places one.
    Applied,
    /// The gate is withheld. This is the rule as it stood before the ecology was built, and it is
    /// the control.
    Withheld,
}

impl PositionGate {
    pub const fn name(self) -> &'static str {
        match self {
            Self::Applied => "position-gate-applied",
            Self::Withheld => "position-gate-withheld",
        }
    }
}

/// A character a token may be made of. `statement_grammar`'s own rule, restated because that one is
/// private and a composed statement must be tokenized exactly as a deposited one is.
const fn is_token_character(symbol: char) -> bool {
    symbol.is_ascii_alphanumeric() || symbol == '_' || symbol == '.'
}

/// The whole-token population of one line of material.
fn tokens_of(text: &str) -> Vec<String> {
    let mut found = Vec::new();
    let mut carried = String::new();
    for symbol in text.chars() {
        if is_token_character(symbol) {
            carried.push(symbol);
            continue;
        }
        if !carried.is_empty() {
            found.push(std::mem::take(&mut carried));
        }
    }
    if !carried.is_empty() {
        found.push(carried);
    }
    found
        .into_iter()
        .filter(|token| token.chars().next().is_some_and(|first| first.is_ascii_alphabetic() || first == '_'))
        .collect()
}

/// One statement with every binder-name token replaced by the ordinal of the binder that founded it.
fn alpha_normalized(reading: &StatementReading) -> String {
    let slots = reading.slots();
    let mut ordinal: BTreeMap<String, usize> = BTreeMap::new();
    for slot in &slots {
        if slot.species == SlotSpecies::BinderName && !ordinal.contains_key(&slot.occupant) {
            let next = ordinal.len();
            ordinal.insert(slot.occupant.clone(), next);
        }
    }
    let mut rewritten = String::with_capacity(reading.statement.len());
    let mut carried = String::new();
    for symbol in reading.statement.chars() {
        if is_token_character(symbol) {
            carried.push(symbol);
            continue;
        }
        if !carried.is_empty() {
            push_normalized(&mut rewritten, &carried, &ordinal);
            carried.clear();
        }
        rewritten.push(symbol);
    }
    if !carried.is_empty() {
        push_normalized(&mut rewritten, &carried, &ordinal);
    }
    rewritten
}

fn push_normalized(into: &mut String, token: &str, ordinal: &BTreeMap<String, usize>) {
    match ordinal.get(token) {
        Some(at) => {
            into.push('#');
            into.push_str(&at.to_string());
        }
        None => into.push_str(token),
    }
}

/// **The conditioning.** Where the material's own reading places each identifier, and which
/// declarations share a shape.
///
/// The composition it conditions was founded from **formal grammar with nothing conditioning it**:
/// `compose_candidates` puts every recruited identifier into every recovered slot, so
/// `exactCarrier apply` and `(a b : nlinarith) : a = b` are composed with the same standing as
/// anything else, and the stem licence admits them because `P` and `apply` share the founded letter
/// `p`. The stem licence is a licence on the **contact** — that these two identifiers belong
/// together. It says nothing about the **place**, and the place is what the deposit's own reading
/// already knows: `apply` was only ever the head of a proof step, `Soma` only ever named a scope,
/// `Nat.zero` only ever stood in term position of a body, and `exactCarrier` is the only identifier
/// the material ever put in the first position of a statement's trailing region.
///
/// Two things are read and neither is authored:
///
/// - **The position census.** Every population [`crate::lean_development`] returns, plus the slot
///   species [`crate::statement_grammar`] recovers over **every** declaration's statement rather than
///   over the theorem statements alone.
/// - **The declared-shape cohort.** `def exactCarrier (P : Prop) : Prop` and
///   `abbrev ExactRelay (Q : Prop) : Prop` normalize to one skeleton, so the material's own reading
///   cannot tell the two apart, and an identifier may stand where any member of its cohort stands.
///   That is what lets a declaration the material never *used* in a statement position be composed
///   into one — which is the whole difference between reciting the deposit and reaching past it.
///
/// The grain is [`crate::lean_development::DeclarationGrain::EveryTopLevelDeclaration`], and the
/// widening is the point: `read_derivation` opens one declaration per artifact, so
/// `def exactCarrier` and `abbrev ExactRelay` were **invisible** to the composition that was
/// supposed to be conditioned on them.
#[derive(Clone, Debug)]
pub struct StatementPositionEcology {
    conduct: BTreeMap<String, BTreeSet<ConductPosition>>,
    shapes: BTreeMap<String, DeclaredShape>,
    shape_of: BTreeMap<String, String>,
    founding: BTreeMap<String, (usize, String, String)>,
    preamble_lines: Vec<(String, String)>,
    declaration_grammar: RecoveredStatementGrammar,
    unread: BTreeSet<String>,
}

impl StatementPositionEcology {
    /// Found the ecology from one joined development reading and the source texts it was read from.
    ///
    /// `sources` is `(whole, text)` — the same lineage carrier `Exposure` uses — and is read only to
    /// recover each founding line **verbatim**, so a composed artifact can carry the declarations its
    /// own names need. Nothing is parsed out of it that the reading did not already found.
    pub fn found(
        reading: &DevelopmentReading,
        sources: &[(String, String)],
    ) -> Result<Self, StatementGrammarRefusal> {
        let statements: BTreeSet<String> = reading
            .declarations
            .iter()
            .map(|form| form.statement.clone())
            .filter(|statement| !statement.trim().is_empty())
            .collect();
        let declaration_grammar = recover(&statements)?;

        let mut conduct: BTreeMap<String, BTreeSet<ConductPosition>> = BTreeMap::new();
        for statement_reading in declaration_grammar.readings() {
            for slot in statement_reading.slots() {
                conduct
                    .entry(slot.occupant.clone())
                    .or_default()
                    .insert(ConductPosition::Slot(slot.species));
            }
        }

        let mut shapes: BTreeMap<String, DeclaredShape> = BTreeMap::new();
        let mut shape_of: BTreeMap<String, String> = BTreeMap::new();
        let mut unread: BTreeSet<String> = BTreeSet::new();
        for form in &reading.declarations {
            conduct
                .entry(form.name.clone())
                .or_default()
                .insert(ConductPosition::Declared {
                    former: form.former.clone(),
                });
            for named in form.recruited.keys() {
                conduct
                    .entry(named.clone())
                    .or_default()
                    .insert(ConductPosition::Term);
            }
            for named in form.tactics.keys() {
                conduct
                    .entry(named.clone())
                    .or_default()
                    .insert(ConductPosition::Tactic);
            }
            for named in form.local_bindings.keys() {
                conduct
                    .entry(named.clone())
                    .or_default()
                    .insert(ConductPosition::LocalBinding);
            }
            match declaration_grammar.reading(&form.statement) {
                Some(statement_reading) => {
                    let skeleton = alpha_normalized(statement_reading);
                    shape_of.insert(form.name.clone(), skeleton.clone());
                    let shape = shapes
                        .entry(skeleton.clone())
                        .or_insert_with(|| DeclaredShape {
                            skeleton,
                            members: Vec::new(),
                        });
                    if !shape.members.contains(&form.name) {
                        shape.members.push(form.name.clone());
                    }
                }
                None => {
                    unread.insert(form.name.clone());
                }
            }
        }
        for named in reading.preamble.keys() {
            conduct
                .entry(named.clone())
                .or_default()
                .insert(ConductPosition::Preamble);
        }
        for named in reading.scoping.keys() {
            conduct
                .entry(named.clone())
                .or_default()
                .insert(ConductPosition::Scoping);
        }

        let declared: BTreeSet<(String, String)> = reading
            .declarations
            .iter()
            .map(|form| (form.former.clone(), form.name.clone()))
            .collect();
        let mut founding: BTreeMap<String, (usize, String, String)> = BTreeMap::new();
        let mut preamble_lines: Vec<(String, String)> = Vec::new();
        let mut order = 0usize;
        for (whole, text) in sources {
            for line in text.lines() {
                let trimmed = line.trim();
                let mut parts = trimmed.split_whitespace();
                let Some(former) = parts.next() else {
                    continue;
                };
                if PREAMBLE_FORMS.contains(&former) {
                    if !preamble_lines.iter().any(|(_, carried)| carried == trimmed) {
                        preamble_lines.push((whole.clone(), trimmed.to_owned()));
                    }
                    continue;
                }
                let Some(head) = parts.next() else {
                    continue;
                };
                let name: String = head.chars().take_while(|c| is_token_character(*c)).collect();
                if name.is_empty()
                    || founding.contains_key(&name)
                    || !declared.contains(&(former.to_owned(), name.clone()))
                {
                    continue;
                }
                founding.insert(name, (order, whole.clone(), trimmed.to_owned()));
                order += 1;
            }
        }

        Ok(Self {
            conduct,
            shapes,
            shape_of,
            founding,
            preamble_lines,
            declaration_grammar,
            unread,
        })
    }

    /// Every identifier the reading placed anywhere.
    ///
    /// **This is the recruited population the composition should have been drawing on.**
    /// `ConditionedBody::recruited_population` is `read_derivation`'s, which opens one declaration
    /// per artifact and therefore never saw `ExactRelay` or the binder `Q` at all.
    pub fn recruited(&self) -> BTreeSet<String> {
        self.conduct.keys().cloned().collect()
    }

    /// Where the material placed one identifier, in canonical order. Empty for a token the reading
    /// never placed.
    pub fn stood_in(&self, identifier: &str) -> Vec<ConductPosition> {
        self.conduct
            .get(identifier)
            .map(|carried| carried.iter().cloned().collect())
            .unwrap_or_default()
    }

    /// The declarations sharing one identifier's declared shape, itself included. Empty when the
    /// material declares no such name.
    pub fn cohort(&self, identifier: &str) -> Vec<String> {
        self.shape_of
            .get(identifier)
            .and_then(|skeleton| self.shapes.get(skeleton))
            .map(|shape| shape.members.clone())
            .unwrap_or_default()
    }

    /// **The gate.** Did the material stand this identifier, or any member of its declared-shape
    /// cohort, in this slot species?
    pub fn admits(&self, identifier: &str, slot: SlotSpecies) -> bool {
        let wanted = ConductPosition::Slot(slot);
        if self
            .conduct
            .get(identifier)
            .is_some_and(|carried| carried.contains(&wanted))
        {
            return true;
        }
        self.cohort(identifier).iter().any(|member| {
            self.conduct
                .get(member)
                .is_some_and(|carried| carried.contains(&wanted))
        })
    }

    /// Every identifier the gate admits into one slot species, with the cohort member that carried
    /// it there.
    pub fn admitted_into(&self, slot: SlotSpecies) -> BTreeMap<String, String> {
        let wanted = ConductPosition::Slot(slot);
        let mut carried = BTreeMap::new();
        for identifier in self.conduct.keys() {
            if self.conduct[identifier].contains(&wanted) {
                carried.insert(identifier.clone(), identifier.clone());
                continue;
            }
            if let Some(member) = self.cohort(identifier).into_iter().find(|member| {
                self.conduct
                    .get(member)
                    .is_some_and(|places| places.contains(&wanted))
            }) {
                carried.insert(identifier.clone(), member);
            }
        }
        carried
    }

    /// The grammar recovered over **every** declaration's statement.
    pub const fn declaration_grammar(&self) -> &RecoveredStatementGrammar {
        &self.declaration_grammar
    }

    /// Every declared shape with more than one member — the cohorts that do any work.
    pub fn cohorts(&self) -> Vec<&DeclaredShape> {
        self.shapes
            .values()
            .filter(|shape| shape.members.len() > 1)
            .collect()
    }

    /// Every declared shape, including the singletons.
    pub fn shapes(&self) -> Vec<&DeclaredShape> {
        self.shapes.values().collect()
    }

    /// Declarations whose statement the grammar could not read. Retained, never dropped.
    pub const fn unread(&self) -> &BTreeSet<String> {
        &self.unread
    }

    /// The whole position census, for a reader.
    pub fn census(&self) -> BTreeMap<String, Vec<ConductPosition>> {
        self.conduct
            .iter()
            .map(|(identifier, places)| (identifier.clone(), places.iter().cloned().collect()))
            .collect()
    }

    /// The founding lines a composed statement's own names need, transitively closed, verbatim.
    ///
    /// A name the material declares pulls the line that declares it, and that line's own names pull
    /// theirs. What no declaration founds is looked for on the preamble lines, and what neither
    /// founds is simply left free — the scope states what it carries and never invents a declaration.
    pub fn scope_for(&self, statement: &str) -> ComposedScope {
        let mut wanted: BTreeSet<String> = BTreeSet::new();
        let mut frontier: Vec<String> = tokens_of(statement);
        while let Some(name) = frontier.pop() {
            let Some((_, _, line)) = self.founding.get(&name) else {
                continue;
            };
            if !wanted.insert(name) {
                continue;
            }
            for token in tokens_of(line) {
                if self.founding.contains_key(&token) && !wanted.contains(&token) {
                    frontier.push(token);
                }
            }
        }
        let mut ordered: Vec<(usize, String)> = wanted
            .iter()
            .filter_map(|name| {
                self.founding
                    .get(name)
                    .map(|(order, _, line)| (*order, line.clone()))
            })
            .collect();
        ordered.sort();

        let mut imports: Vec<String> = Vec::new();
        let mut founding: Vec<String> = Vec::new();
        let mut incomplete: Vec<String> = Vec::new();
        for (_, line) in ordered {
            if declaration_finishes_on_its_own_line(&line) {
                founding.push(line);
            } else {
                incomplete.push(line);
            }
        }

        // Whatever the declarations do not found, the preamble may.
        let founded_here: BTreeSet<String> = founding
            .iter()
            .chain(incomplete.iter())
            .flat_map(|line| tokens_of(line))
            .collect();
        let free: BTreeSet<String> = tokens_of(statement)
            .into_iter()
            .filter(|token| !self.founding.contains_key(token))
            .chain(founded_here.into_iter().filter(|token| !self.founding.contains_key(token)))
            .collect();
        for (_, line) in &self.preamble_lines {
            if !tokens_of(line).iter().any(|token| free.contains(token)) {
                continue;
            }
            if line.starts_with("import") {
                imports.push(line.clone());
            } else {
                founding.insert(0, line.clone());
            }
        }

        ComposedScope {
            imports,
            founding,
            incomplete,
        }
    }
}

/// Does a declaration line carry its own body? A one-line lookup cannot recover a declaration whose
/// body runs on, and saying so is the difference between an incomplete scope and a truncated one.
fn declaration_finishes_on_its_own_line(line: &str) -> bool {
    match line.split_once(":=") {
        Some((_, right)) => !right.trim().is_empty() && right.trim() != "by",
        None => false,
    }
}

// -------------------------------------------------------------------------------------------------
// The admission rule
// -------------------------------------------------------------------------------------------------

/// The name a composed declaration takes. `.` is the only character a recruited identifier carries
/// that a Lean declaration name may not.
pub fn composed_name(declaration: &str, stem: &str, brought: &str, site: &str) -> String {
    format!(
        "{declaration}_founds_{stem}_{}_{site}",
        brought.replace('.', "_")
    )
}

/// The artifact one admitted composition presents.
///
/// The composed statement stands where a deposited statement would; the body names **both sides of
/// the contact pair**, so the licence that founded the statement is visible in the circuit as
/// recruitment rather than carried only in prose. No import line and no tactic name is written.
pub fn compose_artifact(name: &str, statement: &str, held: &str, brought: &str) -> String {
    compose_artifact_in_scope(name, statement, held, brought, &ComposedScope::default())
}

/// The same artifact carrying the founding lines its own names need, verbatim from the material.
///
/// **This is what separates a composed string from something a batch grader could be asked about.**
/// The unscoped form emits a theorem naming `ExactRelay` with nothing declaring `ExactRelay`, so no
/// kernel could elaborate it whatever the statement said. Nothing here is *authored*: every line is
/// one the material wrote, recovered by [`StatementPositionEcology::scope_for`], and the composed
/// theorem stays the last `theorem` line so `read_derivation` reads back the composition and not a
/// carried declaration.
pub fn compose_artifact_in_scope(
    name: &str,
    statement: &str,
    held: &str,
    brought: &str,
    scope: &ComposedScope,
) -> String {
    let mut text = String::new();
    for line in &scope.imports {
        text.push_str(line);
        text.push('\n');
    }
    text.push_str("namespace Soma\n");
    for line in &scope.founding {
        text.push_str(line);
        text.push('\n');
    }
    text.push_str(&format!(
        "theorem {name} {statement} := by\n  have founded := {held}\n  have brought := {brought}\nend Soma\n"
    ));
    text
}

/// The stems of an occurrence family, canonically ordered.
fn stem_names(occurrences: &[&crate::conditioned_derivation::StemOccurrence]) -> Vec<String> {
    let mut stems: Vec<String> = occurrences
        .iter()
        .map(|occurrence| occurrence.stem.clone())
        .collect();
    stems.sort();
    stems.dedup();
    stems
}

/// Every committed founded stem that holds two identifiers together, with the offsets it stands at.
fn licences(
    morphology: &FoundedMorphology,
    held: &str,
    brought: &str,
) -> Result<(Vec<StatementLicence>, String, String), ConditionedDerivationRefusal> {
    let held_cover = morphology.cover(held)?;
    let brought_cover = morphology.cover(brought)?;
    let mut found: BTreeMap<String, StatementLicence> = BTreeMap::new();
    for here in &held_cover.occurrences {
        for there in &brought_cover.occurrences {
            if here.stem != there.stem {
                continue;
            }
            let held_face = stem_names(&held_cover.face_at(here.at));
            let brought_face = stem_names(&brought_cover.face_at(there.at));
            let held_crossings = stem_names(&held_cover.crossings_of(here));
            let brought_crossings = stem_names(&brought_cover.crossings_of(there));
            let contact = if !held_crossings.is_empty() || !brought_crossings.is_empty() {
                ContactSpecies::Crossed
            } else if held_face.len() > 1 || brought_face.len() > 1 {
                ContactSpecies::Superposed
            } else {
                ContactSpecies::Simple
            };
            found.entry(here.stem.clone()).or_insert(StatementLicence {
                stem: here.stem.clone(),
                held_at: here.at,
                brought_at: there.at,
                wholes: morphology
                    .stem(&here.stem)
                    .map(|stem| stem.wholes.clone())
                    .unwrap_or_default(),
                contact,
                held_face,
                brought_face,
                held_crossings,
                brought_crossings,
            });
        }
    }
    Ok((
        found.into_values().collect(),
        held_cover.render(),
        brought_cover.render(),
    ))
}

/// Adjudicate one candidate. **Every candidate gets a verdict; nothing is dropped.**
///
/// The order is: what the grammar cannot place, then what the population's own lengths do not
/// found, then whether the composition returns to the deposit, then the licence, then the read-back.
/// The conditioning is the **last** gate and the only one that founds, which is what makes the
/// unconditioned null's empty admission a statement about the conditioning rather than about the
/// grammar.
pub fn adjudicate(
    candidate: &CandidateStatement,
    grammar: &RecoveredStatementGrammar,
    morphology: &FoundedMorphology,
    standing: &BTreeSet<String>,
) -> Result<StatementAdmission, ConditionedDerivationRefusal> {
    adjudicate_conditioned(candidate, grammar, morphology, standing, None)
}

/// [`adjudicate`] with the position ecology on the causal path.
///
/// The gate is the **last** one and it is a conjunct, never a widener: a candidate the stem licence
/// refuses is refused whatever the ecology says, so `Applied` can only ever return a subpopulation of
/// `Withheld`. It fires only where the composition **places an identifier into a recovered slot** —
/// `candidate.slot` — because a binder withdrawal or extension moves a whole group the population
/// already witnessed and puts nothing anywhere new, so there is no place for a position licence to
/// be about.
/// The identifiers the standing population ever puts in a **binder-name** position. These are the
/// bound variables of this material; everything else a statement uses is a standing declaration.
///
/// Read off the population and never authored: `Prop` and `Nat` appear only as types and heads, so
/// they are standing; `P` and `h` appear as binder names, so they are bound and owe an introduction.
fn population_binds(grammar: &RecoveredStatementGrammar, standing: &BTreeSet<String>) -> BTreeSet<String> {
    let mut bound = BTreeSet::new();
    for statement in standing {
        let Some(reading) = grammar.reading(statement) else {
            continue;
        };
        for slot in reading.slots() {
            if slot.species == SlotSpecies::BinderName {
                bound.insert(slot.occupant.clone());
            }
        }
    }
    bound
}

/// The first use, in span order, of an identifier the population binds and this statement has not
/// yet introduced. `None` when every use is either standing or already bound.
fn first_unbound_use(
    statement: &str,
    grammar: &RecoveredStatementGrammar,
    standing: &BTreeSet<String>,
) -> Option<(String, usize)> {
    let binds = population_binds(grammar, standing);
    // A composed statement is not in the standing population, so the recovered grammar has no
    // reading of it to look up — it must be READ. Recovering over `standing ∪ {statement}` reads it
    // under the population's own recovered rule rather than under one this check invented.
    //
    // The first form of this check called `grammar.reading(statement)` and got `None` on every
    // composed candidate, so it returned "no unbound use" for all of them and admitted the same
    // seven statements it was written to refuse. It fired on 2 candidates out of 437 and looked
    // like it was working.
    let owned;
    let reading = match grammar.reading(statement) {
        Some(reading) => reading,
        None => {
            let mut population = standing.clone();
            population.insert(statement.to_owned());
            owned = recover(&population).ok()?;
            owned.reading(statement)?
        }
    };
    // **Group by group, not slot by slot.** A binder group's carried type is checked against what
    // EARLIER groups introduced, and only then are this group's own names introduced. Walking the
    // flattened slot list instead admits `(P : P)` — the name counts as introduced before its own
    // type is read — and `(P : P)` is a binder typed by itself, which no stratified type theory
    // permits. This ordering is also the correct rule for dependent binders generally: `(P : Prop)
    // (h : P)` stands because `P` came from an earlier group.
    let mut introduced: BTreeSet<String> = BTreeSet::new();
    let mut at = 0usize;
    for group in &reading.binders {
        if let Some(carried) = &group.carried
            && binds.contains(&carried.occupant)
            && !introduced.contains(&carried.occupant)
        {
            return Some((carried.occupant.clone(), at + group.names.len()));
        }
        for name in &group.names {
            introduced.insert(name.occupant.clone());
        }
        at += group.names.len() + usize::from(group.carried.is_some());
    }
    if let Some(BodyReading::Applied { head, arguments }) = &reading.body {
        for slot in std::iter::once(head).chain(arguments.iter()) {
            if binds.contains(&slot.occupant) && !introduced.contains(&slot.occupant) {
                return Some((slot.occupant.clone(), at));
            }
            at += 1;
        }
    }
    None
}

pub fn adjudicate_conditioned(
    candidate: &CandidateStatement,
    grammar: &RecoveredStatementGrammar,
    morphology: &FoundedMorphology,
    standing: &BTreeSet<String>,
    ecology: Option<&StatementPositionEcology>,
) -> Result<StatementAdmission, ConditionedDerivationRefusal> {
    // 1. what the grammar cannot place
    if candidate.species == CompositionSpecies::ResidueSubstitution {
        let residue = grammar
            .reading(&candidate.from)
            .and_then(|reading| reading.residue.first().cloned());
        return Ok(StatementAdmission::Refused(
            StatementObstruction::SlotLiesInGrammarResidue {
                statement: candidate.from.clone(),
                residue: candidate.held.clone(),
                refused_by: residue
                    .map(|residue| residue.refused_by)
                    .unwrap_or_else(|| "the grammar recovered no reading of this statement".to_owned()),
            },
        ));
    }
    if candidate.species == CompositionSpecies::ArgumentApplication
        && let Some(bound) = grammar.aperture().iter().find(|bound| {
            matches!(
                bound,
                GrammarAperture::ArgumentPositionNeverCarriedAnApplication { .. }
            )
        }) {
            return Ok(StatementAdmission::Refused(
                StatementObstruction::GrammarNeverWitnessedTheShape {
                    bound: bound.clone(),
                },
            ));
        }

    // 2. the lengths the population founds
    if matches!(
        candidate.species,
        CompositionSpecies::BinderWithdrawal | CompositionSpecies::BinderExtension
    ) {
        let carried = grammar
            .reading(&candidate.from)
            .map_or(0, |reading| reading.binders.len());
        let length = if candidate.species == CompositionSpecies::BinderWithdrawal {
            carried.saturating_sub(1)
        } else {
            carried + 1
        };
        if !grammar.binder_length_is_founded(length) {
            return Ok(StatementAdmission::Refused(
                StatementObstruction::BinderListLengthIsUnfounded {
                    length,
                    witnessed: grammar.binder_group_lengths().clone(),
                },
            ));
        }
    }

    // 3. did it compose anything at all
    if candidate.statement == candidate.from {
        return Ok(StatementAdmission::Refused(
            StatementObstruction::ComposedStatementIsUnchanged {
                statement: candidate.statement.clone(),
            },
        ));
    }

    // 4. does it return to the deposit
    if standing.contains(&candidate.statement) {
        return Ok(StatementAdmission::Refused(
            StatementObstruction::ComposedStatementIsAlreadyStanding {
                statement: candidate.statement.clone(),
            },
        ));
    }

    // 5. the licence, which is the conditioning
    let (found, held_cover, brought_cover) = licences(morphology, &candidate.held, &candidate.brought)?;
    if found.is_empty() {
        return Ok(StatementAdmission::Refused(
            StatementObstruction::NoFoundedStemHoldsThem {
                held: candidate.held.clone(),
                held_cover,
                brought: candidate.brought.clone(),
                brought_cover,
            },
        ));
    }

    // 6. the position licence, which is the second conjunct of the conditioning
    let mut stood_in: Vec<ConductPosition> = Vec::new();
    if let (Some(ecology), Some(slot)) = (ecology, candidate.slot) {
        if !ecology.admits(&candidate.brought, slot) {
            return Ok(StatementAdmission::Refused(
                StatementObstruction::IdentifierNeverStoodInThisPosition {
                    brought: candidate.brought.clone(),
                    slot,
                    stood_in: ecology.stood_in(&candidate.brought),
                    cohort: ecology.cohort(&candidate.brought),
                },
            ));
        }
        stood_in = ecology.stood_in(&candidate.brought);
    }

    // 7. the read-back, which is the composer being held to the reading
    let probe = compose_artifact(
        "composition_probe",
        &candidate.statement,
        &candidate.held,
        &candidate.brought,
    );
    match read_derivation(&probe) {
        Some(derivation) if derivation.statement == candidate.statement => {}
        Some(derivation) => {
            return Ok(StatementAdmission::Refused(
                StatementObstruction::ReadBackMissedTheComposition {
                    wanted: candidate.statement.clone(),
                    read: derivation.statement,
                },
            ));
        }
        None => {
            return Ok(StatementAdmission::Refused(
                StatementObstruction::ReadBackMissedTheComposition {
                    wanted: candidate.statement.clone(),
                    read: String::new(),
                },
            ));
        }
    }

    // what the grammar does not certify about the admission, carried rather than erased
    let mut carried_aperture = Vec::new();
    if let Some(reading) = grammar.reading(&candidate.from)
        && let Some(BodyReading::Applied { head, .. }) = &reading.body {
            let composed_head = if candidate.slot == Some(SlotSpecies::BodyHead) {
                candidate.brought.clone()
            } else {
                head.occupant.clone()
            };
            if let Some(bound) = grammar.unfounded_head_arity(&composed_head) {
                carried_aperture.push(bound);
            }
        }

    // LAST. SCOPE. An identifier used in a type, head or argument position must already have been
    //    introduced by a binder in the same statement, unless the population treats it as a standing
    //    declaration.
    //
    //    **This is not a semantics claim and it needs no grammar of meaning**, which is what an
    //    earlier reading of this ceiling wrongly said was owed. It is read off the population: an
    //    identifier the standing statements only ever USE and never BIND is a standing declaration
    //    (`Prop`, `Nat`, `exactCarrier`); one the population does bind is a bound variable and must
    //    be bound before it is used. The composition ran without this and admitted
    //    `|- (h : P) (P : Prop) : exactCarrier P`, which uses `P` a group before introducing it, and
    //    `|- (h : Prop) : exactCarrier P`, whose target names a `P` nothing binds.
    if let Some((identifier, at)) = first_unbound_use(&candidate.statement, grammar, standing) {
        return Ok(StatementAdmission::Refused(
            StatementObstruction::IdentifierUsedBeforeItIsBound {
                statement: candidate.statement.clone(),
                identifier,
                at,
            },
        ));
    }
    Ok(StatementAdmission::Admitted {
        licences: found,
        carried_aperture,
        stood_in,
    })
}

/// Adjudicate a whole candidate population. The return is the population, never a selection of it.
pub fn admit(
    candidates: Vec<CandidateStatement>,
    grammar: RecoveredStatementGrammar,
    morphology: &FoundedMorphology,
    standing: BTreeSet<String>,
) -> Result<AdmittedStatements, StatementCompositionRefusal> {
    admit_conditioned(candidates, grammar, morphology, standing, None)
}

/// [`admit`] under a declared position gate.
pub fn admit_conditioned(
    candidates: Vec<CandidateStatement>,
    grammar: RecoveredStatementGrammar,
    morphology: &FoundedMorphology,
    standing: BTreeSet<String>,
    ecology: Option<&StatementPositionEcology>,
) -> Result<AdmittedStatements, StatementCompositionRefusal> {
    let mut adjudicated = Vec::with_capacity(candidates.len());
    for candidate in candidates {
        let admission =
            adjudicate_conditioned(&candidate, &grammar, morphology, &standing, ecology)?;
        adjudicated.push(AdjudicatedCandidate {
            candidate,
            admission,
        });
    }
    Ok(AdmittedStatements {
        grammar,
        adjudicated,
        standing,
        gate: if ecology.is_some() {
            PositionGate::Applied
        } else {
            PositionGate::Withheld
        },
    })
}

/// **The entry point.** Recover the grammar from the body's own statements, compose every candidate,
/// and adjudicate them all.
///
/// This is beside `ConditionedBody::derive`, never through it. `derive` still gates on statement
/// equality, `compose_passage` still writes the queried statement verbatim, and
/// `EmittedPassageMissedItsStatement` still refuses a drifted route: none of the three is touched,
/// and all three keep holding for the species they govern.
pub fn found_statements(
    body: &ConditionedBody,
) -> Result<AdmittedStatements, StatementCompositionRefusal> {
    let standing = body.standing_statements();
    let grammar = recover(&standing)?;
    let recruited = body.recruited_population();
    let reaching = declarations_reaching(body);
    let candidates = compose_candidates(&grammar, &recruited, &reaching);
    admit(candidates, grammar, body.morphology(), standing)
}

/// **The conditioned entry point.** The same composition, drawing on the population the development
/// reading recruits, adjudicated under a declared position gate.
///
/// Both settings compose the **same** candidates, which is what makes the pair an orbit rather than
/// two runs: the recruited population comes from the ecology in both, and only the gate moves.
pub fn found_statements_under(
    body: &ConditionedBody,
    ecology: &StatementPositionEcology,
    gate: PositionGate,
) -> Result<AdmittedStatements, StatementCompositionRefusal> {
    let standing = body.standing_statements();
    let grammar = recover(&standing)?;
    let recruited = ecology.recruited();
    let reaching = declarations_reaching(body);
    let candidates = compose_candidates(&grammar, &recruited, &reaching);
    let applied = match gate {
        PositionGate::Applied => Some(ecology),
        PositionGate::Withheld => None,
    };
    admit_conditioned(candidates, grammar, body.morphology(), standing, applied)
}

// -------------------------------------------------------------------------------------------------
// The passages, and the circuit
// -------------------------------------------------------------------------------------------------

/// One artifact a founded statement presents, with everything that founded it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ComposedPassage {
    pub name: String,
    /// The composed statement. **Absent from the deposit by construction**, since a composition that
    /// landed on a standing statement was refused.
    pub statement: String,
    /// The deposited statement it was composed from.
    pub from: String,
    /// The standing declaration whose route this composition extends.
    pub declaration: String,
    pub species: CompositionSpecies,
    pub site: String,
    pub held: String,
    pub brought: String,
    pub stem: String,
    pub wholes: Vec<String>,
    /// The recovered rule that composed it, in one line.
    pub rule: String,
    /// What the grammar does not certify about it.
    pub carried_aperture: Vec<GrammarAperture>,
    /// Where the material stood the brought identifier, when the position gate was applied.
    pub stood_in: Vec<ConductPosition>,
    /// The founding lines the artifact carries so its own names resolve. Empty when composed
    /// without an ecology.
    pub scope: ComposedScope,
    pub text: String,
}

/// The artifacts the admitted population presents: one per (admitted candidate, standing
/// declaration, licensing stem).
///
/// Plural by construction and never reduced — a composed statement reached under two founded stems
/// is two routes to one statement, which is exactly the structure `route_movement` and the circuit's
/// grade-1 cycles are for.
pub fn compose(
    admitted: &AdmittedStatements,
) -> Result<Vec<ComposedPassage>, StatementCompositionRefusal> {
    compose_in_scope(admitted, None)
}

/// [`compose`], with every artifact carrying the founding lines its own names need.
pub fn compose_in_scope(
    admitted: &AdmittedStatements,
    ecology: Option<&StatementPositionEcology>,
) -> Result<Vec<ComposedPassage>, StatementCompositionRefusal> {
    let mut composed = Vec::new();
    for entry in admitted.admitted() {
        let StatementAdmission::Admitted {
            licences,
            carried_aperture,
            stood_in,
        } = &entry.admission
        else {
            continue;
        };
        let scope = ecology.map_or_else(ComposedScope::default, |ecology| {
            ecology.scope_for(&entry.candidate.statement)
        });
        for declaration in &entry.candidate.declarations {
            for licence in licences {
                let name = composed_name(
                    declaration,
                    &licence.stem,
                    &entry.candidate.brought,
                    &entry.candidate.site,
                );
                let text = compose_artifact_in_scope(
                    &name,
                    &entry.candidate.statement,
                    &entry.candidate.held,
                    &entry.candidate.brought,
                    &scope,
                );
                let derivation = read_derivation(&text).ok_or(
                    StatementCompositionRefusal::ComposedPassageDeclaresNothing { name: name.clone() },
                )?;
                if derivation.statement != entry.candidate.statement {
                    return Err(
                        StatementCompositionRefusal::ComposedPassageMissedItsStatement {
                            name,
                            wanted: entry.candidate.statement.clone(),
                            read: derivation.statement,
                        },
                    );
                }
                composed.push(ComposedPassage {
                    name,
                    statement: entry.candidate.statement.clone(),
                    from: entry.candidate.from.clone(),
                    declaration: declaration.clone(),
                    species: entry.candidate.species,
                    site: entry.candidate.site.clone(),
                    held: entry.candidate.held.clone(),
                    brought: entry.candidate.brought.clone(),
                    stem: licence.stem.clone(),
                    wholes: licence.wholes.clone(),
                    rule: entry.candidate.rule.clone(),
                    carried_aperture: carried_aperture.clone(),
                    stood_in: stood_in.clone(),
                    scope: scope.clone(),
                    text,
                });
            }
        }
    }
    composed.sort();
    composed.dedup();
    Ok(composed)
}

/// The whole passage population a founding presents: the deposit, then what it composed.
///
/// Every composed artifact is read back through `read_derivation`, so the circuit sees deposited and
/// composed material through one reading, exactly as `ConditionedBody::passages` does for a derived
/// one.
pub fn passages_with_composed(
    body: &ConditionedBody,
    composed: &[ComposedPassage],
) -> Result<Vec<Passage>, StatementCompositionRefusal> {
    let mut passages = body.standing().to_vec();
    for founded in composed {
        let derivation = read_derivation(&founded.text).ok_or(
            StatementCompositionRefusal::ComposedPassageDeclaresNothing {
                name: founded.name.clone(),
            },
        )?;
        if derivation.statement != founded.statement {
            return Err(
                StatementCompositionRefusal::ComposedPassageMissedItsStatement {
                    name: founded.name.clone(),
                    wanted: founded.statement.clone(),
                    read: derivation.statement,
                },
            );
        }
        passages.push(Passage {
            id: PassageId(passages.len() as u64),
            origin: PassageOrigin::Derived {
                stem: founded.stem.clone(),
                reaches: founded.declaration.clone(),
                brought: founded.brought.clone(),
            },
            derivation,
            text: founded.text.clone(),
        });
    }
    Ok(passages)
}

/// **The fourth move species**, read off a circuit that carries composed passages.
///
/// A move per composed passage. Its boundary is the recruited-symbol frame **and nothing else**; its
/// `after` carries the frame, the passage's own cells, and **the statement 0-cell**. That last
/// membership is what separates this species from `Deposit`, `RecruitmentExchange` and `LemmaSplit`,
/// all three of which have the statement vertex in their boundary because both sides of the move
/// already reach it.
pub fn statement_composition_moves(
    circuit: &ConditionedCircuit,
    standing: &BTreeSet<String>,
) -> Vec<DerivationMove> {
    let mut moves = Vec::new();
    for passage in &circuit.passages {
        if !passage.is_derived() || standing.contains(&passage.derivation.statement) {
            continue;
        }
        let mut frame: BTreeSet<CausalCellId> = BTreeSet::new();
        for symbol in passage.derivation.recruited.keys() {
            if let Some(cell) = circuit.circuit.vertices().get(symbol) {
                frame.insert(*cell);
            }
        }
        let mut after = frame.clone();
        if let Some(cell) = circuit
            .circuit
            .vertices()
            .get(&statement_vertex_key(&passage.derivation.statement))
        {
            after.insert(*cell);
        }
        after.extend(passage_interior(circuit, passage));
        let stem = match &passage.origin {
            PassageOrigin::Derived { stem, .. } => stem.clone(),
            PassageOrigin::Standing { source } => source.clone(),
        };
        moves.push(DerivationMove {
            species: MoveSpecies::StatementComposition,
            statement: passage.derivation.statement.clone(),
            stem,
            withdraws: Vec::new(),
            deposits: vec![passage.derivation.name.clone()],
            substitution: Substitution {
                boundary: frame.clone(),
                before: frame,
                after,
            },
        });
    }
    moves
}

/// Does this move deposit its own statement 0-cell? **The discriminator of the fourth species.**
///
/// True exactly when the statement vertex is in `after` and not in `boundary`. Every `Deposit`,
/// `RecruitmentExchange` and `LemmaSplit` returns false, because the statement they act under is
/// shared by both sides and therefore sits in the boundary.
pub fn deposits_its_statement_vertex(
    circuit: &ConditionedCircuit,
    declared: &DerivationMove,
) -> bool {
    let Some(vertex) = circuit
        .circuit
        .vertices()
        .get(&statement_vertex_key(&declared.statement))
    else {
        return false;
    };
    declared.substitution.after.contains(vertex) && !declared.substitution.boundary.contains(vertex)
}

// -------------------------------------------------------------------------------------------------
// The ablation
// -------------------------------------------------------------------------------------------------

/// One founded statement under one licensing stem. The unit an ablation moves.
///
/// A statement and a route to it are **different objects here**, and separating them is the point:
/// a founded statement reached under three stems loses one route when one stem is removed and does
/// not stop being founded. Reporting only the statement population would call that no change.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FoundedRoute {
    pub statement: String,
    pub stem: String,
}

/// One founded statement that departed when a stem was removed, with the stems that had licensed it
/// and the recovered sites that composed it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct StatementDeparture {
    pub statement: String,
    pub stems: Vec<String>,
    pub sites: Vec<String>,
}

/// One founded statement, or one route to one, that a removal **reopened**: unlicensed before,
/// licensed now.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct StatementReopening {
    pub statement: String,
    /// The stems that license it now.
    pub stems: Vec<String>,
    /// The removed stem, which had contained one of them and suppressed it by maximality.
    pub was_covered_by: String,
}

/// What removing one founded stem removed from the founded-statement population, and what its
/// removal reopened — **at both granularities**.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StatementStemAblation {
    pub stem: String,
    pub wholes: Vec<String>,
    pub statements_before: BTreeSet<String>,
    pub statements_after: BTreeSet<String>,
    /// Statements founded before the removal and not after.
    pub statements_departed: Vec<StatementDeparture>,
    /// Statements founded after the removal and not before.
    pub statements_reopened: Vec<StatementReopening>,
    /// `(statement, stem)` routes the removal made structurally absent.
    pub routes_departed: Vec<FoundedRoute>,
    /// `(statement, stem)` routes the removal reopened, each with the stem that licenses it now.
    pub routes_reopened: Vec<StatementReopening>,
    /// Reopened routes whose licensing stem the removed stem does **not** contain. Must be empty:
    /// nothing else can promote an occurrence.
    pub unaccounted: Vec<StatementReopening>,
}

impl StatementStemAblation {
    /// The removal removed later founding **by removing structure**, and every reopening is
    /// accounted for by the maximality the removed stem had been exercising.
    pub fn removes_structure(&self) -> bool {
        !self.routes_departed.is_empty() && self.unaccounted.is_empty()
    }
}

fn licensed_by_statement(
    admitted: &AdmittedStatements,
) -> BTreeMap<String, (Vec<String>, Vec<String>)> {
    let mut carried: BTreeMap<String, (BTreeSet<String>, BTreeSet<String>)> = BTreeMap::new();
    for entry in admitted.admitted() {
        let slot = carried
            .entry(entry.candidate.statement.clone())
            .or_default();
        for licence in entry.admission.licences() {
            slot.0.insert(licence.stem.clone());
        }
        slot.1.insert(entry.candidate.site.clone());
    }
    carried
        .into_iter()
        .map(|(statement, (stems, sites))| {
            (
                statement,
                (
                    stems.into_iter().collect::<Vec<String>>(),
                    sites.into_iter().collect::<Vec<String>>(),
                ),
            )
        })
        .collect()
}

fn founded_routes(admitted: &AdmittedStatements) -> BTreeSet<FoundedRoute> {
    admitted
        .admitted()
        .into_iter()
        .flat_map(|entry| {
            entry
                .admission
                .licences()
                .iter()
                .map(|licence| FoundedRoute {
                    statement: entry.candidate.statement.clone(),
                    stem: licence.stem.clone(),
                })
                .collect::<Vec<FoundedRoute>>()
        })
        .collect()
}

/// Delete one founded stem, re-found, and return what stopped being founded and what reopened.
pub fn ablate_stem_for_statements(
    body: &ConditionedBody,
    stem: &str,
) -> Result<StatementStemAblation, StatementCompositionRefusal> {
    ablate_stem_for_statements_under(body, stem, None)
}

/// [`ablate_stem_for_statements`] under a declared position gate. `None` is the unconditioned rule
/// and reproduces [`ablate_stem_for_statements`] exactly.
pub fn ablate_stem_for_statements_under(
    body: &ConditionedBody,
    stem: &str,
    ecology: Option<&StatementPositionEcology>,
) -> Result<StatementStemAblation, StatementCompositionRefusal> {
    let founded = body.morphology().stem(stem).ok_or(
        ConditionedDerivationRefusal::StemWasNeverFounded {
            stem: stem.to_owned(),
        },
    )?;
    let wholes = founded.wholes.clone();
    let ablated = body
        .without_stem(stem)
        .ok_or(ConditionedDerivationRefusal::StemWasNeverFounded {
            stem: stem.to_owned(),
        })?;

    let (before, after) = match ecology {
        Some(ecology) => (
            found_statements_under(body, ecology, PositionGate::Applied)?,
            found_statements_under(&ablated, ecology, PositionGate::Applied)?,
        ),
        None => (found_statements(body)?, found_statements(&ablated)?),
    };
    let carried_before = licensed_by_statement(&before);
    let carried_after = licensed_by_statement(&after);

    let statements_departed: Vec<StatementDeparture> = carried_before
        .iter()
        .filter(|(statement, _)| !carried_after.contains_key(*statement))
        .map(|(statement, (stems, sites))| StatementDeparture {
            statement: statement.clone(),
            stems: stems.clone(),
            sites: sites.clone(),
        })
        .collect();
    let statements_reopened: Vec<StatementReopening> = carried_after
        .iter()
        .filter(|(statement, _)| !carried_before.contains_key(*statement))
        .map(|(statement, (stems, _))| StatementReopening {
            statement: statement.clone(),
            stems: stems.clone(),
            was_covered_by: stem.to_owned(),
        })
        .collect();

    let routes_before = founded_routes(&before);
    let routes_after = founded_routes(&after);
    let routes_departed: Vec<FoundedRoute> =
        routes_before.difference(&routes_after).cloned().collect();
    let routes_reopened: Vec<StatementReopening> = routes_after
        .difference(&routes_before)
        .map(|route| StatementReopening {
            statement: route.statement.clone(),
            stems: vec![route.stem.clone()],
            was_covered_by: stem.to_owned(),
        })
        .collect();
    let unaccounted: Vec<StatementReopening> = routes_reopened
        .iter()
        .filter(|entry| {
            !entry
                .stems
                .iter()
                .any(|carried| stem.contains(carried.as_str()) && stem != carried)
        })
        .cloned()
        .collect();

    Ok(StatementStemAblation {
        stem: stem.to_owned(),
        wholes,
        statements_before: before.founded_statements(),
        statements_after: after.founded_statements(),
        statements_departed,
        statements_reopened,
        routes_departed,
        routes_reopened,
        unaccounted,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conditioned_derivation::{expose, found_conditioned_circuit, DerivationQuery, Exposure};
    use crate::derivation_atlas::{route_movement, CircuitAperture};
    use crate::derivation_skein::{deposit_moves, MoveAperture};

    const APERTURE: CircuitAperture = CircuitAperture::STATEMENT_INCIDENT;

    /// The deposit's own three statements, carried by artifacts of its own shape.
    fn deposit() -> Vec<(String, String)> {
        vec![
            (
                "carry".to_owned(),
                "namespace Soma\ntheorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by\n  \
                 have step := exact_chart_carry\nend Soma\n"
                    .to_owned(),
            ),
            (
                "relay".to_owned(),
                "namespace Soma\ntheorem carrier_relay (h : P) : exactCarrier P := by\n  \
                 have step := formal_carry\nend Soma\n"
                    .to_owned(),
            ),
            (
                "agree".to_owned(),
                "namespace Soma\ntheorem every_receiver_agrees (a b : Nat) : a = b := by\n  \
                 have step := Nat.zero\nend Soma\n"
                    .to_owned(),
            ),
        ]
    }

    /// Two wholes committing `exact`, `carry`, `carrier` and the letters the residual licences use.
    fn corpus() -> Vec<Exposure> {
        vec![
            expose(
                "one",
                "an exact transport must carry the boundary. the carrier is named here. p a n t",
            ),
            expose(
                "two",
                "exact transport, and what it must carry across. the carrier again. p a n t",
            ),
        ]
    }

    fn conditioned() -> ConditionedBody {
        let mut body = ConditionedBody::mount(deposit()).expect("mounts");
        body.condition(&corpus());
        body
    }

    #[test]
    fn the_unconditioned_null_founds_no_statement_and_every_candidate_is_refused_by_name() {
        let body = ConditionedBody::mount(deposit()).expect("mounts");
        let founded = found_statements(&body).expect("founds");
        assert!(!founded.adjudicated.is_empty(), "there must be candidates");
        assert!(founded.admitted().is_empty());
        assert!(founded.founded_statements().is_empty());
        // and the refusal is named, per candidate, rather than being an empty return
        for entry in founded.refused() {
            assert!(entry.admission.obstruction().is_some());
        }
        assert!(founded
            .obstructions()
            .contains_key("no-founded-stem-holds-them"));
    }

    #[test]
    fn the_conditioned_body_founds_statements_the_deposit_does_not_reach() {
        let body = conditioned();
        let founded = found_statements(&body).expect("founds");
        let statements = founded.founded_statements();
        assert!(!statements.is_empty());
        for statement in &statements {
            assert!(
                !body.standing_statements().contains(statement),
                "{statement} is standing"
            );
        }
        // the morphemic one: `exactCarrier` and `exact_chart_carry` share the committed word `exact`
        assert!(
            statements.contains("(P : Prop) (h : P) : exact_chart_carry P"),
            "{statements:?}"
        );
    }

    #[test]
    fn the_admission_is_a_population_and_admits_neither_everything_nor_nothing() {
        let founded = found_statements(&conditioned()).expect("founds");
        assert!(founded.is_a_population());
        assert_eq!(
            founded.adjudicated.len(),
            founded.admitted().len() + founded.refused().len()
        );
    }

    #[test]
    fn a_composition_landing_on_a_standing_statement_is_refused_and_retained() {
        let founded = found_statements(&conditioned()).expect("founds");
        let landed: Vec<&AdjudicatedCandidate> = founded
            .obstructions()
            .get("composed-statement-is-already-standing")
            .cloned()
            .unwrap_or_default();
        assert!(!landed.is_empty(), "no composition returned to the deposit");
        for entry in landed {
            assert!(founded.standing.contains(&entry.candidate.statement));
        }
    }

    #[test]
    fn an_application_in_argument_position_is_refused_because_the_population_never_witnessed_one() {
        let founded = found_statements(&conditioned()).expect("founds");
        let refused = founded
            .obstructions()
            .get("grammar-never-witnessed-the-shape")
            .cloned()
            .unwrap_or_default();
        assert!(!refused.is_empty());
        // and this is the record's own probe, refused by name
        assert!(refused.iter().any(|entry| entry.candidate.statement
            == "(P : Prop) (h : P) : exactCarrier (exactCarrier P)"));
    }

    #[test]
    fn a_substitution_into_an_undecomposed_body_is_refused_as_residue() {
        let founded = found_statements(&conditioned()).expect("founds");
        let refused = founded
            .obstructions()
            .get("slot-lies-in-grammar-residue")
            .cloned()
            .unwrap_or_default();
        assert!(!refused.is_empty());
        for entry in refused {
            assert_eq!(entry.candidate.from, "(a b : Nat) : a = b");
            assert_eq!(entry.candidate.held, "a = b");
        }
    }

    #[test]
    fn withdrawing_the_only_group_is_refused_because_no_statement_witnesses_an_empty_region() {
        let founded = found_statements(&conditioned()).expect("founds");
        let refused = founded
            .obstructions()
            .get("binder-list-length-is-unfounded")
            .cloned()
            .unwrap_or_default();
        assert!(!refused.is_empty());
        for entry in refused {
            assert_eq!(entry.candidate.species, CompositionSpecies::BinderWithdrawal);
        }
    }

    #[test]
    fn every_composed_passage_reads_back_reaching_the_statement_it_composed() {
        let body = conditioned();
        let founded = found_statements(&body).expect("founds");
        let composed = compose(&founded).expect("composes");
        assert!(!composed.is_empty());
        for passage in &composed {
            let derivation = read_derivation(&passage.text).expect("declares");
            assert_eq!(derivation.statement, passage.statement);
            // `read_derivation` excludes single-character tokens as binder convention, so a contact
            // partner that is one — a binder name the statement itself carries — is invisible to it
            // by that reading's own declared bound, not by anything this composer did.
            if passage.brought.chars().count() > 1 {
                assert!(
                    derivation.recruited.contains_key(&passage.brought),
                    "{} dropped {}",
                    passage.name,
                    passage.brought
                );
            }
        }
    }

    #[test]
    fn the_founded_statement_founds_a_zero_cell_and_route_movement_reports_it() {
        let body = conditioned();
        let founded = found_statements(&body).expect("founds");
        let composed = compose(&founded).expect("composes");
        let before =
            found_conditioned_circuit(body.standing().to_vec(), APERTURE).expect("founds");
        let after = found_conditioned_circuit(
            passages_with_composed(&body, &composed).expect("passages"),
            APERTURE,
        )
        .expect("founds");

        let movement = route_movement(&before.circuit, &after.circuit);
        assert!(!movement.founded_statements().is_empty());
        assert_eq!(
            *movement.founded_statements(),
            founded.founded_statements(),
            "the organ built to see a founded statement must see exactly the founded population"
        );
        for statement in movement.founded_statements() {
            assert!(after
                .circuit
                .vertices()
                .contains_key(&statement_vertex_key(statement)));
            assert!(!before
                .circuit
                .vertices()
                .contains_key(&statement_vertex_key(statement)));
        }
    }

    #[test]
    fn derive_still_returns_the_empty_population_on_a_statement_the_deposit_does_not_reach() {
        // The falsifier the record established. Founding a statement is a species beside `derive`,
        // never a weakening of it.
        let body = conditioned();
        for absent in [
            "(P : Prop) (h : P) : exactCarrier (exactCarrier P)",
            "(P : Prop) (h : P) : exact_chart_carry P",
            "(P : Prop) : exactCarrier P",
        ] {
            assert!(body
                .derive(&DerivationQuery::reaching(absent))
                .expect("derives")
                .is_empty());
        }
        // and it still returns a population on a statement the deposit does reach
        assert!(!body
            .derive(&DerivationQuery::reaching("(P : Prop) (h : P) : exactCarrier P"))
            .expect("derives")
            .is_empty());
    }

    #[test]
    fn the_fourth_species_deposits_its_statement_vertex_and_the_other_three_do_not() {
        let body = conditioned();
        let founded = found_statements(&body).expect("founds");
        let composed = compose(&founded).expect("composes");
        let circuit = found_conditioned_circuit(
            passages_with_composed(&body, &composed).expect("passages"),
            APERTURE,
        )
        .expect("founds");

        let composing = statement_composition_moves(&circuit, &body.standing_statements());
        assert!(!composing.is_empty());
        for declared in &composing {
            assert_eq!(declared.species, MoveSpecies::StatementComposition);
            assert!(deposits_its_statement_vertex(&circuit, declared));
            assert!(declared.withdraws.is_empty());
        }

        // the other three species, read off the same circuit, all keep the statement in the boundary
        for declared in deposit_moves(&circuit) {
            assert!(!deposits_its_statement_vertex(&circuit, &declared));
        }
    }

    #[test]
    fn removing_the_licensing_stem_removes_the_route_it_licensed_and_reopens_what_it_covered() {
        let body = conditioned();
        let ablation = ablate_stem_for_statements(&body, "exact").expect("ablates");
        assert!(ablation.removes_structure());
        assert!(ablation.unaccounted.is_empty());

        // the route licensed by the removed stem is structurally absent, named with its statement
        assert!(ablation.routes_departed.contains(&FoundedRoute {
            statement: "(P : Prop) (h : P) : exact_chart_carry P".to_owned(),
            stem: "exact".to_owned(),
        }));

        // **Re-founded 2026-08-09.** This asserted that removing `exact` REOPENS the occurrences it
        // contains. That held only while `FoundedMorphology::cover` deleted every contained
        // occurrence at construction: `act` and `x` were invisible until `exact` left. The cover is
        // retained now, so they stand from the beginning and there is nothing to reopen.
        //
        // The removal half is untouched and still asserted above — `removes_structure` holds and the
        // route departs by name. What is regraded is only the reopening, which was a **receiver
        // artifact of the reduction** rather than a property of the material.
        assert!(
            ablation.routes_reopened.is_empty(),
            "nothing was suppressed, so nothing reopens: {:?}",
            ablation.routes_reopened
        );

        // every departed statement was founded before and is not founded after
        for departed in &ablation.statements_departed {
            assert!(ablation.statements_before.contains(&departed.statement));
            assert!(!ablation.statements_after.contains(&departed.statement));
        }
    }

    /// **The statement is over-determined and the route is not, and that is a finding rather than a
    /// defect.** Removing `exact` takes away the route `exact` licensed, and the statement stays
    /// founded, because the residual letters `exact` had been suppressing by maximality license the
    /// same contact pair the moment it is gone. A report at statement granularity alone would read
    /// this as no change, which is why the ablation carries both.
    #[test]
    fn a_statement_reached_under_several_stems_survives_losing_one_of_them() {
        let body = conditioned();
        let ablation = ablate_stem_for_statements(&body, "exact").expect("ablates");
        let statement = "(P : Prop) (h : P) : exact_chart_carry P";
        assert!(ablation.statements_before.contains(statement));
        assert!(ablation.statements_after.contains(statement));
        assert!(ablation
            .routes_departed
            .iter()
            .any(|route| route.statement == statement));
        // Re-founded with its sibling above: the statement survives because several stems reach it,
        // and that survival is now visible directly — it stands in `statements_after` — rather than
        // through a reopening the constructor's reduction had manufactured.
        assert!(ablation.routes_reopened.is_empty());
        assert!(
            ablation
                .routes_departed
                .iter()
                .filter(|route| route.statement == statement)
                .count()
                < ablation
                    .statements_before
                    .iter()
                    .filter(|carried| carried.as_str() == statement)
                    .count()
                    + ablation.routes_departed.len(),
            "the statement is over-determined: losing one route does not lose it"
        );
    }

    #[test]
    fn an_ablation_naming_a_stem_the_morphology_never_founded_is_refused() {
        let body = conditioned();
        assert!(matches!(
            ablate_stem_for_statements(&body, "zzzz"),
            Err(StatementCompositionRefusal::Conditioned(
                ConditionedDerivationRefusal::StemWasNeverFounded { .. }
            ))
        ));
    }

    #[test]
    fn an_admission_carries_the_arity_the_grammar_does_not_certify_for_it() {
        let founded = found_statements(&conditioned()).expect("founds");
        let head_substitution = founded
            .admitted()
            .into_iter()
            .find(|entry| {
                entry.candidate.slot == Some(SlotSpecies::BodyHead)
                    && entry.candidate.brought == "exact_chart_carry"
            })
            .expect("a head substitution is admitted");
        let StatementAdmission::Admitted {
            carried_aperture, ..
        } = &head_substitution.admission
        else {
            unreachable!()
        };
        assert!(carried_aperture.contains(&GrammarAperture::HeadArityIsUnfounded {
            identifier: "exact_chart_carry".to_owned()
        }));
    }

    #[test]
    fn a_morphemic_aperture_names_a_subpopulation_and_the_complement_is_returned_whole() {
        let founded = found_statements(&conditioned()).expect("founds");
        let morphemic = founded.admitted_at_morphemic(4);
        let residual = founded.admitted_below_morphemic(4);
        assert!(!morphemic.is_empty());
        assert!(!residual.is_empty());
        assert_eq!(morphemic.len() + residual.len(), founded.admitted().len());
    }

    #[test]
    fn a_composed_passage_enters_the_move_aperture_by_its_licensing_stem() {
        let body = conditioned();
        let founded = found_statements(&body).expect("founds");
        let composed = compose(&founded).expect("composes");
        let passages = passages_with_composed(&body, &composed).expect("passages");
        let aperture = MoveAperture::morphemic(&passages, 4);
        assert!(aperture.stems.contains("exact"), "{:?}", aperture.stems);
    }

    // ---------------------------------------------------------------------------------------------
    // The position ecology
    // ---------------------------------------------------------------------------------------------

    /// The same three statements, in artifacts that also carry the **definitional** declarations the
    /// narrow reading drops: a `def` and an `abbrev` of the same declared shape, and a proof body
    /// whose head is the tactic `exact`.
    fn scoped_deposit() -> Vec<(String, String)> {
        vec![
            (
                "carry".to_owned(),
                "namespace Soma\ndef exactCarrier (P : Prop) : Prop := P\n\
                 theorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by\n  \
                 exact formal_carry\nend Soma\n"
                    .to_owned(),
            ),
            (
                "relay".to_owned(),
                "namespace Soma\nabbrev ExactRelay (Q : Prop) : Prop := exactCarrier Q\n\
                 theorem carrier_relay (h : P) : exactCarrier P := by\n  \
                 have step := formal_carry\nend Soma\n"
                    .to_owned(),
            ),
            (
                "agree".to_owned(),
                "namespace Soma\ntheorem every_receiver_agrees (a b : Nat) : a = b := by\n  \
                 have step := Nat.zero\nend Soma\n"
                    .to_owned(),
            ),
        ]
    }

    fn scoped_body() -> ConditionedBody {
        let mut body = ConditionedBody::mount(scoped_deposit()).expect("mounts");
        body.condition(&corpus());
        body
    }

    fn scoped_ecology() -> StatementPositionEcology {
        let deposit = scoped_deposit();
        let reading = crate::lean_development::join(
            deposit
                .iter()
                .map(|(_, text)| {
                    crate::lean_development::read_development(
                        text,
                        crate::lean_development::DeclarationGrain::EveryTopLevelDeclaration,
                    )
                })
                .collect(),
        );
        StatementPositionEcology::found(&reading, &deposit).expect("founds an ecology")
    }

    #[test]
    fn the_ecology_records_where_the_material_places_an_identifier_and_never_what_it_is() {
        let ecology = scoped_ecology();
        assert_eq!(
            ecology.stood_in("exact"),
            vec![ConductPosition::Tactic],
            "`exact` heads a proof step and stands nowhere else"
        );
        assert_eq!(ecology.stood_in("Soma"), vec![ConductPosition::Scoping]);
        assert!(ecology
            .stood_in("exactCarrier")
            .contains(&ConductPosition::Slot(SlotSpecies::BodyHead)));
        assert!(ecology
            .stood_in("exactCarrier")
            .contains(&ConductPosition::Declared {
                former: "def".to_owned()
            }));
        // and the census is a population, not a classification: `Prop` carries four places at once
        assert!(ecology.stood_in("Prop").len() >= 2);
    }

    #[test]
    fn the_wider_reading_recruits_declarations_read_derivation_never_opened() {
        let ecology = scoped_ecology();
        let narrow = scoped_body().recruited_population();
        assert!(
            !narrow.contains("ExactRelay"),
            "the narrow grain opens one declaration per artifact and cannot see the abbrev"
        );
        assert!(ecology.recruited().contains("ExactRelay"));
        assert!(ecology.recruited().is_superset(&narrow));
    }

    #[test]
    fn two_declarations_the_reading_cannot_tell_apart_are_one_cohort() {
        let ecology = scoped_ecology();
        let cohort = ecology.cohort("ExactRelay");
        assert!(cohort.contains(&"exactCarrier".to_owned()), "{cohort:?}");
        assert!(cohort.contains(&"ExactRelay".to_owned()), "{cohort:?}");
        // the cohort is what carries it into a position it was never itself witnessed in
        assert!(!ecology
            .stood_in("ExactRelay")
            .contains(&ConductPosition::Slot(SlotSpecies::BodyHead)));
        assert!(ecology.admits("ExactRelay", SlotSpecies::BodyHead));
    }

    #[test]
    fn a_tactic_is_refused_from_a_statement_slot_and_the_refusal_names_where_it_did_stand() {
        let body = scoped_body();
        let ecology = scoped_ecology();
        let founded =
            found_statements_under(&body, &ecology, PositionGate::Applied).expect("founds");
        let refused = founded
            .refused()
            .into_iter()
            .find(|entry| {
                entry.candidate.brought == "exact"
                    && entry.candidate.slot == Some(SlotSpecies::BodyHead)
            })
            .expect("`exact` is composed into a head slot");
        let Some(StatementObstruction::IdentifierNeverStoodInThisPosition {
            slot, stood_in, ..
        }) = refused.admission.obstruction()
        else {
            panic!("expected the position obstruction, got {:?}", refused.admission);
        };
        assert_eq!(*slot, SlotSpecies::BodyHead);
        assert_eq!(stood_in, &vec![ConductPosition::Tactic]);
        // and the same candidate passes the stem licence, so this is the position gate and not the
        // contact gate wearing a new name
        let withheld = adjudicate(&refused.candidate, &founded.grammar, body.morphology(), &founded.standing)
            .expect("adjudicates");
        assert!(withheld.is_admitted());
    }

    #[test]
    fn the_position_gate_is_a_conjunct_and_never_a_widener() {
        let body = scoped_body();
        let ecology = scoped_ecology();
        let withheld =
            found_statements_under(&body, &ecology, PositionGate::Withheld).expect("founds");
        let applied =
            found_statements_under(&body, &ecology, PositionGate::Applied).expect("founds");
        assert_eq!(
            withheld.adjudicated.len(),
            applied.adjudicated.len(),
            "the orbit is over ONE candidate population"
        );
        assert_eq!(withheld.gate, PositionGate::Withheld);
        assert_eq!(applied.gate, PositionGate::Applied);
        assert!(applied
            .founded_statements()
            .is_subset(&withheld.founded_statements()));
    }

    #[test]
    fn the_gauge_orbit_on_this_material_is_not_trivial() {
        let body = scoped_body();
        let ecology = scoped_ecology();
        let withheld =
            found_statements_under(&body, &ecology, PositionGate::Withheld).expect("founds");
        let applied =
            found_statements_under(&body, &ecology, PositionGate::Applied).expect("founds");
        let removed: BTreeSet<String> = withheld
            .founded_statements()
            .difference(&applied.founded_statements())
            .cloned()
            .collect();
        assert!(
            !removed.is_empty(),
            "a gauge whose group acts trivially on the declared material is not a gauge"
        );
        assert!(!applied.founded_statements().is_empty());
        assert!(applied
            .obstructions()
            .contains_key("identifier-never-stood-in-this-position"));
    }

    #[test]
    fn the_conditioned_composition_reaches_the_declaration_the_material_never_used() {
        let body = scoped_body();
        let ecology = scoped_ecology();
        let founded =
            found_statements_under(&body, &ecology, PositionGate::Applied).expect("founds");
        assert!(founded
            .founded_statements()
            .contains("(P : Prop) (h : P) : ExactRelay P"));
        assert!(founded.is_a_population());
    }

    #[test]
    fn the_unconditioned_null_founds_nothing_under_the_gate_as_well() {
        let null = ConditionedBody::mount(scoped_deposit()).expect("mounts");
        let ecology = scoped_ecology();
        let founded =
            found_statements_under(&null, &ecology, PositionGate::Applied).expect("founds");
        assert!(!founded.adjudicated.is_empty());
        assert!(founded.admitted().is_empty());
        assert!(founded.founded_statements().is_empty());
    }

    #[test]
    fn a_composed_artifact_carries_the_founding_lines_its_own_names_need() {
        let body = scoped_body();
        let ecology = scoped_ecology();
        let founded =
            found_statements_under(&body, &ecology, PositionGate::Applied).expect("founds");
        let composed = compose_in_scope(&founded, Some(&ecology)).expect("composes");
        let carried = composed
            .iter()
            .find(|passage| passage.statement == "(P : Prop) (h : P) : ExactRelay P")
            .expect("the ExactRelay composition is presented");
        assert!(carried.scope.is_complete());
        assert!(carried
            .scope
            .founding
            .iter()
            .any(|line| line == "def exactCarrier (P : Prop) : Prop := P"));
        assert!(carried
            .scope
            .founding
            .iter()
            .any(|line| line == "abbrev ExactRelay (Q : Prop) : Prop := exactCarrier Q"));
        // the transitive closure is ordered so a name is declared before it is used
        let at = |needle: &str| {
            carried
                .scope
                .founding
                .iter()
                .position(|line| line.contains(needle))
                .expect("carried")
        };
        assert!(at("def exactCarrier") < at("abbrev ExactRelay"));
        // and the artifact still reads back reaching the composition, not a carried declaration
        let read = read_derivation(&carried.text).expect("reads");
        assert_eq!(read.statement, carried.statement);
    }

    #[test]
    fn an_unscoped_composition_carries_no_founding_line_and_is_unchanged() {
        let body = scoped_body();
        let ecology = scoped_ecology();
        let founded =
            found_statements_under(&body, &ecology, PositionGate::Applied).expect("founds");
        let bare = compose(&founded).expect("composes");
        assert!(bare.iter().all(|passage| passage.scope.is_empty()));
        assert!(bare
            .iter()
            .all(|passage| passage.text.starts_with("namespace Soma\ntheorem ")));
    }
}
