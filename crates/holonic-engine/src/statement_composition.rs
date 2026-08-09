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
//! ## The licence law, and it is one law for every species
//!
//! **Every composition species names the pair of identifiers it brings into contact, and the
//! morphology must hold that pair together.** That is the same mechanism
//! `conditioned_derivation::derive` licenses a bridge by — two identifiers sharing a committed
//! founded stem under [`FoundedMorphology::cover`]'s maximality — lifted from the proof body to the
//! statement. A body exposed to nothing commits no stem, covers nothing, holds no pair together, and
//! therefore admits **no** composed statement. The conditioning is on the causal path here for
//! exactly the reason it is there, and the unconditioned null is the control that shows it.
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
//! Nothing here is submitted to a kernel, and a composed passage is production read as structure
//! exactly as the deposited artifacts are — the deposit itself carries `theorem carrier_transport
//! ... := Nat.zero`, which no kernel accepts and which the atlas reads all the same. A composed
//! statement is a statement this deposit's own grammar and morphology reach; it is not asserted to
//! be true, provable, or well-typed. Nothing here bears on any Millennium result.

use std::collections::{BTreeMap, BTreeSet};

use crate::algebraic::CausalCellId;
use crate::conditioned_derivation::{
    ConditionedBody, ConditionedCircuit, ConditionedDerivationRefusal, FoundedMorphology, Passage,
    PassageId, PassageOrigin,
};
use crate::derivation_atlas::{read_derivation, statement_vertex_key};
use crate::derivation_skein::{passage_interior, DerivationMove, MoveSpecies};
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
    /// The artifact composed for this candidate did not read back reaching the composed statement.
    /// The analogue of `EmittedPassageMissedItsStatement` for this species, retained as a candidate
    /// obstruction rather than raised, so one malformed composition cannot void a population.
    ReadBackMissedTheComposition { wanted: String, read: String },
}

impl std::fmt::Display for StatementObstruction {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
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
            Self::ComposedStatementIsUnchanged { .. } => "composed-statement-is-unchanged",
            Self::ReadBackMissedTheComposition { .. } => "read-back-missed-the-composition",
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
    format!(
        "namespace Soma\ntheorem {name} {statement} := by\n  have founded := {held}\n  have brought := {brought}\nend Soma\n"
    )
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
            found.entry(here.stem.clone()).or_insert(StatementLicence {
                stem: here.stem.clone(),
                held_at: here.at,
                brought_at: there.at,
                wholes: morphology
                    .stem(&here.stem)
                    .map(|stem| stem.wholes.clone())
                    .unwrap_or_default(),
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

    // 6. the read-back, which is the composer being held to the reading
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

    Ok(StatementAdmission::Admitted {
        licences: found,
        carried_aperture,
    })
}

/// Adjudicate a whole candidate population. The return is the population, never a selection of it.
pub fn admit(
    candidates: Vec<CandidateStatement>,
    grammar: RecoveredStatementGrammar,
    morphology: &FoundedMorphology,
    standing: BTreeSet<String>,
) -> Result<AdmittedStatements, StatementCompositionRefusal> {
    let mut adjudicated = Vec::with_capacity(candidates.len());
    for candidate in candidates {
        let admission = adjudicate(&candidate, &grammar, morphology, &standing)?;
        adjudicated.push(AdjudicatedCandidate {
            candidate,
            admission,
        });
    }
    Ok(AdmittedStatements {
        grammar,
        adjudicated,
        standing,
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
    let mut composed = Vec::new();
    for entry in admitted.admitted() {
        let StatementAdmission::Admitted {
            licences,
            carried_aperture,
        } = &entry.admission
        else {
            continue;
        };
        for declaration in &entry.candidate.declarations {
            for licence in licences {
                let name = composed_name(
                    declaration,
                    &licence.stem,
                    &entry.candidate.brought,
                    &entry.candidate.site,
                );
                let text = compose_artifact(
                    &name,
                    &entry.candidate.statement,
                    &entry.candidate.held,
                    &entry.candidate.brought,
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

    let before = found_statements(body)?;
    let after = found_statements(&ablated)?;
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

        // and every reopened route is accounted for by a proper factor of the removed stem: `exact`
        // had been suppressing the occurrences it contains, and removing it returns them
        assert!(!ablation.routes_reopened.is_empty());
        for reopened in &ablation.routes_reopened {
            assert!(reopened
                .stems
                .iter()
                .any(|stem| "exact".contains(stem.as_str()) && stem != "exact"));
        }

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
        assert!(ablation
            .routes_reopened
            .iter()
            .any(|route| route.statement == statement));
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
}
