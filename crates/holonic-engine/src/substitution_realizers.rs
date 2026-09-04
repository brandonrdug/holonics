//! Realizers founded by substitution, so that placement is paid for by a move the machine made.
//!
//! `placement::place` asks, per realizer, `reaches: FnMut(RealizerId) -> Vec<ItemId>` — which items
//! this realizer's production lands on. Any caller can answer that with a closure; what nothing
//! could answer is where the realizer **population** comes from. A `CausalCell` does not retain what
//! founded it: it carries `source_events`, a grade and a boundary, and none of those is a record of
//! the *move* that deposited it. So a complex has no realizers to read off it, and the population
//! had to arrive as a caller's private bookkeeping.
//!
//! [`crate::skein::Substitution`] is that record. A substitution is a declared local move — two
//! fillings of one hole — and `substitution.added()` is exactly the population of cells the move
//! deposits. **Each declared substitution is a realizer; its landings are what it added.** That is
//! `archive/plans/THE_ASSEMBLY.md` step 2, and it gives `skein` — which had zero callers — a caller
//! whose return is a placement rather than a verdict.
//!
//! ```text
//!   Substitution        added()        conduct class        StandingClass / OpenClass
//!   a declared move  ->  landings  ->  what a receiver  ->  paid for, or exhibited as
//!                        (cells)       distinguishes        an obstruction
//! ```
//!
//! The conduct classes are step 1's: [`crate::complex_system::ComplexSystem`] reads a
//! `GradedCausalComplex` through declared [`crate::dilation::DilatedSection`] receivers and steps
//! conduct across the complex's own 1-cells. This module's tests and
//! `examples/substitution_realizer_placement.rs` both drive that organ rather than a fixture-local
//! machine, because a demonstration whose classes are not the ones step 1 produces is a
//! demonstration about a different composition.
//!
//! ## The realizer population is an object, not a side-channel
//!
//! [`SubstitutionRealizers`] is returned and retained whole. It holds every substitution that was
//! read — **the move itself**, its landings, what it withdrew, and its full [`SkeinReading`], every
//! context's exact remainder rather than a verdict — together with the context family those
//! verdicts index into. Substitutions `read_substitution` refused are retained too, with the move
//! and the refusal species named, because a record that keeps only what was accepted is
//! success-filtering wearing bookkeeping's name.
//!
//! The deposit names what its own indices mean. `RefusedSubstitution { declared: 2 }` and
//! `ContextVerdict { context: 0 }` are positions in families the deposit carries, so a remounted
//! reading can be read without the caller that produced it. [`DeclaredSubstitution`] exists for that
//! reason and no other: `skein::Substitution` is not `Serialize` and this deposit is, the same
//! reason [`SubstitutionRefusal`] exists beside `SkeinRefusal`.
//!
//! ## Three apertures, all three in the return
//!
//! `THE_ASSEMBLY.md`'s holistic constraint: *"the aperture (each organ declares its own; composing
//! without reading them returns a wrong answer)."* Composing this way was measured doing exactly
//! that, on 2026-08-08:
//!
//! ```text
//!   FRAME A  declared [swap_faces]  ->  declared [swap_faces, grow_edge, grow_vertex]
//!            both at EveryRead          a REAL founding: the declared population grew 1 -> 3
//!   FRAME B  the same three, at Invisible  ->  at EveryRead
//!            NOTHING was founded: one population, a looser filter
//! ```
//!
//! Both return **bit-identical** [`Placement`]s, and `placement::discharge` calls both `Founded` —
//! reporting an aperture move as the FOUND that pays. `Placement` carries `receiver_extent` and
//! `class_extent` precisely so the *receiver*-side aperture cannot do this; the realizer side had no
//! carrier at all. [`SubstitutionPlacement`] is that carrier. It holds
//!
//! ```text
//!   declared    the declared substitution family, as moves      growth here is a FOUNDING
//!   admitted    the realizers this aperture handed to `place`   growth here alone is a WIDENING
//!   admission   which filter was applied
//!   contexts    the family the readings the filter reads were taken against
//! ```
//!
//! and [`discharge_substitutions`] separates the two. Neither is forbidden; what is forbidden is not
//! being able to tell.
//!
//! ## What multiplicity means here, and what it does not
//!
//! `added()` is a `BTreeSet`, so one substitution can never land on one *cell* twice. A landing
//! count above one therefore means **the move deposited several distinct cells that the receiver
//! family cannot tell apart** — not a covering degree and not a winding number. That is still the
//! integral question `supported_realizers` asks: a class reached only as `2·c` is supported over the
//! rationals and not over the integers, and here the `2` is two indistinguishable deposited cells.
//! Filling a circle with two faces at once reaches the face class only doubled; filling it with one
//! face reaches it singly, and that difference is a `Z/2` the reading returns.
//!
//! ## What is not claimed
//!
//! Nothing here decides that a substitution *should* be admitted. The three apertures are declared,
//! not ranked, and no quantity in this module is compared by magnitude. An invariance verdict
//! carries `skein`'s own boundary clause: it is relative to the declared context family and to the
//! invariants read.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::algebraic::{CausalCellId, GradedCausalComplex};
// The cell/item bijection has exactly one owner, and it is `complex_system` — step 1 of the same
// assembly. Aliased here so a substitution call site reads in its own vocabulary, and imported
// rather than re-declared so there is never a second implementation of one conversion to keep in
// agreement. It is deliberately not an `impl From` in `algebraic.rs`.
use crate::complex_system::item as item_of_cell;
use crate::placement::{Placement, place};
use crate::rebase_invariants::PivotRule;
use crate::receiver_exact_compression::{ItemId, ObservedSystem, Partition};
use crate::skein::{GradeRemainder, SkeinReading, SkeinRefusal, Substitution, read_substitution};
use crate::supported_realizers::{Realization, RealizerId, landings_from_classes};

/// Which of the read substitutions are handed to `place` as realizers.
///
/// These are **apertures, not a ranking**. Each answers a different question and a reading taken at
/// one is not comparable to a reading taken at another unless the aperture is carried, which
/// [`SubstitutionPlacement`] does.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum RealizerAdmission {
    /// Every substitution that was read without refusal, whatever the receivers made of it.
    EveryRead,
    /// Only substitutions that are a real move no declared context can see — `compresses()`.
    /// A substitution read against an empty context family is **not** invisible: nobody looked.
    Invisible,
    /// Only substitutions at least one declared context can tell apart.
    ///
    /// [`Invisible`](RealizerAdmission::Invisible) and this do **not** partition
    /// [`EveryRead`](RealizerAdmission::EveryRead): a move that changes nothing is in neither, and
    /// neither is a move nobody looked at.
    Visible,
}

/// Why `read_substitution` refused a declared substitution.
///
/// The species is kept typed. Only the algebraic detail degrades to a message, because
/// `CausalAlgebraicError` is not `Serialize` and this deposit is.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum SubstitutionRefusal {
    /// The declared boundary is not contained in both fillings.
    BoundaryNotShared,
    /// A filling or a context is not closed under boundary.
    NotASubcomplex {
        which: String,
    },
    Algebraic {
        reported: String,
    },
}

impl From<SkeinRefusal> for SubstitutionRefusal {
    fn from(refusal: SkeinRefusal) -> Self {
        match refusal {
            SkeinRefusal::BoundaryNotShared => Self::BoundaryNotShared,
            SkeinRefusal::NotASubcomplex(which) => Self::NotASubcomplex {
                which: which.to_owned(),
            },
            SkeinRefusal::Algebraic(error) => Self::Algebraic {
                reported: error.to_string(),
            },
        }
    }
}

/// The declared move itself, in the deposit's own vocabulary.
///
/// `skein::Substitution` derives `Clone, Debug, PartialEq, Eq` and nothing else, so a deposit that
/// referred to declared position `2` named a family only the caller held. This is the same codec
/// [`SubstitutionRefusal`] is, for the same reason, and it is what makes `declared: 2` resolvable
/// from the deposit alone — which is the single link from a placement back to the move that paid.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeclaredSubstitution {
    pub boundary: BTreeSet<CausalCellId>,
    pub before: BTreeSet<CausalCellId>,
    pub after: BTreeSet<CausalCellId>,
}

impl From<&Substitution> for DeclaredSubstitution {
    fn from(substitution: &Substitution) -> Self {
        Self {
            boundary: substitution.boundary.clone(),
            before: substitution.before.clone(),
            after: substitution.after.clone(),
        }
    }
}

/// A declared substitution, read as one thing the machine can produce.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SubstitutionRealizer {
    pub realizer: RealizerId,
    /// Position in the declared population. Provenance, never a capability — and pinned: a realizer
    /// id **is** its declared position, so refusals leave gaps rather than compacting the survivors.
    /// `Placement` carries only `RealizerId`s, so compacting them would silently re-attribute every
    /// standing class to the wrong move.
    pub declared: usize,
    /// The move, so the deposit is readable without the caller that produced it.
    pub substitution: DeclaredSubstitution,
    /// `substitution.added()` — the cells the move deposits, which is what pays for a class.
    ///
    /// Not `after - boundary`: a move may carry a non-boundary cell across itself, and charging it
    /// for a cell that was already there is a different and wrong quantity.
    pub landings: BTreeSet<CausalCellId>,
    /// `substitution.removed()`. Retained and never handed to `place`: a removal deposits nothing,
    /// so it pays for nothing, and a record that dropped it would show a move as having no extent.
    pub withdrawn: BTreeSet<CausalCellId>,
    /// The full reading, every context's exact remainder included. `None` when the population was
    /// declared without a complex to read it against.
    pub reading: Option<SkeinReading>,
}

impl SubstitutionRealizer {
    /// The `reaches` answer for this realizer: the deposited cells, as items.
    pub fn reaches(&self) -> Vec<ItemId> {
        self.landings.iter().copied().map(item_of_cell).collect()
    }

    /// Whether this substitution is handed to `place` under the given aperture.
    pub fn admitted_under(&self, admission: RealizerAdmission) -> bool {
        match admission {
            RealizerAdmission::EveryRead => true,
            RealizerAdmission::Invisible => {
                self.reading.as_ref().is_some_and(SkeinReading::compresses)
            }
            RealizerAdmission::Visible => self
                .reading
                .as_ref()
                .is_some_and(|reading| !reading.distinguishing_contexts().is_empty()),
        }
    }

    /// The exact remainder this move left, across **every** declared context — `skein`'s
    /// certified-remainder return, carried through the adapter rather than collapsed to whether it
    /// was zero or truncated to the first context that looked.
    ///
    /// It is empty in three different situations: nothing was read, nobody looked, and nobody could
    /// see the move. **Emptiness here is therefore not invariance**, which is why
    /// [`admitted_under`](Self::admitted_under) asks `compresses()` — a reading that also requires a
    /// context to have existed and cells to have moved — rather than asking whether this is empty.
    pub fn remainder(&self) -> Vec<&GradeRemainder> {
        self.reading
            .iter()
            .flat_map(|reading| reading.verdicts.iter())
            .flat_map(|verdict| verdict.remainder.iter())
            .collect()
    }
}

/// A declared substitution that was not a substitution, kept rather than dropped.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RefusedSubstitution {
    pub declared: usize,
    /// The move that was refused. Without it `declared` indexes a family the deposit does not hold.
    pub substitution: DeclaredSubstitution,
    pub refusal: SubstitutionRefusal,
}

/// The realizer population founded by a declared substitution family.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SubstitutionRealizers {
    pub schema: String,
    /// The context family every reading was taken against. `ContextVerdict.context` indexes this,
    /// so the deposit names what its own verdict indices mean. Empty when no complex was read.
    pub contexts: Vec<BTreeSet<CausalCellId>>,
    pub realizers: Vec<SubstitutionRealizer>,
    /// Refusals. A reader that ingested only the accepted moves would be success-filtering.
    pub refused: Vec<RefusedSubstitution>,
}

impl SubstitutionRealizers {
    /// How many substitutions were declared, accepted and refused together.
    pub fn declared_extent(&self) -> usize {
        self.realizers.len() + self.refused.len()
    }

    /// The move at a declared position, accepted or refused. The link from a `RealizerId` in a
    /// [`Placement`] back to the substitution that paid for the class.
    pub fn declared_at(&self, declared: usize) -> Option<&DeclaredSubstitution> {
        self.realizers
            .iter()
            .find(|realizer| realizer.declared == declared)
            .map(|realizer| &realizer.substitution)
            .or_else(|| {
                self.refused
                    .iter()
                    .find(|refused| refused.declared == declared)
                    .map(|refused| &refused.substitution)
            })
    }

    /// The declared family, in declared order, refusals included. Growth of **this** is a founding;
    /// growth of what an aperture admits from a fixed one is not.
    pub fn declared_population(&self) -> Vec<DeclaredSubstitution> {
        (0..self.declared_extent())
            .filter_map(|declared| self.declared_at(declared).cloned())
            .collect()
    }

    /// The realizers this aperture hands to `place`, as the objects themselves.
    ///
    /// The single site the admission filter is applied. It used to be applied twice — once here and
    /// once again inside the closure `place_substitutions` passes — and the second application was
    /// provably redundant, since `place` only ever asks about ids this one produced. A refusal that
    /// cannot fire is not a refusal.
    pub fn admitted_under(&self, admission: RealizerAdmission) -> Vec<&SubstitutionRealizer> {
        self.realizers
            .iter()
            .filter(|realizer| realizer.admitted_under(admission))
            .collect()
    }

    /// The realizer ids this aperture hands to `place`.
    ///
    /// Non-admitted realizers are **withheld from the call**, not passed as ghosts that land
    /// nowhere. A ghost still enters `RealizerSupport::realizer_extent`, so the support reading
    /// would describe a population the aperture never consulted.
    pub fn ids_under(&self, admission: RealizerAdmission) -> Vec<RealizerId> {
        self.admitted_under(admission)
            .into_iter()
            .map(|realizer| realizer.realizer)
            .collect()
    }

    /// The `reaches` answer, gated by the aperture.
    ///
    /// Public surface: a caller that assembled its own id list — as the ghost-wiring comparison in
    /// this module's tests does — must not be paid by a substitution the aperture excluded, or the
    /// aperture would be advisory. `place_substitutions` does not route through here, because it
    /// already read the aperture once.
    pub fn reaches_under(&self, admission: RealizerAdmission, realizer: RealizerId) -> Vec<ItemId> {
        self.realizers
            .iter()
            .find(|candidate| candidate.realizer == realizer)
            .filter(|candidate| candidate.admitted_under(admission))
            .map(SubstitutionRealizer::reaches)
            .unwrap_or_default()
    }

    /// The realizations against a conduct partition, so the incidence and the positive form of this
    /// population can be taken directly.
    ///
    /// `place` builds the same landings by its own route; that the two agree is a check with two
    /// frames rather than one, and `supported_realizers::positive_form` applied to
    /// `incidence(&self.realizations_under(..), class_extent)` is §11's positive form on this
    /// population.
    pub fn realizations_under(
        &self,
        admission: RealizerAdmission,
        conduct: &Partition,
    ) -> Vec<Realization> {
        self.admitted_under(admission)
            .into_iter()
            .map(|realizer| Realization {
                realizer: realizer.realizer,
                landings: landings_from_classes(realizer.reaches(), |item| conduct.block_of(item)),
            })
            .collect()
    }
}

/// A placement, together with the realizer-side apertures that produced it.
///
/// `Placement` carries the receiver-side aperture — `receiver_extent`, `class_extent` — so that
/// discharging an obstruction by distinguishing less reads as `Coarsened` and never as production.
/// The realizer side has three declarations of its own and none of them was in the return: the
/// declared family, the admission filter, and the context family the filter reads. Without them,
/// declaring two new moves and merely relaxing the filter over a fixed family are bit-identical.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SubstitutionPlacement {
    pub schema: String,
    pub placement: Placement,
    /// Which filter was applied.
    pub admission: RealizerAdmission,
    /// The declared family, as moves. Growth here is the FOUND that pays.
    pub declared: Vec<DeclaredSubstitution>,
    /// The realizers the filter handed to `place`, named rather than counted. Growth here with
    /// `declared` fixed is a widening and never a production.
    pub admitted: Vec<RealizerId>,
    /// The context family the admission filter's readings were taken against. A move can become
    /// admissible because a context was declared, with nothing produced.
    pub contexts: Vec<BTreeSet<CausalCellId>>,
}

/// How a later substitution reading discharged what an earlier one left open, with **all** the
/// apertures read.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum SubstitutionDischarge {
    /// A move was declared that had not been declared before, and the open population shrank. This
    /// is the FOUND that pays.
    Founded,
    /// Nothing new was declared; more of a fixed family reached `place` — because the filter was
    /// relaxed, or because a context was declared that made a move legible to the filter. The
    /// realizer-side twin of [`Discharge::Coarsened`](crate::placement::Discharge::Coarsened), and
    /// the case `placement::discharge` alone reports as `Founded`.
    Widened,
    /// The receiver family shrank, so classes stopped being distinguished.
    Coarsened,
    /// More than one aperture moved. Reported rather than guessed at.
    Mixed,
    /// Nothing was open, or no declared aperture moved.
    Nothing,
}

/// Name the kind of discharge between two substitution readings.
///
/// Three axes, read independently:
///
/// ```text
///   produced   some move in `after.declared` was not in `before.declared`
///   relaxed    nothing was produced and `after.admitted` is larger than `before.admitted`
///   coarsened  the receiver family or the class family shrank
/// ```
///
/// `Nothing` when the open population did not shrink, and also when it shrank while no declared
/// aperture moved — in which case whatever discharged it is outside everything this reading
/// declares, and naming it here would be a guess.
pub fn discharge_substitutions(
    before: &SubstitutionPlacement,
    after: &SubstitutionPlacement,
) -> SubstitutionDischarge {
    if before.placement.open.is_empty() || after.placement.open.len() >= before.placement.open.len()
    {
        return SubstitutionDischarge::Nothing;
    }
    let produced = after
        .declared
        .iter()
        .any(|move_made| !before.declared.contains(move_made));
    let relaxed = !produced && after.admitted.len() > before.admitted.len();
    let coarsened = after.placement.receiver_extent < before.placement.receiver_extent
        || after.placement.class_extent < before.placement.class_extent;

    match (produced, relaxed, coarsened) {
        (true, _, false) => SubstitutionDischarge::Founded,
        (false, true, false) => SubstitutionDischarge::Widened,
        (false, false, true) => SubstitutionDischarge::Coarsened,
        (false, false, false) => SubstitutionDischarge::Nothing,
        _ => SubstitutionDischarge::Mixed,
    }
}

/// Found a realizer population from declared substitutions, without reading them.
///
/// Every substitution becomes a realizer whose landings are what it added. No context family is
/// consulted, so every reading is `None` and only [`RealizerAdmission::EveryRead`] admits anything.
pub fn realizers_from_substitutions(substitutions: &[Substitution]) -> SubstitutionRealizers {
    SubstitutionRealizers {
        schema: "holonic-engine.substitution-realizers.v2".to_owned(),
        contexts: Vec::new(),
        realizers: substitutions
            .iter()
            .enumerate()
            .map(|(declared, substitution)| SubstitutionRealizer {
                realizer: RealizerId(declared as u64),
                declared,
                substitution: DeclaredSubstitution::from(substitution),
                landings: substitution.added(),
                withdrawn: substitution.removed(),
                reading: None,
            })
            .collect(),
        refused: Vec::new(),
    }
}

/// Read each declared substitution against the context family, and found the realizer population
/// from what survived.
///
/// A refusal is retained rather than propagated: one malformed substitution in a declared family
/// does not destroy the reading of the others. **A malformed *context* refuses every substitution**,
/// since `read_substitution` checks the whole family per call, and that is the correct behaviour —
/// a context that is not a subcomplex makes every verdict meaningless, not one of them.
///
/// A realizer id is the substitution's **declared position**, so a refusal leaves a gap in the id
/// sequence rather than compacting the survivors onto it.
pub fn read_and_realize(
    complex: &GradedCausalComplex,
    substitutions: &[Substitution],
    contexts: &[BTreeSet<CausalCellId>],
    rule: PivotRule,
) -> SubstitutionRealizers {
    let mut realizers = Vec::new();
    let mut refused = Vec::new();
    for (declared, substitution) in substitutions.iter().enumerate() {
        match read_substitution(complex, substitution, contexts, rule) {
            Ok(reading) => realizers.push(SubstitutionRealizer {
                realizer: RealizerId(declared as u64),
                declared,
                substitution: DeclaredSubstitution::from(substitution),
                landings: substitution.added(),
                withdrawn: substitution.removed(),
                reading: Some(reading),
            }),
            Err(refusal) => refused.push(RefusedSubstitution {
                declared,
                substitution: DeclaredSubstitution::from(substitution),
                refusal: refusal.into(),
            }),
        }
    }
    SubstitutionRealizers {
        schema: "holonic-engine.substitution-realizers.v2".to_owned(),
        contexts: contexts.to_vec(),
        realizers,
        refused,
    }
}

/// Decide placement against a system, paid for by substitutions, with the apertures carried.
///
/// This is the composition step 2 names: `skein` founds the realizers, `placement` decides what
/// stands. A class no substitution deposited into is OPEN and never a class.
pub fn place_substitutions(
    system: &dyn ObservedSystem,
    realizers: &SubstitutionRealizers,
    admission: RealizerAdmission,
) -> SubstitutionPlacement {
    // The aperture is read once, here, and the ids and the landings both come out of that one read.
    let admitted = realizers.admitted_under(admission);
    let ids: Vec<RealizerId> = admitted.iter().map(|realizer| realizer.realizer).collect();
    let landings: BTreeMap<RealizerId, Vec<ItemId>> = admitted
        .iter()
        .map(|realizer| (realizer.realizer, realizer.reaches()))
        .collect();
    let placement = place(system, &ids, |realizer| {
        // `ids` are the keys of `landings`, built in the same pass, and `place` asks about nothing
        // else. This arm is here because the closure must be total, not because it can be reached.
        landings.get(&realizer).cloned().unwrap_or_default()
    });
    SubstitutionPlacement {
        schema: "holonic-engine.substitution-placement.v1".to_owned(),
        placement,
        admission,
        declared: realizers.declared_population(),
        admitted: ids,
        contexts: realizers.contexts.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebraic::{CausalChain, ComparativeMultiplicity};
    use crate::causal::EventId;
    // The reverse leg of the bijection, needed only by the round-trip contract test. The module
    // proper only ever converts cells into items.
    use crate::complex_system::{AddressReading, ComplexSystem, cell as cell_of_item};
    use crate::dilation::{Horizon, WalkOrder, dilate};
    use crate::placement::{Discharge, discharge};
    use crate::rebase_invariants::{IntegerMatrix, smith_normal_form};
    use crate::supported_realizers::{incidence, positive_form, quadratic_value};
    use num_bigint::BigInt;
    use num_traits::Zero;

    // ---------------------------------------------------------------------------------------
    // the material
    //
    // A triangle with its three edges, TWO faces both filling it, and a detached vertex. The two
    // faces exist so that a move can deposit two cells the receivers cannot tell apart -- which is
    // the only way this fixture can exhibit a class reached rationally and not integrally. The
    // detached vertex exists so that a move can deposit into a class no incidence reaches; without
    // it that class could never be reached and the "OPEN" half of the claim would be unfalsifiable
    // rather than merely unpaid.

    struct Triangle {
        complex: GradedCausalComplex,
        a: CausalCellId,
        b: CausalCellId,
        c: CausalCellId,
        d: CausalCellId,
        ab: CausalCellId,
        bc: CausalCellId,
        ca: CausalCellId,
        t1: CausalCellId,
        t2: CausalCellId,
    }

    fn source() -> BTreeSet<EventId> {
        BTreeSet::from([EventId(1)])
    }

    fn triangle() -> Triangle {
        let mut complex = GradedCausalComplex::default();
        let vertex = |complex: &mut GradedCausalComplex, name: &str| {
            complex
                .found_cell(name, source(), 0, CausalChain::default())
                .unwrap()
        };
        let a = vertex(&mut complex, "a");
        let b = vertex(&mut complex, "b");
        let c = vertex(&mut complex, "c");

        let edge = |complex: &mut GradedCausalComplex,
                    name: &str,
                    from: CausalCellId,
                    to: CausalCellId| {
            let mut boundary = CausalChain::default();
            boundary.add_term(to, ComparativeMultiplicity::positive(1u32));
            boundary.add_term(from, ComparativeMultiplicity::negative(1u32));
            complex.found_cell(name, source(), 1, boundary).unwrap()
        };
        let ab = edge(&mut complex, "ab", a, b);
        let bc = edge(&mut complex, "bc", b, c);
        let ca = edge(&mut complex, "ca", c, a);

        let face = |complex: &mut GradedCausalComplex, name: &str| {
            let mut boundary = CausalChain::default();
            for edge in [ab, bc, ca] {
                boundary.add_term(edge, ComparativeMultiplicity::positive(1u32));
            }
            complex.found_cell(name, source(), 2, boundary).unwrap()
        };
        let t1 = face(&mut complex, "t1");
        let t2 = face(&mut complex, "t2");

        let d = vertex(&mut complex, "d");

        Triangle {
            complex,
            a,
            b,
            c,
            d,
            ab,
            bc,
            ca,
            t1,
            t2,
        }
    }

    /// The complex read through **step 1's organ**, not through a machine invented here: two real
    /// dilated sections as receivers, and conduct stepping across the complex's own 1-cells.
    ///
    /// This module used to declare its own `ObservedSystem` in this block, whose `successor` stepped
    /// a 2-cell down to a 1-cell — precisely what `ComplexSystem` declares a terminus. Every
    /// demonstration then rested on conduct classes step 1 does not produce, and the two steps were
    /// joined by a `u64` rewrap and nothing else.
    fn system(world: &Triangle) -> ComplexSystem<'_> {
        let focus = |cell| {
            dilate(&world.complex, cell, Horizon::Unbounded, WalkOrder::Breadth)
                .expect("the focus is a cell of this complex")
        };
        ComplexSystem::declare(
            &world.complex,
            AddressReading::Metric,
            vec![focus(world.a), focus(world.b)],
            ComplexSystem::every_one_cell(&world.complex),
        )
        .expect("the fixture declares an aperture this complex can honour")
    }

    /// Filling the circle with one face. A real move, and one every declared context can see.
    fn fill_once(world: &Triangle) -> Substitution {
        let circle = circle(world);
        let mut filled = circle.clone();
        filled.insert(world.t1);
        Substitution {
            boundary: circle.clone(),
            before: circle,
            after: filled,
        }
    }

    /// Filling it with BOTH faces at once. Deposits two cells the receivers cannot separate.
    fn fill_twice(world: &Triangle) -> Substitution {
        let circle = circle(world);
        let mut filled = circle.clone();
        filled.insert(world.t1);
        filled.insert(world.t2);
        Substitution {
            boundary: circle.clone(),
            before: circle,
            after: filled,
        }
    }

    /// Adding a second face to a circle **that already carries one**.
    ///
    /// The only declared move in this file that keeps a non-boundary cell across itself, and the
    /// reason it exists: for every other move here `added()` and `after - boundary` coincide by
    /// accident of the material, so a mutation swapping the module's headline quantity for the wrong
    /// one survived the whole suite.
    fn add_second_face(world: &Triangle) -> Substitution {
        let circle = circle(world);
        let mut with_first = circle.clone();
        with_first.insert(world.t1);
        let mut with_both = with_first.clone();
        with_both.insert(world.t2);
        Substitution {
            boundary: circle,
            before: with_first,
            after: with_both,
        }
    }

    /// Swapping one filling face for the other. Cells really move and no receiver can tell.
    fn swap_faces(world: &Triangle) -> Substitution {
        let circle = circle(world);
        let mut with_first = circle.clone();
        with_first.insert(world.t1);
        let mut with_second = circle.clone();
        with_second.insert(world.t2);
        Substitution {
            boundary: circle,
            before: with_first,
            after: with_second,
        }
    }

    /// Depositing one edge. Lands in the class of `ab`, and its remainder differs from context to
    /// context: against loose vertices it joins two components, against the arc it closes a cycle.
    fn grow_edge(world: &Triangle) -> Substitution {
        let ends = BTreeSet::from([world.a, world.b]);
        let mut with_edge = ends.clone();
        with_edge.insert(world.ab);
        Substitution {
            boundary: ends.clone(),
            before: ends,
            after: with_edge,
        }
    }

    /// Depositing the detached vertex, which nothing else in the complex reaches.
    fn grow_vertex(world: &Triangle) -> Substitution {
        let one = BTreeSet::from([world.a]);
        let mut two = one.clone();
        two.insert(world.d);
        Substitution {
            boundary: one.clone(),
            before: one,
            after: two,
        }
    }

    /// A move that changes nothing. In neither aperture, and it must never pay for anything.
    fn stand_still(world: &Triangle) -> Substitution {
        let held = BTreeSet::from([world.a, world.b, world.c]);
        Substitution {
            boundary: held.clone(),
            before: held.clone(),
            after: held,
        }
    }

    /// Removing the filling face. A real move that deposits nothing.
    fn unfill(world: &Triangle) -> Substitution {
        let circle = circle(world);
        let mut filled = circle.clone();
        filled.insert(world.t1);
        Substitution {
            boundary: circle.clone(),
            before: filled,
            after: circle,
        }
    }

    /// A declared boundary that lies in neither filling: refused, and retained.
    fn unshared_boundary(world: &Triangle) -> Substitution {
        Substitution {
            boundary: BTreeSet::from([world.ca]),
            before: BTreeSet::from([world.a]),
            after: BTreeSet::from([world.a, world.d]),
        }
    }

    fn circle(world: &Triangle) -> BTreeSet<CausalCellId> {
        BTreeSet::from([world.a, world.b, world.c, world.ab, world.bc, world.ca])
    }

    /// Three contexts that are three different readings, not one counted three times.
    ///
    /// The move that separates them is `grow_edge`. Against loose vertices, depositing `ab` joins
    /// two components; against the arc `bc, ca` it closes a cycle instead; against the whole circle
    /// it is invisible, because `ab` is already there. A family whose members give one subcomplex
    /// for every declared move cannot exhibit a per-context remainder at all, which is what this
    /// family was until 2026-08-08.
    fn contexts(world: &Triangle) -> Vec<BTreeSet<CausalCellId>> {
        vec![
            BTreeSet::from([world.a, world.b, world.c]),
            BTreeSet::from([world.a, world.b, world.c, world.bc, world.ca]),
            circle(world),
        ]
    }

    /// The class each named cell falls in, computed from the conduct partition directly. Used to
    /// state the claims in terms of cells rather than class indices.
    fn class_of(placed: &Placement, cell: CausalCellId) -> usize {
        placed
            .compression
            .conduct
            .block_of(item_of_cell(cell))
            .expect("every cell of the complex is an item of the system")
    }

    /// The realizers that paid for the class a named cell falls in.
    fn paid_by(placed: &Placement, cell: CausalCellId) -> Vec<RealizerId> {
        let class = class_of(placed, cell);
        placed
            .standing
            .iter()
            .find(|standing| standing.class == class)
            .unwrap_or_else(|| panic!("the class of {cell:?} does not stand"))
            .realizers
            .clone()
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
    // the fixture must be able to distinguish what is claimed of it

    /// Eight conduct classes, and the only identification is the one the file needs: the two faces.
    /// If the receivers merged more, this whole file would be testing one class against itself.
    #[test]
    fn the_fixture_holds_two_indistinguishable_faces_and_separates_every_other_cell() {
        let world = triangle();
        let placed = place_substitutions(
            &system(&world),
            &realizers_from_substitutions(&[]),
            RealizerAdmission::EveryRead,
        );
        let placement = &placed.placement;
        assert_eq!(
            placement.receiver_extent, 2,
            "two dilated sections, two frames"
        );
        assert_eq!(placement.class_extent, 8);
        assert_eq!(
            class_of(placement, world.t1),
            class_of(placement, world.t2),
            "the two faces must be indistinguishable, or nothing here can be reached in multiple"
        );
        let separated: BTreeSet<usize> = [
            world.a, world.b, world.c, world.d, world.ab, world.bc, world.ca, world.t1,
        ]
        .into_iter()
        .map(|cell| class_of(placement, cell))
        .collect();
        assert_eq!(
            separated.len(),
            8,
            "every other cell is on its own; the identification is exactly one pair"
        );
        assert_ne!(
            class_of(placement, world.d),
            class_of(placement, world.a),
            "the detached vertex is a class of its own, reachable only by the move that deposits it"
        );
    }

    /// The conversion this module depends on is a bijection. It is owned by `complex_system`, and
    /// this asserts the contract at the point of use: a landing is only a payment if the cell a
    /// substitution deposited and the item a receiver distinguishes are the same thing.
    ///
    /// An `assert_ne!(item(CausalCellId(1)), item(CausalCellId(2)))` sat below until 2026-08-08. It
    /// is injectivity of `|c| ItemId(c.0)`, which the round trip above it already implies, and it
    /// could not have failed for any implementation of either direction.
    #[test]
    fn the_cell_item_conversion_this_module_depends_on_is_a_bijection() {
        for raw in [0u64, 1, 2, 7, 65_535, u64::MAX] {
            assert_eq!(
                cell_of_item(item_of_cell(CausalCellId(raw))),
                CausalCellId(raw)
            );
            assert_eq!(item_of_cell(cell_of_item(ItemId(raw))), ItemId(raw));
        }
    }

    /// `reaches_under` is public and answers per aperture. Asked about a realizer the aperture
    /// withholds, it must return nothing — otherwise a caller that built its own id list could be
    /// paid by a substitution the aperture excluded, and the aperture would be advisory.
    #[test]
    fn reaches_under_returns_nothing_for_a_realizer_its_aperture_withholds() {
        let world = triangle();
        let founded = read_and_realize(
            &world.complex,
            &[swap_faces(&world), fill_once(&world)],
            &contexts(&world),
            PivotRule::FirstNonzero,
        );
        // 0 is the invisible face swap; 1 is the visible fill.
        assert_eq!(
            founded.reaches_under(RealizerAdmission::Invisible, RealizerId(0)),
            vec![item_of_cell(world.t2)]
        );
        assert!(
            founded
                .reaches_under(RealizerAdmission::Invisible, RealizerId(1))
                .is_empty(),
            "a visible move must pay nothing at the invisible aperture"
        );
        assert_eq!(
            founded.reaches_under(RealizerAdmission::Visible, RealizerId(1)),
            vec![item_of_cell(world.t1)]
        );
        assert!(
            founded
                .reaches_under(RealizerAdmission::Visible, RealizerId(0))
                .is_empty()
        );
        assert!(
            founded
                .reaches_under(RealizerAdmission::EveryRead, RealizerId(9))
                .is_empty(),
            "and an id that names no declared substitution pays nothing"
        );
    }

    // ---------------------------------------------------------------------------------------
    // the adapter

    /// The whole claim of the module in one assertion: landings are `added()`, and a move that only
    /// withdraws lands nowhere while its withdrawal stays in the record.
    #[test]
    fn a_substitution_lands_on_exactly_what_it_added_and_a_withdrawal_pays_for_nothing() {
        let world = triangle();
        let declared = [fill_once(&world), unfill(&world), swap_faces(&world)];
        let founded = realizers_from_substitutions(&declared);

        assert_eq!(founded.realizers[0].landings, BTreeSet::from([world.t1]));
        assert!(founded.realizers[0].withdrawn.is_empty());
        assert_eq!(founded.realizers[0].reaches(), vec![item_of_cell(world.t1)]);

        assert!(
            founded.realizers[1].landings.is_empty(),
            "a removal deposits nothing"
        );
        assert_eq!(
            founded.realizers[1].withdrawn,
            BTreeSet::from([world.t1]),
            "and what it withdrew is retained, so the move is not invisible in the record"
        );

        assert_eq!(founded.realizers[2].landings, BTreeSet::from([world.t2]));
        assert_eq!(founded.realizers[2].withdrawn, BTreeSet::from([world.t1]));

        // The deposit names the move, field for field against the material rather than against
        // another call of the same codec, so that a codec dropping a field is visible.
        let mut filled = circle(&world);
        filled.insert(world.t1);
        assert_eq!(founded.realizers[0].substitution.boundary, circle(&world));
        assert_eq!(founded.realizers[0].substitution.before, circle(&world));
        assert_eq!(founded.realizers[0].substitution.after, filled);
        assert_eq!(founded.realizers[1].substitution.before, filled);
        assert_eq!(founded.realizers[1].substitution.after, circle(&world));
        assert_eq!(
            founded.declared_at(2),
            Some(&DeclaredSubstitution::from(&swap_faces(&world)))
        );
        assert_eq!(founded.declared_population().len(), 3);
    }

    /// The separator for the module's headline quantity.
    ///
    /// `landings` is `after - before`, not `after - boundary`. Those two coincide for every move in
    /// this fixture except this one, because no other move keeps a non-boundary cell across itself —
    /// which is why a mutation swapping them passed eighteen tests. The same fixture separates
    /// `withdrawn = before - after` from `before - boundary`.
    #[test]
    fn a_move_that_keeps_a_cell_across_itself_separates_added_from_after_minus_boundary() {
        let world = triangle();
        let declared = add_second_face(&world);

        let after_minus_boundary: BTreeSet<CausalCellId> = declared
            .after
            .difference(&declared.boundary)
            .copied()
            .collect();
        let before_minus_boundary: BTreeSet<CausalCellId> = declared
            .before
            .difference(&declared.boundary)
            .copied()
            .collect();
        assert_eq!(
            after_minus_boundary,
            BTreeSet::from([world.t1, world.t2]),
            "the move carries t1 across itself, so the two quantities genuinely differ here"
        );
        assert_eq!(before_minus_boundary, BTreeSet::from([world.t1]));

        let founded = read_and_realize(
            &world.complex,
            &[declared],
            &contexts(&world),
            PivotRule::FirstNonzero,
        );
        let realizer = &founded.realizers[0];
        assert_eq!(
            realizer.landings,
            BTreeSet::from([world.t2]),
            "the move deposits exactly the second face"
        );
        assert!(realizer.withdrawn.is_empty(), "and withdraws nothing");
        assert_ne!(realizer.landings, after_minus_boundary);
        assert_ne!(realizer.withdrawn, before_minus_boundary);

        // And the consequence at placement, which is where the wrong quantity would do its damage:
        // one deposit into the face class pays for it integrally. Charged with `after - boundary`
        // the same move would land TWICE in one class and the class would come back OPEN with a Z/2.
        let placed = place_substitutions(&system(&world), &founded, RealizerAdmission::EveryRead);
        assert_eq!(paid_by(&placed.placement, world.t1), vec![RealizerId(0)]);
        assert!(
            placed.placement.support.torsion_obstruction().is_empty(),
            "a single deposit is not a doubled one: {:?}",
            placed.placement.support.torsion_obstruction()
        );
    }

    // ---------------------------------------------------------------------------------------
    // the required demonstration: one class stands because a substitution reached it, another
    // stays OPEN because none did

    #[test]
    fn a_class_a_substitution_reached_stands_and_a_class_none_reached_stays_open() {
        let world = triangle();
        let founded = read_and_realize(
            &world.complex,
            &[swap_faces(&world)],
            &contexts(&world),
            PivotRule::FirstNonzero,
        );
        assert!(founded.refused.is_empty(), "{:?}", founded.refused);
        assert_eq!(
            founded.ids_under(RealizerAdmission::Invisible),
            vec![RealizerId(0)],
            "the face swap is a real move no declared context can see"
        );

        let placed = place_substitutions(&system(&world), &founded, RealizerAdmission::Invisible);
        let placement = &placed.placement;

        // The face class stands, and it stands because the substitution reached it.
        let standing = placement
            .standing
            .iter()
            .find(|class| class.class == class_of(placement, world.t1))
            .expect("the class the swap deposited into must stand");
        assert_eq!(
            standing.realizers,
            vec![RealizerId(0)],
            "and the realizer that paid for it is named"
        );
        assert!(standing.members.contains(&item_of_cell(world.t1)));
        assert!(standing.members.contains(&item_of_cell(world.t2)));
        assert_eq!(placement.standing.len(), 1);

        // Every other class stays OPEN. Nothing deposited into them, and they are named rather than
        // counted. `every_standing_class_was_paid_for()` and an OPEN-versus-standing disjointness
        // loop sat here until 2026-08-08: `place` pushes to `standing` only where `reached_by` is
        // non-empty and `continue`s to `open` otherwise, so both are theorems about `place` and both
        // passed against deliberately adversarial closures.
        let open: BTreeSet<usize> = placement.open.iter().map(|class| class.class).collect();
        let unreached: BTreeSet<usize> = [
            world.a, world.b, world.c, world.d, world.ab, world.bc, world.ca,
        ]
        .into_iter()
        .map(|cell| class_of(placement, cell))
        .collect();
        assert_eq!(
            open, unreached,
            "a class no substitution deposited into is OPEN and never a class"
        );
        assert!(!placement.closed());
        assert_eq!(
            placement.support.free_obstruction(),
            7,
            "and the obstruction is exhibited, at exactly the seven unreached classes"
        );
    }

    /// **The decisive one.** Declaring new substitutions and relaxing the admission filter over a
    /// fixed family return bit-identical `Placement`s, and `placement::discharge` reports both as
    /// `Founded`. Only one of them produced anything.
    #[test]
    fn declaring_more_substitutions_is_a_founding_and_widening_the_filter_is_not() {
        let world = triangle();
        let family = contexts(&world);
        let three = [swap_faces(&world), grow_edge(&world), grow_vertex(&world)];
        let one = read_and_realize(
            &world.complex,
            &three[..1],
            &family,
            PivotRule::FirstNonzero,
        );
        let all = read_and_realize(&world.complex, &three, &family, PivotRule::FirstNonzero);

        // FRAME A: the declared family grows, at one aperture. A real founding.
        let a_before = place_substitutions(&system(&world), &one, RealizerAdmission::EveryRead);
        let a_after = place_substitutions(&system(&world), &all, RealizerAdmission::EveryRead);
        // FRAME B: one declared family, read at two apertures. Nothing was produced.
        let b_before = place_substitutions(&system(&world), &all, RealizerAdmission::Invisible);
        let b_after = place_substitutions(&system(&world), &all, RealizerAdmission::EveryRead);

        // The material can vary the property: the open population really shrinks in both frames.
        assert_eq!(a_before.placement.open.len(), 7);
        assert_eq!(a_after.placement.open.len(), 5);
        assert_eq!(a_after.placement.standing.len(), 3);

        // The frames are indistinguishable AS PLACEMENTS. This is the defect, exhibited rather than
        // asserted away.
        assert_eq!(
            a_before.placement, b_before.placement,
            "a one-move family at EveryRead and a three-move family at Invisible place identically"
        );
        assert_eq!(a_after.placement, b_after.placement);
        assert_eq!(
            discharge(&a_before.placement, &a_after.placement),
            Discharge::Founded
        );
        assert_eq!(
            discharge(&b_before.placement, &b_after.placement),
            Discharge::Founded,
            "placement alone reports the widening as the FOUND that pays, because the realizer-side \
             aperture is not in its return"
        );

        // Carrying the realizer aperture tells them apart.
        assert_eq!(
            discharge_substitutions(&a_before, &a_after),
            SubstitutionDischarge::Founded
        );
        assert_eq!(
            discharge_substitutions(&b_before, &b_after),
            SubstitutionDischarge::Widened,
            "nothing was declared that was not declared before; the filter was relaxed"
        );

        // Named, not counted.
        assert_eq!(
            a_before.declared,
            vec![DeclaredSubstitution::from(&three[0])]
        );
        assert_eq!(a_after.declared.len(), 3);
        assert_eq!(
            b_before.declared, b_after.declared,
            "one declared family, read at two apertures"
        );
        assert_eq!(b_before.admitted, vec![RealizerId(0)]);
        assert_eq!(
            b_after.admitted,
            vec![RealizerId(0), RealizerId(1), RealizerId(2)]
        );
        assert_eq!(b_before.admission, RealizerAdmission::Invisible);
        assert_eq!(b_after.admission, RealizerAdmission::EveryRead);
    }

    /// Declaring a **context** can admit a move at a fixed aperture over a fixed family, with
    /// nothing produced. That is a widening too, and it is the case an `admission != admission`
    /// test would miss.
    #[test]
    fn declaring_a_context_admits_a_move_without_producing_one() {
        let world = triangle();
        let declared = [swap_faces(&world)];
        let unlooked = read_and_realize(&world.complex, &declared, &[], PivotRule::FirstNonzero);
        let looked = read_and_realize(
            &world.complex,
            &declared,
            &contexts(&world),
            PivotRule::FirstNonzero,
        );

        let before = place_substitutions(&system(&world), &unlooked, RealizerAdmission::Invisible);
        let after = place_substitutions(&system(&world), &looked, RealizerAdmission::Invisible);

        assert!(
            before.admitted.is_empty(),
            "a move nobody looked at is not invisible"
        );
        assert_eq!(after.admitted, vec![RealizerId(0)]);
        assert_eq!(before.admission, after.admission, "the filter did not move");
        assert_eq!(before.declared, after.declared, "and nothing was declared");
        assert!(before.contexts.is_empty());
        assert_eq!(after.contexts.len(), 3);
        assert!(after.placement.open.len() < before.placement.open.len());
        assert_eq!(
            discharge_substitutions(&before, &after),
            SubstitutionDischarge::Widened
        );
    }

    /// Why `ids_under` **withholds** rather than passing withheld realizers as ghosts that land
    /// nowhere — and why neither wiring is a founding.
    ///
    /// "Deposit the population" reads at first as "hand `place` every declared realizer and let the
    /// aperture empty its landings". That wiring returns the same standing and open classes, so the
    /// difference is not what stands: it is the population `RealizerSupport` then describes, which
    /// counts three realizers the aperture handed over one of.
    #[test]
    fn withholding_and_ghosting_describe_two_populations_and_neither_widening_is_a_founding() {
        let world = triangle();
        let founded = read_and_realize(
            &world.complex,
            &[swap_faces(&world), grow_edge(&world), grow_vertex(&world)],
            &contexts(&world),
            PivotRule::FirstNonzero,
        );
        let every = founded.ids_under(RealizerAdmission::EveryRead);

        let ghosted = place(&system(&world), &every, |realizer| {
            founded.reaches_under(RealizerAdmission::Invisible, realizer)
        });
        let withheld = place_substitutions(&system(&world), &founded, RealizerAdmission::Invisible);
        let wide = place_substitutions(&system(&world), &founded, RealizerAdmission::EveryRead);

        // The two narrow readings agree about what stands and what is open, class for class.
        assert_eq!(ghosted.standing, withheld.placement.standing);
        assert_eq!(ghosted.open, withheld.placement.open);
        assert_eq!(ghosted.open.len(), 7);

        // They disagree about the population the support reading describes.
        assert_eq!(
            withheld.placement.support.realizer_extent, 1,
            "the aperture handed `place` one realizer"
        );
        assert_eq!(
            ghosted.support.realizer_extent, 3,
            "and the ghost wiring reports three, erasing the aperture from the reading"
        );
        assert_eq!(withheld.admitted, vec![RealizerId(0)]);

        // `placement::discharge` is wrong about both wirings, in opposite directions...
        assert_eq!(
            discharge(&withheld.placement, &wide.placement),
            Discharge::Founded,
            "the withholding wiring reads a widening as production"
        );
        assert_eq!(
            discharge(&ghosted, &wide.placement),
            Discharge::Nothing,
            "and the ghost wiring reads it as nothing"
        );
        // ...because neither is a founding. Nothing was declared that was not declared before.
        assert_eq!(
            discharge_substitutions(&withheld, &wide),
            SubstitutionDischarge::Widened
        );
        assert_eq!(withheld.declared, wide.declared);
    }

    // ---------------------------------------------------------------------------------------
    // the nonzero controls -- a law that returns zero proves nothing about itself

    /// Depositing two indistinguishable faces at once reaches the face class only doubled, so it is
    /// supported rationally and **not** integrally. The returned quantity is provably nonzero: a
    /// `Z/2` in the cokernel and a `reached_only_in_multiple` of exactly 2.
    #[test]
    fn a_move_depositing_two_indistinguishable_cells_supports_its_class_only_in_multiple() {
        let world = triangle();
        let founded = read_and_realize(
            &world.complex,
            &[fill_twice(&world)],
            &contexts(&world),
            PivotRule::FirstNonzero,
        );
        assert_eq!(
            founded.realizers[0].landings,
            BTreeSet::from([world.t1, world.t2])
        );

        let placed = place_substitutions(&system(&world), &founded, RealizerAdmission::EveryRead);
        let placement = &placed.placement;
        let open = placement
            .open
            .iter()
            .find(|class| class.class == class_of(placement, world.t1))
            .expect("a doubled deposit does not pay integrally");
        assert_eq!(
            open.reached_only_in_multiple,
            Some(BigInt::from(2)),
            "and the factor is returned, not merely the fact of failure"
        );
        assert!(placement.standing.is_empty());
        assert_eq!(
            placement.support.torsion_obstruction(),
            vec![BigInt::from(2)],
            "the integral-versus-rational split, nonzero"
        );
        assert_eq!(
            placement.support.supported_rank, 1,
            "rationally the population spans the face class"
        );
    }

    /// And it dissolves: adding a move that deposits ONE face makes the class integrally reachable.
    /// Without this the `Z/2` could be an artifact of the reduction rather than a statement about
    /// what substitutions can produce.
    #[test]
    fn adding_a_move_that_deposits_one_cell_dissolves_the_doubled_obstruction() {
        let world = triangle();
        let founded = read_and_realize(
            &world.complex,
            &[fill_twice(&world), fill_once(&world)],
            &contexts(&world),
            PivotRule::FirstNonzero,
        );
        let placed = place_substitutions(&system(&world), &founded, RealizerAdmission::EveryRead);
        assert!(
            placed.placement.support.torsion_obstruction().is_empty(),
            "reaching the class singly must remove the Z/2, not merely add to it"
        );
        assert_eq!(
            paid_by(&placed.placement, world.t1),
            vec![RealizerId(0), RealizerId(1)],
            "the face class now stands, paid for by both moves"
        );
    }

    /// The certified remainder a visible move leaves is retained through the adapter and is
    /// nonzero. Filling the circle kills the grade-1 cycle, and the reading says so exactly.
    #[test]
    fn the_certified_remainder_of_a_visible_move_is_retained_and_is_nonzero() {
        let world = triangle();
        let founded = read_and_realize(
            &world.complex,
            &[fill_once(&world)],
            &contexts(&world),
            PivotRule::FirstNonzero,
        );
        let realizer = &founded.realizers[0];
        assert!(
            realizer.admitted_under(RealizerAdmission::Visible),
            "filling a circle is a move the declared contexts can see"
        );
        assert!(!realizer.admitted_under(RealizerAdmission::Invisible));

        let remainder = realizer.remainder();
        assert!(!remainder.is_empty(), "the remainder must not be empty");
        assert!(
            remainder
                .iter()
                .any(|moved| moved.grade == 1 && moved.betti_change == -1),
            "filling the circle removes exactly one grade-1 cycle: {remainder:?}"
        );
        assert_eq!(
            realizer.reading.as_ref().unwrap().distinguishing_contexts(),
            vec![0, 1, 2],
            "every declared context already contains the circle, so all three see this one; the \
             family is separated by `grow_edge` instead"
        );
    }

    /// The declared context family is three readings, not one counted three times — and every
    /// member's exact remainder survives the adapter.
    ///
    /// A mutation truncating `remainder()` to the first verdict survived the whole suite, because
    /// every move the suite read it on gave `ctx union filling` the same subcomplex for every
    /// declared context. Here the three contexts return three *different* answers about one move.
    #[test]
    fn every_declared_contexts_remainder_survives_the_adapter_and_they_are_not_the_same_remainder()
    {
        let world = triangle();
        let founded = read_and_realize(
            &world.complex,
            &[grow_edge(&world)],
            &contexts(&world),
            PivotRule::FirstNonzero,
        );
        let realizer = &founded.realizers[0];
        let reading = realizer.reading.as_ref().expect("the move was read");
        assert_eq!(reading.verdicts.len(), 3);
        assert_ne!(
            reading.verdicts[0].remainder, reading.verdicts[1].remainder,
            "the first two contexts must disagree, or truncating to the first is invisible"
        );
        assert!(
            reading.verdicts[2].remainder.is_empty(),
            "and the whole circle already holds `ab`, so the third sees nothing: {:?}",
            reading.verdicts[2].remainder
        );

        let remainder = realizer.remainder();
        assert_eq!(
            remainder.len(),
            2,
            "one entry from context 0 and one from context 1: {remainder:?}"
        );
        assert_eq!(
            (remainder[0].grade, remainder[0].betti_change),
            (0, -1),
            "against three loose vertices, depositing `ab` joins two components"
        );
        assert_eq!(
            (remainder[1].grade, remainder[1].betti_change),
            (1, 1),
            "against the arc `bc, ca` the same deposit closes a cycle instead"
        );
        assert_eq!(
            reading.distinguishing_contexts(),
            vec![0, 1],
            "a proper subset of the declared family, which is what makes the verdict relative"
        );
        assert!(!realizer.admitted_under(RealizerAdmission::Invisible));
        assert!(realizer.admitted_under(RealizerAdmission::Visible));

        // The deposit carries the family its verdict indices point into.
        assert_eq!(founded.contexts, contexts(&world));
    }

    /// The positive form on this substitution population, evaluated exactly and cross-checked
    /// against `|M x|^2` for an incidence built independently, straight off `Substitution::added()`.
    ///
    /// A bare `x^T (M^T M) x >= 0` loop stood here until 2026-08-08. That is a theorem for every
    /// integer matrix — it passed unchanged against deliberately impossible incidences, negative
    /// landings and all — and it graded nothing. It also carried the probe `[0, 0, 0]`, whose value
    /// is exactly zero, inside a test named for being nonzero.
    #[test]
    fn the_positive_form_agrees_with_an_independently_built_incidence_on_every_probe() {
        let world = triangle();
        let declared = [
            fill_once(&world),
            grow_edge(&world),
            grow_vertex(&world),
            fill_twice(&world),
        ];
        let founded = read_and_realize(
            &world.complex,
            &declared,
            &contexts(&world),
            PivotRule::FirstNonzero,
        );
        let placed = place_substitutions(&system(&world), &founded, RealizerAdmission::EveryRead);
        let placement = &placed.placement;
        let extent = placement.class_extent;
        let realizations = founded
            .realizations_under(RealizerAdmission::EveryRead, &placement.compression.conduct);
        let form = positive_form(&incidence(&realizations, extent));

        // The independent frame: the incidence rebuilt here from the declarations themselves.
        let mut theirs = IntegerMatrix::zeros(declared.len(), extent);
        for (row, substitution) in declared.iter().enumerate() {
            for cell in substitution.added() {
                let class = class_of(placement, cell);
                let carried = theirs.at(row, class) + BigInt::from(1);
                theirs.set(row, class, carried);
            }
        }

        let faces = class_of(placement, world.t1);
        let mut unit = vec![BigInt::zero(); extent];
        unit[faces] = BigInt::from(1);
        assert_eq!(
            quadratic_value(&form, &unit),
            BigInt::from(5),
            "fill_once lands once in the face class and fill_twice lands twice: 1^2 + 2^2"
        );

        let mut probes: Vec<Vec<BigInt>> = vec![
            (0..extent).map(|_| BigInt::from(1)).collect(),
            (0..extent)
                .map(|index| {
                    let magnitude = (index as i64) + 2;
                    BigInt::from(if index % 2 == 0 {
                        magnitude
                    } else {
                        -magnitude
                    })
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
                "the form and the declarations disagree on {probe:?}"
            );
            if !value.is_zero() {
                nonzero += 1;
            }
        }
        assert!(
            nonzero >= 3,
            "the form must be nonzero on the classes the moves paid for, not merely non-negative"
        );
    }

    // ---------------------------------------------------------------------------------------
    // two frames on the same quantity

    /// `place` builds the landings by its own route; this module builds them by another; and the
    /// test counts them by a third, straight off `Substitution::added()`. All three must agree, at
    /// two apertures whose ranks differ — a fixture where they did not differ would let a constant
    /// pass as agreement.
    #[test]
    fn the_incidence_agrees_with_placement_and_with_the_substitutions_themselves() {
        let world = triangle();
        let declared = [
            swap_faces(&world),
            grow_edge(&world),
            grow_vertex(&world),
            fill_twice(&world),
        ];
        let founded = read_and_realize(
            &world.complex,
            &declared,
            &contexts(&world),
            PivotRule::FirstNonzero,
        );

        let mut ranks = BTreeSet::new();
        for admission in [RealizerAdmission::Invisible, RealizerAdmission::EveryRead] {
            let placed = place_substitutions(&system(&world), &founded, admission);
            let placement = &placed.placement;
            let realizations =
                founded.realizations_under(admission, &placement.compression.conduct);
            let matrix = incidence(&realizations, placement.class_extent);
            let rank = smith_normal_form(&matrix, PivotRule::FirstNonzero).rank();
            assert_eq!(
                rank, placement.support.supported_rank,
                "the incidence this module returns must have the rank placement computed"
            );
            ranks.insert(rank);

            // The third frame: count the deposited cells per class straight off the declarations.
            let mut expected = vec![BigInt::zero(); placement.class_extent];
            for realizer in founded.admitted_under(admission) {
                for cell in &declared[realizer.declared].added() {
                    expected[class_of(placement, *cell)] += 1;
                }
            }
            for class in 0..placement.class_extent {
                let mut column = BigInt::zero();
                for row in 0..matrix.rows() {
                    column += matrix.at(row, class);
                }
                assert_eq!(column, expected[class], "class {class} under {admission:?}");
            }
        }
        assert_eq!(
            ranks.len(),
            2,
            "the two apertures must not have the same rank"
        );
    }

    // ---------------------------------------------------------------------------------------
    // the zero controls, each paired with a case that is not zero

    /// A substitution nobody looked at is not invisible. With no context declared the two
    /// receiver-relative apertures admit nothing and every class stays OPEN — and the SAME
    /// population under `EveryRead` closes classes, so the zero is a property of the aperture and
    /// not of the code.
    #[test]
    fn an_empty_context_family_admits_nothing_receiver_relative_and_that_is_not_a_dead_law() {
        let world = triangle();
        let founded = read_and_realize(
            &world.complex,
            &[swap_faces(&world), grow_edge(&world), grow_vertex(&world)],
            &[],
            PivotRule::FirstNonzero,
        );
        assert_eq!(
            founded.realizers.len(),
            3,
            "all three were read without refusal"
        );
        assert!(founded.ids_under(RealizerAdmission::Invisible).is_empty());
        assert!(founded.ids_under(RealizerAdmission::Visible).is_empty());

        let blind = place_substitutions(&system(&world), &founded, RealizerAdmission::Invisible);
        assert!(blind.placement.standing.is_empty());
        assert_eq!(blind.placement.open.len(), 8);

        let seeing = place_substitutions(&system(&world), &founded, RealizerAdmission::EveryRead);
        assert_eq!(
            seeing.placement.standing.len(),
            3,
            "the same substitutions do pay when the aperture does not require a reading"
        );
    }

    /// `Invisible` and `Visible` do not partition `EveryRead`. A move that changes nothing is in
    /// neither, and reporting it as one or the other would be a verdict the reading cannot support.
    #[test]
    fn a_move_that_changes_nothing_is_neither_invisible_nor_visible() {
        let world = triangle();
        let founded = read_and_realize(
            &world.complex,
            &[stand_still(&world), swap_faces(&world), fill_once(&world)],
            &contexts(&world),
            PivotRule::FirstNonzero,
        );
        let still = &founded.realizers[0];
        assert!(!still.admitted_under(RealizerAdmission::Invisible));
        assert!(!still.admitted_under(RealizerAdmission::Visible));
        assert!(still.admitted_under(RealizerAdmission::EveryRead));
        assert!(still.remainder().is_empty());
        assert!(
            still.reaches().is_empty(),
            "and it can never pay for a class"
        );

        let every = founded.ids_under(RealizerAdmission::EveryRead).len();
        let split = founded.ids_under(RealizerAdmission::Invisible).len()
            + founded.ids_under(RealizerAdmission::Visible).len();
        assert_eq!(every, 3);
        assert_eq!(
            split, 2,
            "the two apertures do not cover the declared population"
        );
    }

    /// A declared substitution that is not one is refused, retained, and never becomes a realizer.
    #[test]
    fn a_refused_substitution_is_retained_and_never_pays_for_a_class() {
        let world = triangle();
        // The face without its edges: `after` is not closed under boundary.
        let open_filling = Substitution {
            boundary: BTreeSet::from([world.a, world.b, world.c]),
            before: BTreeSet::from([world.a, world.b, world.c]),
            after: BTreeSet::from([world.a, world.b, world.c, world.t1]),
        };
        let founded = read_and_realize(
            &world.complex,
            &[
                open_filling.clone(),
                swap_faces(&world),
                unshared_boundary(&world),
            ],
            &contexts(&world),
            PivotRule::FirstNonzero,
        );

        assert_eq!(founded.realizers.len(), 1);
        assert_eq!(
            founded.realizers[0].declared, 1,
            "the good one keeps its position"
        );
        assert_eq!(founded.refused.len(), 2);
        assert_eq!(founded.declared_extent(), 3);
        assert!(matches!(
            founded.refused[0].refusal,
            SubstitutionRefusal::NotASubcomplex { .. }
        ));
        assert_eq!(
            founded.refused[1],
            RefusedSubstitution {
                declared: 2,
                substitution: DeclaredSubstitution::from(&unshared_boundary(&world)),
                refusal: SubstitutionRefusal::BoundaryNotShared
            }
        );
        assert_eq!(
            founded.declared_at(0),
            Some(&DeclaredSubstitution::from(&open_filling)),
            "a refused move is still resolvable from its declared position"
        );

        let placed = place_substitutions(&system(&world), &founded, RealizerAdmission::EveryRead);
        assert_eq!(
            placed.placement.standing.len(),
            1,
            "only the substitution that was read pays"
        );
        assert_eq!(placed.placement.support.realizer_extent, 1);
        assert_eq!(
            placed.declared.len(),
            3,
            "and the declared family in the return holds the refused moves too"
        );
    }

    /// A realizer id is its **declared position**, and a placement's `realizers` is the only link
    /// from a standing class back to the move that paid for it.
    ///
    /// Compacting the ids over refusals passed the whole suite: nothing pinned `RealizerId` to
    /// `declared`, so every standing class would have been re-attributed to the wrong move with no
    /// test noticing.
    #[test]
    fn a_placement_names_the_declared_position_of_the_substitution_that_paid() {
        let world = triangle();
        let declared = [
            unshared_boundary(&world),
            grow_vertex(&world),
            unshared_boundary(&world),
            fill_once(&world),
        ];
        let founded = read_and_realize(
            &world.complex,
            &declared,
            &contexts(&world),
            PivotRule::FirstNonzero,
        );
        assert_eq!(
            founded
                .realizers
                .iter()
                .map(|realizer| realizer.realizer)
                .collect::<Vec<_>>(),
            vec![RealizerId(1), RealizerId(3)],
            "the two refusals leave gaps at 0 and 2; the survivors keep their declared positions"
        );
        assert_eq!(
            founded
                .refused
                .iter()
                .map(|refused| refused.declared)
                .collect::<Vec<_>>(),
            vec![0, 2]
        );

        let placed = place_substitutions(&system(&world), &founded, RealizerAdmission::EveryRead);
        assert_eq!(paid_by(&placed.placement, world.d), vec![RealizerId(1)]);
        assert_eq!(paid_by(&placed.placement, world.t1), vec![RealizerId(3)]);

        // And the deposit reads the id back to the move, without the caller that declared it.
        assert_eq!(
            founded.declared_at(3),
            Some(&DeclaredSubstitution::from(&fill_once(&world)))
        );
        assert_eq!(
            founded.declared_at(1),
            Some(&DeclaredSubstitution::from(&grow_vertex(&world)))
        );
        assert_eq!(founded.declared_at(4), None);
    }

    /// A malformed **context** refuses every declared substitution, because `read_substitution`
    /// checks the whole family per call — a context that is not a subcomplex makes every verdict
    /// meaningless, not one of them. The control is the same three moves against a family that is
    /// closed.
    #[test]
    fn a_malformed_context_refuses_every_declared_substitution() {
        let world = triangle();
        let declared = [swap_faces(&world), grow_edge(&world), grow_vertex(&world)];
        // The face without the edges it is attached to.
        let broken = vec![BTreeSet::from([world.a, world.t1])];
        let refused = read_and_realize(&world.complex, &declared, &broken, PivotRule::FirstNonzero);

        assert!(refused.realizers.is_empty(), "not one of them was read");
        assert_eq!(refused.refused.len(), 3);
        for (position, entry) in refused.refused.iter().enumerate() {
            assert_eq!(entry.declared, position);
            assert_eq!(
                entry.refusal,
                SubstitutionRefusal::NotASubcomplex {
                    which: "context".to_owned()
                },
                "the refusal names the context and not the filling"
            );
        }
        assert_eq!(
            refused.contexts, broken,
            "the malformed family is in the deposit"
        );

        let read = read_and_realize(
            &world.complex,
            &declared,
            &contexts(&world),
            PivotRule::FirstNonzero,
        );
        assert_eq!(
            read.realizers.len(),
            3,
            "the same three moves against a closed family are all read, so the refusal is the \
             context and not the moves"
        );
    }

    /// A population declared without a complex has no reading, so the receiver-relative apertures
    /// admit nothing while `EveryRead` still places. Reading `None` as invisible would let an
    /// unexamined move pass as a compression.
    #[test]
    fn an_unread_population_is_never_invisible() {
        let world = triangle();
        let founded = realizers_from_substitutions(&[swap_faces(&world), grow_edge(&world)]);
        assert!(founded.realizers.iter().all(|r| r.reading.is_none()));
        assert!(founded.contexts.is_empty());
        assert!(founded.ids_under(RealizerAdmission::Invisible).is_empty());
        assert!(founded.ids_under(RealizerAdmission::Visible).is_empty());
        assert_eq!(founded.ids_under(RealizerAdmission::EveryRead).len(), 2);

        let placed = place_substitutions(&system(&world), &founded, RealizerAdmission::EveryRead);
        assert_eq!(paid_by(&placed.placement, world.t2), vec![RealizerId(0)]);
        assert_eq!(paid_by(&placed.placement, world.ab), vec![RealizerId(1)]);
        assert_eq!(placed.placement.standing.len(), 2);
        assert_eq!(placed.placement.open.len(), 6);
    }

    /// The population rests, remounts exactly, and the remounted deposit places identically
    /// **against a complex it never met** — a second, independently built copy of the material.
    ///
    /// This is what "an object the machine returns rather than a bookkeeping side-channel" has to
    /// mean operationally: a closure passed to `place` cannot be deposited, re-read, or carried to
    /// another frame, and this can. Re-placing against the same in-memory complex is one frame and
    /// could not have caught a deposit that had kept a reference to it.
    #[test]
    fn the_declared_population_rests_and_the_remounted_deposit_places_against_a_second_complex() {
        let world = triangle();
        let founded = read_and_realize(
            &world.complex,
            &[
                swap_faces(&world),
                fill_twice(&world),
                grow_edge(&world),
                unshared_boundary(&world),
            ],
            &contexts(&world),
            PivotRule::FirstNonzero,
        );
        assert_eq!(
            founded.refused.len(),
            1,
            "a refusal must be in the resting form too"
        );

        let rested = ron::to_string(&founded).expect("the deposit rests");
        let remounted: SubstitutionRealizers = ron::from_str(&rested).expect("and remounts");
        assert_eq!(remounted, founded);

        let elsewhere = triangle();
        for admission in [
            RealizerAdmission::EveryRead,
            RealizerAdmission::Invisible,
            RealizerAdmission::Visible,
        ] {
            assert_eq!(
                place_substitutions(&system(&elsewhere), &remounted, admission),
                place_substitutions(&system(&world), &founded, admission),
                "{admission:?}"
            );
        }
    }

    /// Nothing declared leaves every class OPEN, and never reports a vacuous success.
    ///
    /// `every_standing_class_was_paid_for()` was asserted here until 2026-08-08 and is a theorem
    /// about `place` — vacuously true whenever `standing` is empty, which this test asserts one line
    /// earlier.
    #[test]
    fn nothing_declared_pays_for_nothing() {
        let world = triangle();
        let founded = realizers_from_substitutions(&[]);
        let placed = place_substitutions(&system(&world), &founded, RealizerAdmission::EveryRead);
        assert!(placed.placement.standing.is_empty());
        assert_eq!(placed.placement.open.len(), 8);
        assert!(!placed.placement.closed());
        assert!(!placed.placement.support.fully_supported());
        assert!(placed.declared.is_empty());
        assert!(placed.admitted.is_empty());
    }
}
