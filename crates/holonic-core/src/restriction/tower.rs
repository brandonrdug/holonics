//! The continuing tower, its gluing trichotomy, and the non-invertible transition that carries its
//! residual.
//!
//! # The paired Lean owner
//!
//! [definition] This is the transverse axis of the Holon core's restriction facet `π`
//! ([`crate::restriction`]); it moved here from `crates/holonic-engine/src/continuing_tower.rs`,
//! which re-exports every item at its old path. [`Transition::residual`] is what
//! [`crate::restriction::Descent`] retains when a square or a factoring does not descend.
//!
//! This module is one half of a coupled pair. The other half is
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/ContinuingTower.lean`, namespace
//! `Soma.Holonics.Foundation.ContinuingTower`, which names this file in its header. Every public
//! item below cites the declaration it realizes. The citation is bidirectional on purpose: neither
//! side is a description of the other, and a change on one side that is not carried to the other
//! breaks the pair.
//!
//! | Lean declaration | Rust owner |
//! |---|---|
//! | `Tower` | [`Tower`] |
//! | `Tower.Refines` | [`Tower::refines`] |
//! | `Tower.restrict` | [`Tower::restrict`] |
//! | `Tower.restrict_refl`, `Tower.restrict_trans` | [`check_restriction_laws`] (receipt) |
//! | `Tower.CompatibleSection` | [`CompatibleSection`] |
//! | `Tower.ObservationFibre` | [`ObservationFibre`] |
//! | `Tower.GluingResult`, `Tower.gluingResult_total` | [`GluingResult`], [`glue_chain`] |
//! | `Tower.MaterializedFace` | [`MaterializedFace`] |
//! | `ComputableTower`, `ComputableTower.section` | [`ComputableTower`], [`computable_section`] |
//! | `Transition` | [`Transition`] |
//! | `Transition.comp`, `Transition.comp_residual` | [`ComposedTransition`] |
//! | `Transition.ofEquiv`, `ofEquiv_residual_subsingleton` | [`ExactShift`], [`NoResidual`] |
//! | `Transition.laterReceiverFactors` | [`Transition::reopen_later_receiver`] |
//! | `Transition.residual_separates` | [`Transition::separating_residuals`] |
//! | `Tower.restrictTransition`, `Tower.section_witness_reopened` | [`TowerRestrictTransition`] |
//! | `coarseGrain`, `coarseGrain_comp_residual_pair` | [`CoarseGrain`] |
//! | `padicTower`, `padicTower_plural` | [`ResidueTower`] |
//! | `shiftTower`, `shiftTower_obstructed` | [`ShiftTower`] |
//! | `unitTower`, `unitTower_gluing` | [`UnitTower`] |
//! | `padicSectionEquiv`, `padicFibreEquiv`, `padicFibre_card` | [`FibreSplitting`], [`ResidueTower::split_fibre`] |
//! | `padicDigitGap`, `padicReopenGap` | [`FibreSplitting::coset_index`], [`FibreSplitting::representative`] |
//! | `Migration`, `Migration.naturality` | [`Migration`], [`check_migration_naturality`] |
//! | `Migration.carrySection`, `carrySection_comp` | [`carry_section`], [`ComposedMigration`] |
//! | `Migration.identity`, `rebaseMigration` | [`IdentityMigration`] (zero residual by type) |
//! | `ResidualMigration`, `reopen_apply` | [`ResidualMigration`], [`ResidualMigration::check_reopen`] |
//! | `ResidualMigration.square_either_route_reopens` | [`check_migration_square_reopen`] |
//! | `padicHalfMigration`, `padicHalfMigration_carrySection` | [`HalvingMigration`] |
//! | `Migration.StaysAtItsChart`, `FollowsRefinement`, `ConnectsIncomparableCharts` | [`ChartRoute`], [`check_index_routes`] |
//! | `Migration.FactorsThroughRefinement` | [`check_factors_through_restriction`] |
//! | `Migration.ReversePassage`, `traversability_is_the_residual` | [`check_reverse_passage`] |
//! | `twoChartTower`, `swapMigration`, `twoCharts_no_common_refinement` | [`TwoChartTower`], [`SwapMigration`] |
//!
//! # The first physical consumer
//!
//! `crates/holonic-engine/src/grain_tower.rs` instantiates [`Tower`], [`Transition`] and
//! [`TowerRestrictTransition`] at the grain axis `Component ⊑ Residue ⊑ Atom` of a physical
//! presentation, paired with
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/GrainRestriction.lean`. It founds no
//! second carrier: `check_restriction_laws`, `Transition::check_reopen`,
//! `Transition::reopen_later_receiver` and `Transition::separating_residuals` are the operations it
//! runs on measured data.
//!
//! # What is exact and what is declared
//!
//! No float decides anything here. Faces, residuals, moduli and costs are `num_bigint::BigUint`,
//! `num_bigint::BigInt` or `relational_geometry::Rat`; comparison is `Eq` on those exact carriers.
//!
//! Two things are *declared by the caller* and are not derived, and the Lean side is where their
//! general form lives:
//!
//! * **The chart aperture.** Lean quantifies over every `i ≤ j`. A running program checks a
//!   declared finite chart list and returns a [`RestrictionReceipt`] naming exactly what it
//!   checked. The receipt is the scope of the claim; it is not a proof of the law.
//! * **The section population.** Lean's `CompatibleSection` is the whole continuing object over an
//!   unbounded index. [`glue_chain`] searches a declared finite chain and returns the trichotomy
//!   over that chain, with the exact chart at which an obstruction was met. An `Obstructed` return
//!   therefore names *where* extension failed, which the Lean statement does not need to.
//!
//! A restriction-law violation is a typed [`TowerRefusal`], never a panic, and never a silent
//! repair.

use std::collections::BTreeMap;
use std::fmt::{self, Debug};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use relational_geometry::Rat;

/// Why a tower, a section or a restriction law was refused.
///
/// Lean counterpart: the laws this refuses are `Tower.restrict_refl`, `Tower.restrict_trans` and
/// `Tower.CompatibleSection.compatible`. Lean discharges them as hypotheses of the structure; a
/// running tower must be asked, so every failure is returned as one of these variants instead of
/// aborting.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TowerRefusal<I, F> {
    /// The face is not one the tower presents at that chart, so no law applies to it.
    FaceNotCarried {
        /// The chart the face was offered at.
        chart: I,
        /// The face that is not presented there.
        face: F,
    },
    /// `fine` does not refine `coarse`, so there is no restriction to take.
    NotARefinement {
        /// The claimed coarser chart.
        coarse: I,
        /// The claimed finer chart.
        fine: I,
    },
    /// `Tower.restrict_refl` failed: restricting a chart to itself moved the face.
    RestrictReflFailed {
        /// Where it failed.
        chart: I,
        /// What went in.
        face: F,
        /// What came back.
        returned: F,
    },
    /// `Tower.restrict_trans` failed: two steps disagreed with one.
    RestrictTransFailed {
        /// The coarsest chart.
        coarse: I,
        /// The intermediate chart.
        middle: I,
        /// The finest chart.
        fine: I,
        /// The face at `fine` that was restricted.
        face: F,
        /// What `fine -> middle -> coarse` returned.
        two_step: F,
        /// What `fine -> coarse` returned.
        one_step: F,
    },
    /// `Tower.CompatibleSection.compatible` failed: a finer witness does not restrict to the
    /// coarser one.
    IncompatibleWitness {
        /// The coarser chart.
        coarse: I,
        /// The finer chart.
        fine: I,
        /// What the finer witness restricted to.
        restricted: F,
        /// What the section claims at the coarser chart.
        witness: F,
    },
    /// A chart named by the caller carries no witness in the section.
    ChartMissing {
        /// The chart with no witness.
        chart: I,
    },
    /// The retained observation fibre belongs to a different chart or face than the materialized
    /// presentation. Rust carries these indices as data where Lean carries them in dependent types.
    MaterializedLineageDisagrees {
        /// The materialized chart.
        chart: I,
        /// The materialized face.
        face: F,
        /// The fibre's chart.
        lineage_chart: I,
        /// The fibre's face.
        lineage_face: F,
    },
}

impl<I: Debug, F: Debug> fmt::Display for TowerRefusal<I, F> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FaceNotCarried { chart, face } => write!(
                formatter,
                "the tower presents no face {face:?} at chart {chart:?}"
            ),
            Self::NotARefinement { coarse, fine } => write!(
                formatter,
                "chart {fine:?} does not refine chart {coarse:?}, so there is no restriction"
            ),
            Self::RestrictReflFailed {
                chart,
                face,
                returned,
            } => write!(
                formatter,
                "restrict_refl failed at chart {chart:?}: {face:?} restricted to itself as \
                 {returned:?}"
            ),
            Self::RestrictTransFailed {
                coarse,
                middle,
                fine,
                face,
                two_step,
                one_step,
            } => write!(
                formatter,
                "restrict_trans failed on {coarse:?} <= {middle:?} <= {fine:?} for {face:?}: two \
                 steps returned {two_step:?}, one step returned {one_step:?}"
            ),
            Self::IncompatibleWitness {
                coarse,
                fine,
                restricted,
                witness,
            } => write!(
                formatter,
                "the witness at {fine:?} restricts to {restricted:?} at {coarse:?}, where the \
                 section claims {witness:?}"
            ),
            Self::ChartMissing { chart } => {
                write!(formatter, "the section carries no witness at chart {chart:?}")
            }
            Self::MaterializedLineageDisagrees {
                chart,
                face,
                lineage_chart,
                lineage_face,
            } => write!(
                formatter,
                "materialized chart/face {chart:?}/{face:?} disagrees with lineage \
                 {lineage_chart:?}/{lineage_face:?}"
            ),
        }
    }
}

impl<I: Debug, F: Debug> std::error::Error for TowerRefusal<I, F> {}

/// Exactly which instances of `Tower.restrict_refl` and `Tower.restrict_trans` were checked.
///
/// Lean counterpart: the two fields of `Foundation/ContinuingTower.lean::Tower`. Lean states them
/// for every index; this records the declared finite aperture a program actually asked about.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct RestrictionReceipt<I> {
    /// The `(chart, face-count)` pairs on which `restrict_refl` returned the face unchanged.
    pub reflexive_charts: Vec<I>,
    /// The `(coarse, middle, fine)` triples on which the two-step and one-step restrictions agreed
    /// for at least one supplied face. A triple with no face above it is not recorded.
    pub transitive_triples: Vec<(I, I, I)>,
    /// How many `(chart, face)` pairs were presented.
    pub faces_checked: usize,
}

/// Exactly which refinement pairs of a section were checked for compatibility.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Tower.CompatibleSection.compatible`.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CompatibilityReceipt<I> {
    /// The `(coarse, fine)` pairs whose restriction agreed with the coarser witness.
    pub checked_pairs: Vec<(I, I)>,
}

/// A checked instance of `Transition.reopen_apply`.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Transition.reopen_apply`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct ReopenReceipt {
    /// How many sources were reopened exactly from their transported face and residual.
    pub sources_reopened: usize,
}

/// Why a transition refused.
///
/// Lean counterpart: in Lean `reopen_apply` is a field, so it cannot fail. Here it is asked, and a
/// failure is this value rather than a panic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReopenRefusal<S, T, R> {
    /// The source that was not recovered.
    pub source: S,
    /// What the transition transported.
    pub transported: T,
    /// What it retained.
    pub residual: R,
    /// What reopening actually returned.
    pub reopened: S,
}

impl<S: Debug, T: Debug, R: Debug> fmt::Display for ReopenRefusal<S, T, R> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "reopening {:?} with residual {:?} returned {:?}, not the source {:?}",
            self.transported, self.residual, self.reopened, self.source
        )
    }
}

impl<S: Debug, T: Debug, R: Debug> std::error::Error for ReopenRefusal<S, T, R> {}

/// A family of faces over a refinement order, together with the restriction that carries a finer
/// face to the coarser one it presents.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Tower`. Lean's `Face : Index → Type v` is a
/// dependent family; Rust has one `Face` carrier plus [`Tower::carries`], which decides whether a
/// face is actually presented at a chart. That predicate is how the dependency is checked rather
/// than assumed.
pub trait Tower {
    /// The index of apertures, grains, charts, precisions and environments.
    ///
    /// Lean counterpart: `Tower`'s `Index` parameter.
    type Index: Clone + Ord + Debug;

    /// What is presented at one index.
    ///
    /// Lean counterpart: `Tower.Face`.
    type Face: Clone + Eq + Debug;

    /// `fine` refines `coarse`: a face at `fine` restricts to a face at `coarse`.
    ///
    /// Lean counterpart: `Tower.Refines`, which is the index preorder `i ≤ j`. This must be
    /// reflexive and transitive; [`check_restriction_laws`] checks the restriction laws that
    /// depend on it, not the order itself.
    fn refines(&self, coarse: &Self::Index, fine: &Self::Index) -> bool;

    /// Whether this face is one the tower actually presents at that chart.
    ///
    /// Lean counterpart: in Lean this is the typing `face : Face i` and needs no predicate.
    fn carries(&self, chart: &Self::Index, face: &Self::Face) -> bool;

    /// Carry a face at `fine` to the face it presents at `coarse`.
    ///
    /// Lean counterpart: `Tower.restrict`.
    fn restrict(
        &self,
        coarse: &Self::Index,
        fine: &Self::Index,
        face: &Self::Face,
    ) -> TowerFaceOutcome<Self>;
}

/// A [`Tower`] return `V`, or that tower's own typed [`TowerRefusal`] in its own index and face
/// types.
///
/// The refusal travels in the tower's own `Index`/`Face`, so the alias is written over the tower
/// rather than over the two associated types: `TowerOutcome<T, V>` cannot be instantiated with an
/// index and a face belonging to two different towers.
pub type TowerOutcome<T, V> =
    Result<V, TowerRefusal<<T as Tower>::Index, <T as Tower>::Face>>;

/// The [`Tower::restrict`] return: the restricted face, or the tower's typed refusal.
pub type TowerFaceOutcome<T> = TowerOutcome<T, <T as Tower>::Face>;

/// The [`Transition::check_reopen`] return: a [`ReopenReceipt`], or the transition's own
/// [`ReopenRefusal`] carrying its source, target and residual.
pub type ReopenOutcome<T> = Result<
    ReopenReceipt,
    ReopenRefusal<
        <T as Transition>::Source,
        <T as Transition>::Target,
        <T as Transition>::Residual,
    >,
>;

/// Check `restrict_refl` and `restrict_trans` over a declared chart aperture and face population.
///
/// Lean counterpart: the `restrict_refl` and `restrict_trans` fields of
/// `Foundation/ContinuingTower.lean::Tower`, which Lean carries as proofs. Here they are asked and
/// the answer is a [`RestrictionReceipt`] naming exactly what was checked, or a typed
/// [`TowerRefusal`].
///
/// `faces` supplies `(chart, face)` pairs; every pair is used for `restrict_refl`, and every pair
/// whose chart is the finest member of a refining triple is used for `restrict_trans`.
pub fn check_restriction_laws<T: Tower>(
    tower: &T,
    charts: &[T::Index],
    faces: &[(T::Index, T::Face)],
) -> TowerOutcome<T, RestrictionReceipt<T::Index>> {
    let mut receipt = RestrictionReceipt {
        reflexive_charts: Vec::new(),
        transitive_triples: Vec::new(),
        faces_checked: faces.len(),
    };

    for (chart, face) in faces {
        if !tower.carries(chart, face) {
            return Err(TowerRefusal::FaceNotCarried {
                chart: chart.clone(),
                face: face.clone(),
            });
        }
        let returned = tower.restrict(chart, chart, face)?;
        if &returned != face {
            return Err(TowerRefusal::RestrictReflFailed {
                chart: chart.clone(),
                face: face.clone(),
                returned,
            });
        }
        receipt.reflexive_charts.push(chart.clone());
    }

    for coarse in charts {
        for middle in charts {
            if !tower.refines(coarse, middle) {
                continue;
            }
            for fine in charts {
                if !tower.refines(middle, fine) || !tower.refines(coarse, fine) {
                    continue;
                }
                let mut checked_here = false;
                for (chart, face) in faces {
                    if chart != fine {
                        continue;
                    }
                    let two_step =
                        tower.restrict(coarse, middle, &tower.restrict(middle, fine, face)?)?;
                    let one_step = tower.restrict(coarse, fine, face)?;
                    if two_step != one_step {
                        return Err(TowerRefusal::RestrictTransFailed {
                            coarse: coarse.clone(),
                            middle: middle.clone(),
                            fine: fine.clone(),
                            face: face.clone(),
                            two_step,
                            one_step,
                        });
                    }
                    checked_here = true;
                }
                if checked_here {
                    receipt
                        .transitive_triples
                        .push((coarse.clone(), middle.clone(), fine.clone()));
                }
            }
        }
    }

    Ok(receipt)
}

/// One witness at every chart of a declared aperture, agreeing under every restriction between
/// them. This is the continuing object itself, not any one of its faces.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Tower.CompatibleSection`. Lean's section is
/// total over the index; this one carries the declared charts and the [`CompatibilityReceipt`]
/// naming the refinement pairs that were checked.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompatibleSection<I, F> {
    witnesses: BTreeMap<I, F>,
    receipt: CompatibilityReceipt<I>,
}

impl<I: Clone + Ord + Debug, F: Clone + Eq + Debug> CompatibleSection<I, F> {
    /// Build a section, checking compatibility on every refinement pair among the charts supplied.
    ///
    /// Lean counterpart: inhabiting `Tower.CompatibleSection`, whose `compatible` field is a proof
    /// obligation. Here it is checked and a failure is [`TowerRefusal::IncompatibleWitness`].
    pub fn check<T: Tower<Index = I, Face = F>>(
        tower: &T,
        witnesses: BTreeMap<I, F>,
    ) -> Result<Self, TowerRefusal<I, F>> {
        let mut receipt = CompatibilityReceipt {
            checked_pairs: Vec::new(),
        };
        for (chart, face) in &witnesses {
            if !tower.carries(chart, face) {
                return Err(TowerRefusal::FaceNotCarried {
                    chart: chart.clone(),
                    face: face.clone(),
                });
            }
        }
        for (coarse, coarse_face) in &witnesses {
            for (fine, fine_face) in &witnesses {
                if !tower.refines(coarse, fine) {
                    continue;
                }
                let restricted = tower.restrict(coarse, fine, fine_face)?;
                if &restricted != coarse_face {
                    return Err(TowerRefusal::IncompatibleWitness {
                        coarse: coarse.clone(),
                        fine: fine.clone(),
                        restricted,
                        witness: coarse_face.clone(),
                    });
                }
                receipt.checked_pairs.push((coarse.clone(), fine.clone()));
            }
        }
        Ok(Self { witnesses, receipt })
    }

    /// The face this continuing object presents at one chart.
    ///
    /// Lean counterpart: `Tower.CompatibleSection.witness`.
    pub fn witness(&self, chart: &I) -> Option<&F> {
        self.witnesses.get(chart)
    }

    /// The charts this section carries.
    pub fn charts(&self) -> Vec<I> {
        self.witnesses.keys().cloned().collect()
    }

    /// The refinement pairs whose compatibility was checked.
    ///
    /// Lean counterpart: `Tower.CompatibleSection.compatible`, as a receipt rather than a proof.
    pub fn receipt(&self) -> &CompatibilityReceipt<I> {
        &self.receipt
    }
}

/// Every continuing object retained behind one actually materialized face.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Tower.ObservationFibre`, and — by
/// `Tower.observationFibre_eq_preimageFibre`, which is `rfl` — also
/// `Foundation/Holon.lean::Holon.PreimageFibre` of the restrict-to-chart receiver. The two are one
/// object, so this type has no Rust sibling either.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObservationFibre<I, F> {
    chart: I,
    face: F,
    sections: Vec<CompatibleSection<I, F>>,
}

impl<I: Clone + Ord + Debug, F: Clone + Eq + Debug> ObservationFibre<I, F> {
    /// Collect, from a declared section population, exactly those presenting `face` at `chart`.
    pub fn over(chart: I, face: F, population: &[CompatibleSection<I, F>]) -> Self {
        let sections = population
            .iter()
            .filter(|section| section.witness(&chart) == Some(&face))
            .cloned()
            .collect();
        Self {
            chart,
            face,
            sections,
        }
    }

    /// The chart the face was read at.
    pub fn chart(&self) -> &I {
        &self.chart
    }

    /// The face that was read.
    pub fn face(&self) -> &F {
        &self.face
    }

    /// The retained population behind it. A plural fibre is the ordinary case and is never
    /// collapsed to a representative.
    pub fn sections(&self) -> &[CompatibleSection<I, F>] {
        &self.sections
    }

    /// Whether the fibre is empty over the declared population.
    pub fn is_empty(&self) -> bool {
        self.sections.is_empty()
    }
}

/// A face read at a chart, carrying the lineage of continuing objects behind it.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Tower.MaterializedFace`. A face without its
/// observation fibre is not admitted on either side.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MaterializedFace<I, F> {
    /// Where the face was read.
    chart: I,
    /// What was read.
    face: F,
    /// The retained population behind it.
    lineage: ObservationFibre<I, F>,
}

impl<I: Clone + Eq + Ord + Debug, F: Clone + Eq + Debug> MaterializedFace<I, F> {
    /// Admit a face only with the observation fibre collected over the same chart and face.
    pub fn found(
        chart: I,
        face: F,
        lineage: ObservationFibre<I, F>,
    ) -> Result<Self, TowerRefusal<I, F>> {
        if lineage.chart() != &chart || lineage.face() != &face {
            return Err(TowerRefusal::MaterializedLineageDisagrees {
                chart,
                face,
                lineage_chart: lineage.chart().clone(),
                lineage_face: lineage.face().clone(),
            });
        }
        Ok(Self { chart, face, lineage })
    }

    pub fn chart(&self) -> &I {
        &self.chart
    }

    pub fn face(&self) -> &F {
        &self.face
    }

    pub fn lineage(&self) -> &ObservationFibre<I, F> {
        &self.lineage
    }
}

/// Where a chain refused to extend.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::shiftTower_obstructed` proves emptiness
/// without locating it; a search returns the exact chart at which the extension died.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GluingObstruction<I, F> {
    /// The chart the partial section had reached.
    pub blocking_chart: I,
    /// The face it presented there.
    pub blocking_face: F,
    /// The next chart, which nothing above that face reaches.
    pub unreachable_chart: I,
}

/// The three lawful returns of an attempted global section.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Tower.GluingResult`, whose totality is
/// `Tower.gluingResult_total`. [`glue_chain`] is the executable totality: it returns one of these
/// three for every tower and chain, and never a representative chosen out of a plural fibre.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GluingResult<I, F> {
    /// Exactly one continuing object over the declared chain.
    Unique(CompatibleSection<I, F>),
    /// Several. The plurality is the content and is returned whole.
    Plural(Vec<CompatibleSection<I, F>>),
    /// None, although every chart may be inhabited.
    Obstructed(GluingObstruction<I, F>),
}

/// A tower whose adjacent fibres can be listed exactly.
///
/// Lean counterpart: there is no Lean sibling — Lean quantifies over the fibre without listing it.
/// Listing is what makes [`glue_chain`] executable, so it is a separate, declared capability and
/// not part of [`Tower`].
pub trait EnumerableTower: Tower {
    /// Every face at `fine` that restricts to `face` at `coarse`, exactly and finitely.
    ///
    /// Lean counterpart: the population `SuccessorWitnessSystem.restrict_surjective` asserts to be
    /// nonempty in `Millennium/HolonicDirectedPassage.lean`. An empty return here is precisely the
    /// failure of that hypothesis, which is `shiftTower_adjacent_not_surjective`.
    fn adjacent_preimage(
        &self,
        coarse: &Self::Index,
        fine: &Self::Index,
        face: &Self::Face,
    ) -> TowerOutcome<Self, Vec<Self::Face>>;
}

/// Attempt a global section along a declared refining chain from a declared base face.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Tower.gluingResult_total`. Lean's trichotomy
/// is over the whole index; this one is over `chain`, and an `Obstructed` return names the chart at
/// which extension failed. Every returned section is built and then re-checked with
/// [`CompatibleSection::check`], so compatibility is a receipt and not an invariant of the search.
pub fn glue_chain<T: EnumerableTower>(
    tower: &T,
    chain: &[T::Index],
    base: T::Face,
) -> TowerOutcome<T, GluingResult<T::Index, T::Face>> {
    // An empty chart aperture asks nothing, and the empty family is vacuously its unique
    // compatible section. This is the degenerate case of `Tower.gluingResult_total`, not a result
    // about the tower.
    let Some(first) = chain.first() else {
        return Ok(GluingResult::Unique(CompatibleSection {
            witnesses: BTreeMap::new(),
            receipt: CompatibilityReceipt {
                checked_pairs: Vec::new(),
            },
        }));
    };
    if !tower.carries(first, &base) {
        return Err(TowerRefusal::FaceNotCarried {
            chart: first.clone(),
            face: base,
        });
    }

    let mut partial: Vec<Vec<T::Face>> = vec![vec![base.clone()]];
    for window in chain.windows(2) {
        let (coarse, fine) = (&window[0], &window[1]);
        let mut extended: Vec<Vec<T::Face>> = Vec::new();
        for prefix in &partial {
            let head = prefix
                .last()
                .expect("a partial section always carries its base");
            let preimage = tower.adjacent_preimage(coarse, fine, head)?;
            if preimage.is_empty() {
                return Ok(GluingResult::Obstructed(GluingObstruction {
                    blocking_chart: coarse.clone(),
                    blocking_face: head.clone(),
                    unreachable_chart: fine.clone(),
                }));
            }
            for face in preimage {
                let mut next = prefix.clone();
                next.push(face);
                extended.push(next);
            }
        }
        partial = extended;
    }

    let mut sections = Vec::with_capacity(partial.len());
    for faces in partial {
        let witnesses: BTreeMap<T::Index, T::Face> =
            chain.iter().cloned().zip(faces.into_iter()).collect();
        sections.push(CompatibleSection::check(tower, witnesses)?);
    }

    Ok(match sections.len() {
        0 => GluingResult::Obstructed(GluingObstruction {
            blocking_chart: first.clone(),
            blocking_face: base,
            unreachable_chart: chain.last().cloned().unwrap_or_else(|| first.clone()),
        }),
        1 => GluingResult::Unique(
            sections
                .pop()
                .expect("a one-element population has one element"),
        ),
        _ => GluingResult::Plural(sections),
    })
}

/// One retained state from which every chart's face is materialized on demand.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::ComputableTower`. Lean's
/// `materialize_compatible` is a field; here it is checked by [`computable_section`].
pub trait ComputableTower: Tower {
    /// The retained state the faces are generated from.
    ///
    /// Lean counterpart: `ComputableTower.State`.
    type State;

    /// Generate the face at one chart.
    ///
    /// Lean counterpart: `ComputableTower.materialize`.
    fn materialize(
        &self,
        state: &Self::State,
        chart: &Self::Index,
    ) -> TowerFaceOutcome<Self>;

    /// The declared exact work of materializing one chart.
    ///
    /// Lean counterpart: `ComputableTower.cost`. It is a declared cost, not a measurement.
    fn cost(&self, state: &Self::State, chart: &Self::Index) -> BigUint;
}

/// Materialize one state at every chart of a declared aperture and check that the result is a
/// compatible section.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::ComputableTower.section`, where
/// `materialize_compatible` supplies the compatibility directly. Here the check is performed and
/// a failure is [`TowerRefusal::IncompatibleWitness`].
pub fn computable_section<C: ComputableTower>(
    tower: &C,
    state: &C::State,
    charts: &[C::Index],
) -> TowerOutcome<C, CompatibleSection<C::Index, C::Face>> {
    let mut witnesses = BTreeMap::new();
    for chart in charts {
        witnesses.insert(chart.clone(), tower.materialize(state, chart)?);
    }
    CompatibleSection::check(tower, witnesses)
}

/// A chart map that need not be invertible, carrying the part of the source it does not transport.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Transition`. [`Transition::apply`] is what
/// is transported, [`Transition::residual`] is what is dropped and retained, and
/// [`Transition::reopen`] is the executable reconstruction. `reopen_apply` is the law that makes
/// the residual *exactly* the dropped part — not an upper bound, not a score — and
/// [`Transition::check_reopen`] returns it as a receipt.
///
/// Outside the image of `apply`, `reopen` returns whatever the implementation supplies; only
/// presented pairs `(apply(x), residual(x))` carry the law, exactly as in the Lean docstring.
pub trait Transition {
    /// The chart the transition leaves.
    type Source: Clone + Eq + Debug;
    /// The chart it arrives at.
    type Target: Clone + Eq + Debug;
    /// What it does not transport.
    ///
    /// Lean counterpart: `Transition.Residual`.
    type Residual: Clone + Eq + Debug;

    /// What the transition transports.
    ///
    /// Lean counterpart: `Transition.apply`.
    fn apply(&self, source: &Self::Source) -> Self::Target;

    /// What it drops, retained.
    ///
    /// Lean counterpart: `Transition.residual`.
    fn residual(&self, source: &Self::Source) -> Self::Residual;

    /// Reconstruct a source from a transported face and the retained residual.
    ///
    /// Lean counterpart: `Transition.reopen`.
    fn reopen(&self, target: &Self::Target, residual: &Self::Residual) -> Self::Source;

    /// Check `reopen(apply(x), residual(x)) = x` at one source.
    ///
    /// Lean counterpart: `Transition.reopen_apply`, which is a field and cannot fail; here it is
    /// asked and a failure is a [`ReopenRefusal`].
    fn check_reopen(
        &self,
        source: &Self::Source,
    ) -> ReopenOutcome<Self> {
        let transported = self.apply(source);
        let residual = self.residual(source);
        let reopened = self.reopen(&transported, &residual);
        if &reopened == source {
            Ok(ReopenReceipt {
                sources_reopened: 1,
            })
        } else {
            Err(ReopenRefusal {
                source: source.clone(),
                transported,
                residual,
                reopened,
            })
        }
    }

    /// Read any later, finer receiver off the transported face together with the residual.
    ///
    /// Lean counterpart: `Foundation/ContinuingTower.lean::Transition.laterReceiverFactors` — the
    /// sufficiency half of "the residual is exactly what a later finer receiver can reopen".
    fn reopen_later_receiver<Fine>(
        &self,
        transported: &Self::Target,
        residual: &Self::Residual,
        finer: &dyn Fn(&Self::Source) -> Fine,
    ) -> Fine {
        finer(&self.reopen(transported, residual))
    }

    /// When two distinct sources are merged by the transported face, return the residuals that
    /// still separate them.
    ///
    /// Lean counterpart: `Foundation/ContinuingTower.lean::Transition.residual_separates` and
    /// `Transition.residual_separates_insufficiency` — the necessity half. A `Some` whose two
    /// residuals were equal would contradict `Transition.apply_residual_injective`, so
    /// [`Transition::check_reopen`] on either source is the receipt that they differ.
    fn separating_residuals(
        &self,
        left: &Self::Source,
        right: &Self::Source,
    ) -> Option<(Self::Residual, Self::Residual)> {
        if left != right && self.apply(left) == self.apply(right) {
            Some((self.residual(left), self.residual(right)))
        } else {
            None
        }
    }
}

/// The residual of a transition that drops nothing.
///
/// Lean counterpart: the `PUnit` residual of `Foundation/ContinuingTower.lean::Transition.ofEquiv`,
/// whose subsingleton-ness is `Transition.ofEquiv_residual_subsingleton`. This type has one value,
/// so "zero residual" is a fact about the type and not a runtime check.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct NoResidual;

/// The composite of two transitions. Its residual **is** the pair of component residuals.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Transition.comp`, and the equation
/// `Transition.comp_residual`, which holds by `rfl` there and by the `Residual` associated type
/// here. Associativity up to reassociation of the pair is
/// `Transition.compAssocResidualEquiv`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ComposedTransition<Second, First> {
    /// The transition applied second.
    pub second: Second,
    /// The transition applied first.
    pub first: First,
}

impl<Second, First> ComposedTransition<Second, First> {
    /// Compose, second after first.
    ///
    /// Lean counterpart: `Transition.comp`.
    pub fn new(second: Second, first: First) -> Self {
        Self { second, first }
    }
}

impl<Second, First> Transition for ComposedTransition<Second, First>
where
    Second: Transition,
    First: Transition<Target = Second::Source>,
{
    type Source = First::Source;
    type Target = Second::Target;
    type Residual = (Second::Residual, First::Residual);

    fn apply(&self, source: &Self::Source) -> Self::Target {
        self.second.apply(&self.first.apply(source))
    }

    fn residual(&self, source: &Self::Source) -> Self::Residual {
        (
            self.second.residual(&self.first.apply(source)),
            self.first.residual(source),
        )
    }

    fn reopen(&self, target: &Self::Target, residual: &Self::Residual) -> Self::Source {
        self.first
            .reopen(&self.second.reopen(target, &residual.0), &residual.1)
    }
}

/// Exact coarse graining by a positive modulus: transport the quotient, retain the remainder.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::coarseGrain`. The composition law is
/// `coarseGrain_comp_apply` and `coarseGrain_comp_residual`; the lossiness is
/// `coarseGrain_not_injective`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoarseGrain {
    modulus: BigUint,
}

impl CoarseGrain {
    /// Build a coarse graining. A zero modulus is refused: the Lean owner admits it because Lean's
    /// `x / 0 = 0` is total, but a zero grain carries no information and is never what a caller
    /// meant.
    pub fn new(modulus: BigUint) -> Option<Self> {
        if modulus.is_zero() {
            None
        } else {
            Some(Self { modulus })
        }
    }

    /// The grain.
    pub fn modulus(&self) -> &BigUint {
        &self.modulus
    }
}

impl Transition for CoarseGrain {
    type Source = BigUint;
    type Target = BigUint;
    type Residual = BigUint;

    fn apply(&self, source: &BigUint) -> BigUint {
        source / &self.modulus
    }

    fn residual(&self, source: &BigUint) -> BigUint {
        source % &self.modulus
    }

    fn reopen(&self, target: &BigUint, residual: &BigUint) -> BigUint {
        &self.modulus * target + residual
    }
}

/// An exact translation of the integers: invertible, so its residual is [`NoResidual`].
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Transition.ofEquiv` instantiated at an
/// integer translation, with `Transition.ofEquiv_residual_subsingleton` as the zero-residual law.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExactShift {
    offset: BigInt,
}

impl ExactShift {
    /// Translate by `offset`.
    pub fn new(offset: BigInt) -> Self {
        Self { offset }
    }
}

impl Transition for ExactShift {
    type Source = BigInt;
    type Target = BigInt;
    type Residual = NoResidual;

    fn apply(&self, source: &BigInt) -> BigInt {
        source + &self.offset
    }

    fn residual(&self, _source: &BigInt) -> NoResidual {
        NoResidual
    }

    fn reopen(&self, target: &BigInt, _residual: &NoResidual) -> BigInt {
        target - &self.offset
    }
}

/// The floor chart on the exact rationals: transport the integer part, retain the exact fraction.
///
/// Lean counterpart: an instance of `Foundation/ContinuingTower.lean::Transition` with a nontrivial
/// residual over an ordered field; the general laws it satisfies are `Transition.reopen_apply` and
/// `Transition.laterReceiverFactors`. No float participates: the residual is a
/// `relational_geometry::Rat`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct RationalFloor;

impl Transition for RationalFloor {
    type Source = Rat;
    type Target = BigInt;
    type Residual = Rat;

    fn apply(&self, source: &Rat) -> BigInt {
        source.floor().to_integer()
    }

    fn residual(&self, source: &Rat) -> Rat {
        source - Rat::from_integer(source.floor().to_integer())
    }

    fn reopen(&self, target: &BigInt, residual: &Rat) -> Rat {
        Rat::from_integer(target.clone()) + residual
    }
}

/// A tower whose restrictions are presented as transitions carrying their residual.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Tower.restrictTransition`, where the
/// residual must be *supplied*: the tower's laws say what restriction preserves, never what it
/// drops. `Tower.section_witness_reopened` is [`TowerRestrictTransition::check_section_reopen`].
pub trait TowerRestrictTransition: Tower {
    /// What the restriction from `fine` to `coarse` drops.
    ///
    /// Lean counterpart: the `Residual` argument of `Tower.restrictTransition`.
    type RestrictionResidual: Clone + Eq + Debug;

    /// Retain the dropped part of one restriction.
    fn restriction_residual(
        &self,
        coarse: &Self::Index,
        fine: &Self::Index,
        fine_face: &Self::Face,
    ) -> TowerOutcome<Self, Self::RestrictionResidual>;

    /// Reopen the fine face from the coarse face and the residual.
    fn restriction_reopen(
        &self,
        coarse: &Self::Index,
        fine: &Self::Index,
        coarse_face: &Self::Face,
        residual: &Self::RestrictionResidual,
    ) -> TowerFaceOutcome<Self>;

    /// Check that a continuing object's coarse face and the restriction's residual return its fine
    /// face exactly.
    ///
    /// Lean counterpart: `Foundation/ContinuingTower.lean::Tower.section_witness_reopened`.
    fn check_section_reopen(
        &self,
        coarse: &Self::Index,
        fine: &Self::Index,
        section: &CompatibleSection<Self::Index, Self::Face>,
    ) -> TowerOutcome<Self, ReopenReceipt>
    where
        Self: Sized,
    {
        let coarse_face = section
            .witness(coarse)
            .ok_or_else(|| TowerRefusal::ChartMissing {
                chart: coarse.clone(),
            })?;
        let fine_face = section
            .witness(fine)
            .ok_or_else(|| TowerRefusal::ChartMissing {
                chart: fine.clone(),
            })?;
        let residual = self.restriction_residual(coarse, fine, fine_face)?;
        let reopened = self.restriction_reopen(coarse, fine, coarse_face, &residual)?;
        if &reopened == fine_face {
            Ok(ReopenReceipt {
                sources_reopened: 1,
            })
        } else {
            Err(TowerRefusal::IncompatibleWitness {
                coarse: coarse.clone(),
                fine: fine.clone(),
                restricted: reopened,
                witness: fine_face.clone(),
            })
        }
    }
}

/// Why an exact fibre splitting was refused.
///
/// Lean counterpart: the hypotheses of
/// `Foundation/ContinuingTower.lean::padicFibreEquiv` and `padicFibre_card`, which Lean discharges
/// by typing (`face : ZMod (p ^ m)` and `m ≤ m + k` are given). A running program is asked with
/// values it did not choose, so every failure is returned as one of these variants instead of
/// allocating an unbounded carrier or aborting.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SplittingRefusal {
    /// `fine` does not refine `coarse`, so there is no fibre to split.
    NotARefinement {
        /// The claimed coarser chart.
        coarse: u32,
        /// The claimed finer chart.
        fine: u32,
    },
    /// The face offered is not one the coarse chart presents.
    FaceNotCarried {
        /// The chart the face was offered at.
        chart: u32,
        /// The face that is not presented there.
        face: BigUint,
    },
    /// The fine chart's carrier is wider than the caller's declared ceiling. This is returned
    /// *before* any carrier of that width is allocated; see [`ResidueTower::coset_count_bits`].
    CarrierAboveCeiling {
        /// The coarser chart.
        coarse: u32,
        /// The finer chart.
        fine: u32,
        /// How many bits the fine chart's modulus would occupy.
        carrier_bits: u128,
        /// What the caller declared it would accept.
        ceiling_bits: u128,
    },
    /// The coset index named is not one of the splitting's cosets.
    CosetIndexOutOfRange {
        /// The index asked for.
        requested: BigUint,
        /// How many cosets there are.
        coset_count: BigUint,
    },
    /// The fine face offered does not lie in this fibre.
    NotInFibre {
        /// The face the fibre sits over.
        coarse_face: BigUint,
        /// The fine face that was offered.
        fine_face: BigUint,
        /// What that fine face actually restricts to.
        restricted: BigUint,
    },
    /// Listing the cosets would produce more of them than the caller declared it would accept.
    EnumerationAboveCeiling {
        /// How many cosets there are.
        coset_count: BigUint,
        /// What the caller declared it would accept.
        ceiling: u64,
    },
}

impl fmt::Display for SplittingRefusal {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotARefinement { coarse, fine } => write!(
                formatter,
                "chart {fine} does not refine chart {coarse}, so there is no fibre to split"
            ),
            Self::FaceNotCarried { chart, face } => {
                write!(formatter, "the tower presents no face {face} at chart {chart}")
            }
            Self::CarrierAboveCeiling {
                coarse,
                fine,
                carrier_bits,
                ceiling_bits,
            } => write!(
                formatter,
                "splitting the fibre from chart {coarse} to chart {fine} needs a {carrier_bits}-bit \
                 carrier, above the declared ceiling of {ceiling_bits} bits"
            ),
            Self::CosetIndexOutOfRange {
                requested,
                coset_count,
            } => write!(
                formatter,
                "coset index {requested} is not one of the {coset_count} cosets of this fibre"
            ),
            Self::NotInFibre {
                coarse_face,
                fine_face,
                restricted,
            } => write!(
                formatter,
                "the fine face {fine_face} restricts to {restricted}, not to {coarse_face}, so it \
                 is not in this fibre"
            ),
            Self::EnumerationAboveCeiling {
                coset_count,
                ceiling,
            } => write!(
                formatter,
                "listing {coset_count} cosets is above the declared ceiling of {ceiling}"
            ),
        }
    }
}

impl std::error::Error for SplittingRefusal {}

/// The exact splitting of one fibre of a [`ResidueTower`] restriction into its cosets.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::padicFibreEquiv`, the bijection between the
/// fibre over a level-`m` face and `ZMod (p ^ k)` at level `m + k`, together with
/// `padicFibre_card`, which fixes the count at `p ^ k` exactly. [`Self::coset_index`] is Lean's
/// `padicDigitGap` and [`Self::representative`] is Lean's `padicReopenGap`; their two round trips
/// are `padicDigitGap_reopenGap` and `padicReopenGap_restrict`.
///
/// Everything here is `BigUint`. The count is an exact integer, never a float, a logarithm or an
/// asymptotic estimate, and the cosets are never enumerated unless a caller asks for them with a
/// declared ceiling.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FibreSplitting {
    coarse: u32,
    fine: u32,
    coarse_face: BigUint,
    coset_count: BigUint,
    coset_stride: BigUint,
}

impl FibreSplitting {
    /// The coarser chart the fibre sits over.
    pub fn coarse_chart(&self) -> u32 {
        self.coarse
    }

    /// The finer chart the fibre lives in.
    pub fn fine_chart(&self) -> u32 {
        self.fine
    }

    /// The face the fibre sits over.
    pub fn coarse_face(&self) -> &BigUint {
        &self.coarse_face
    }

    /// Exactly how many cosets the fibre splits into: `base ^ (fine - coarse)`.
    ///
    /// Lean counterpart: `padicFibre_card`, which is `p ^ k` on the nose.
    pub fn coset_count(&self) -> &BigUint {
        &self.coset_count
    }

    /// The step between consecutive coset representatives: the coarse chart's modulus
    /// `base ^ coarse`, which is also the modulus of `ker` at the coarse chart.
    pub fn coset_stride(&self) -> &BigUint {
        &self.coset_stride
    }

    /// The representative of one coset, exactly.
    ///
    /// Lean counterpart: `padicReopenGap`, whose defining laws are `padicRestrict_reopenGap` (the
    /// representative really restricts back to the coarse face) and `padicDigitGap_reopenGap` (its
    /// coset index is the one it was built from).
    pub fn representative(&self, coset_index: &BigUint) -> Result<BigUint, SplittingRefusal> {
        if coset_index >= &self.coset_count {
            return Err(SplittingRefusal::CosetIndexOutOfRange {
                requested: coset_index.clone(),
                coset_count: self.coset_count.clone(),
            });
        }
        Ok(&self.coarse_face + coset_index * &self.coset_stride)
    }

    /// Which coset a fine face sits in, exactly.
    ///
    /// Lean counterpart: `padicDigitGap`, and — because it is the residual of
    /// `padicRestrictTransition` — `padicRestrictTransition_residual`. A fine face outside the
    /// fibre is a typed refusal, which is Lean's typing hypothesis asked at runtime.
    pub fn coset_index(&self, fine_face: &BigUint) -> Result<BigUint, SplittingRefusal> {
        let restricted = fine_face % &self.coset_stride;
        if restricted != self.coarse_face {
            return Err(SplittingRefusal::NotInFibre {
                coarse_face: self.coarse_face.clone(),
                fine_face: fine_face.clone(),
                restricted,
            });
        }
        let index = fine_face / &self.coset_stride;
        if index >= self.coset_count {
            return Err(SplittingRefusal::CosetIndexOutOfRange {
                requested: index,
                coset_count: self.coset_count.clone(),
            });
        }
        Ok(index)
    }

    /// List every coset representative, refusing above a declared ceiling.
    ///
    /// Lean counterpart: there is none — Lean quantifies over the fibre without listing it. Listing
    /// is what makes the splitting executable, so it carries the caller's declared aperture.
    pub fn enumerate(&self, ceiling: u64) -> Result<Vec<BigUint>, SplittingRefusal> {
        if self.coset_count > BigUint::from(ceiling) {
            return Err(SplittingRefusal::EnumerationAboveCeiling {
                coset_count: self.coset_count.clone(),
                ceiling,
            });
        }
        let mut representatives = Vec::new();
        let mut index = BigUint::zero();
        while index < self.coset_count {
            representatives.push(&self.coarse_face + &index * &self.coset_stride);
            index += BigUint::one();
        }
        Ok(representatives)
    }
}

/// The residue tower: the face at level `n` is an exact representative modulo `base^n`.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::padicTower`, whose plurality is
/// `padicTower_plural` and whose surjective restrictions are `padicTower_restrict_surjective`.
/// Nothing here claims the `ℤ_p ≃ CompatibleSection` equivalence, which is carrier item **C2** and
/// is unowned on both sides.
///
/// # The chart index is the caller's declaration, and it sizes the allocation
///
/// [established-bounded; measured] The chart index of this tower **is** the exponent: the face
/// carrier at level `n` is `base^n`, an arbitrary-precision integer of exactly
/// [`Self::modulus_bits`] bits. That is the mathematics of a residue tower, not a defect of this
/// implementation, so [`Self::modulus`] is left total and exact: it has no failure arm, and every
/// level a caller names is a level this tower really presents.
///
/// The consequence is that the *caller* owns the bound. A chart index taken from untrusted or
/// deserialized material must be measured with [`Self::modulus_bits`] — which is a multiplication
/// on two integers and allocates nothing — and refused against the caller's own declared ceiling
/// **before** it reaches [`Self::modulus`], [`Tower::carries`], [`Tower::restrict`] or
/// [`EnumerableTower::adjacent_preimage`]. `u32::MAX` at base two is a half-gigabyte carrier;
/// at a larger base it is larger still.
///
/// No bound is imposed here because there is no bound to impose: `Tower::carries` returns `bool`
/// and `Tower::restrict` returns the tower's face, exactly as `Foundation/ContinuingTower.lean`
/// types them, and a ceiling that this tower invented would be a magic number in the middle of an
/// exact construction rather than a declared receiver aperture.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResidueTower {
    base: BigUint,
}

impl ResidueTower {
    /// Build the tower over a base of at least two. A base of zero or one carries no plurality.
    pub fn new(base: BigUint) -> Option<Self> {
        if base < BigUint::from(2u32) {
            None
        } else {
            Some(Self { base })
        }
    }

    /// The modulus `base^level` of one chart. Total and exact at every level.
    ///
    /// The allocation this performs is [`Self::modulus_bits`] bits wide. A caller holding a chart
    /// index it did not itself declare measures that first; see the type's own documentation.
    pub fn modulus(&self, level: u32) -> BigUint {
        self.base.pow(level)
    }

    /// Exactly how many bits [`Self::modulus`] would allocate at `level`, without allocating them.
    ///
    /// `base^level` occupies `level * (base.bits() - 1) + 1` bits at the low end and
    /// `level * base.bits()` bits at the high end; this returns the high end, so it is an upper
    /// bound a caller may compare against its own declared ceiling. Zero at `level = 0`, where the
    /// modulus is `1`. The product is taken in `u128`, which `u32 * u64` cannot overflow.
    pub fn modulus_bits(&self, level: u32) -> u128 {
        u128::from(level) * u128::from(self.base.bits())
    }

    /// The base.
    pub fn base(&self) -> &BigUint {
        &self.base
    }

    /// Exactly how many bits the coset count of one fibre occupies, **without** allocating it.
    ///
    /// Lean counterpart: the exponent `k` of `padicFibre_card`'s `p ^ k`, measured rather than
    /// built. Like [`Self::modulus_bits`] this is a product in `u128`, which `u32 * u64` cannot
    /// overflow, and it is the measurement a caller holding an untrusted chart index compares
    /// against its own ceiling before calling [`Self::split_fibre`].
    pub fn coset_count_bits(&self, coarse: u32, fine: u32) -> Result<u128, SplittingRefusal> {
        if !self.refines(&coarse, &fine) {
            return Err(SplittingRefusal::NotARefinement { coarse, fine });
        }
        Ok(u128::from(fine - coarse) * u128::from(self.base.bits()))
    }

    /// Split one fibre into its exact cosets, refusing above a declared carrier ceiling.
    ///
    /// Lean counterpart: `Foundation/ContinuingTower.lean::padicFibreEquiv` together with
    /// `padicFibre_card`. Lean's fibre is `{ x : ZMod (p ^ (m + k)) // restrict x = face }` and its
    /// cardinality is `p ^ k`; the returned [`FibreSplitting`] carries that count as an exact
    /// `BigUint` and both directions of the bijection as [`FibreSplitting::representative`] and
    /// [`FibreSplitting::coset_index`].
    ///
    /// `ceiling_bits` is the caller's declared aperture on the *fine* chart's carrier, measured by
    /// [`Self::modulus_bits`]. It is checked before anything of that width is built, so a chart
    /// index taken from hostile or deserialized material returns
    /// [`SplittingRefusal::CarrierAboveCeiling`] rather than exhausting memory.
    pub fn split_fibre(
        &self,
        coarse: u32,
        fine: u32,
        coarse_face: &BigUint,
        ceiling_bits: u128,
    ) -> Result<FibreSplitting, SplittingRefusal> {
        if !self.refines(&coarse, &fine) {
            return Err(SplittingRefusal::NotARefinement { coarse, fine });
        }
        let carrier_bits = self.modulus_bits(fine);
        if carrier_bits > ceiling_bits {
            return Err(SplittingRefusal::CarrierAboveCeiling {
                coarse,
                fine,
                carrier_bits,
                ceiling_bits,
            });
        }
        let coset_stride = self.modulus(coarse);
        if coarse_face >= &coset_stride {
            return Err(SplittingRefusal::FaceNotCarried {
                chart: coarse,
                face: coarse_face.clone(),
            });
        }
        Ok(FibreSplitting {
            coarse,
            fine,
            coarse_face: coarse_face.clone(),
            coset_count: self.modulus(fine - coarse),
            coset_stride,
        })
    }
}

impl Tower for ResidueTower {
    type Index = u32;
    type Face = BigUint;

    fn refines(&self, coarse: &u32, fine: &u32) -> bool {
        coarse <= fine
    }

    fn carries(&self, chart: &u32, face: &BigUint) -> bool {
        face < &self.modulus(*chart)
    }

    fn restrict(
        &self,
        coarse: &u32,
        fine: &u32,
        face: &BigUint,
    ) -> Result<BigUint, TowerRefusal<u32, BigUint>> {
        if !self.refines(coarse, fine) {
            return Err(TowerRefusal::NotARefinement {
                coarse: *coarse,
                fine: *fine,
            });
        }
        if !self.carries(fine, face) {
            return Err(TowerRefusal::FaceNotCarried {
                chart: *fine,
                face: face.clone(),
            });
        }
        Ok(face % self.modulus(*coarse))
    }
}

impl EnumerableTower for ResidueTower {
    fn adjacent_preimage(
        &self,
        coarse: &u32,
        fine: &u32,
        face: &BigUint,
    ) -> Result<Vec<BigUint>, TowerRefusal<u32, BigUint>> {
        if !self.refines(coarse, fine) {
            return Err(TowerRefusal::NotARefinement {
                coarse: *coarse,
                fine: *fine,
            });
        }
        if !self.carries(coarse, face) {
            return Err(TowerRefusal::FaceNotCarried {
                chart: *coarse,
                face: face.clone(),
            });
        }
        let coarse_modulus = self.modulus(*coarse);
        let cosets = self.modulus(fine - coarse);
        let mut faces = Vec::new();
        let mut digit = BigUint::zero();
        while digit < cosets {
            faces.push(face + &digit * &coarse_modulus);
            digit += BigUint::one();
        }
        Ok(faces)
    }
}

impl ComputableTower for ResidueTower {
    /// One exact integer standing for the continuing object. Lean counterpart: the `ℤ_p` argument
    /// of `padicSection`, restricted to the integers a program can hold.
    type State = BigUint;

    fn materialize(
        &self,
        state: &BigUint,
        chart: &u32,
    ) -> Result<BigUint, TowerRefusal<u32, BigUint>> {
        Ok(state % self.modulus(*chart))
    }

    fn cost(&self, _state: &BigUint, chart: &u32) -> BigUint {
        BigUint::from(*chart)
    }
}

impl TowerRestrictTransition for ResidueTower {
    /// Which coset of `ker` the fine face sits in: the exact digit block the restriction drops.
    type RestrictionResidual = BigUint;

    fn restriction_residual(
        &self,
        coarse: &u32,
        fine: &u32,
        fine_face: &BigUint,
    ) -> Result<BigUint, TowerRefusal<u32, BigUint>> {
        if !self.refines(coarse, fine) {
            return Err(TowerRefusal::NotARefinement {
                coarse: *coarse,
                fine: *fine,
            });
        }
        if !self.carries(fine, fine_face) {
            return Err(TowerRefusal::FaceNotCarried {
                chart: *fine,
                face: fine_face.clone(),
            });
        }
        Ok(fine_face / self.modulus(*coarse))
    }

    fn restriction_reopen(
        &self,
        coarse: &u32,
        fine: &u32,
        coarse_face: &BigUint,
        residual: &BigUint,
    ) -> Result<BigUint, TowerRefusal<u32, BigUint>> {
        if !self.refines(coarse, fine) {
            return Err(TowerRefusal::NotARefinement {
                coarse: *coarse,
                fine: *fine,
            });
        }
        Ok(coarse_face + residual * self.modulus(*coarse))
    }
}

/// The shift tower: every chart carries the natural numbers, and restriction adds the depth
/// difference. Every chart is inhabited and no continuing object exists.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::shiftTower`, with `shiftTower_obstructed`
/// and `shiftTower_adjacent_not_surjective`. This is the Mittag-Leffler failure: the images shrink
/// without limit, so the obstruction is not a defect of any single chart.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct ShiftTower;

impl Tower for ShiftTower {
    type Index = u32;
    type Face = BigUint;

    fn refines(&self, coarse: &u32, fine: &u32) -> bool {
        coarse <= fine
    }

    fn carries(&self, _chart: &u32, _face: &BigUint) -> bool {
        true
    }

    fn restrict(
        &self,
        coarse: &u32,
        fine: &u32,
        face: &BigUint,
    ) -> Result<BigUint, TowerRefusal<u32, BigUint>> {
        if !self.refines(coarse, fine) {
            return Err(TowerRefusal::NotARefinement {
                coarse: *coarse,
                fine: *fine,
            });
        }
        Ok(face + BigUint::from(fine - coarse))
    }
}

impl EnumerableTower for ShiftTower {
    fn adjacent_preimage(
        &self,
        coarse: &u32,
        fine: &u32,
        face: &BigUint,
    ) -> Result<Vec<BigUint>, TowerRefusal<u32, BigUint>> {
        if !self.refines(coarse, fine) {
            return Err(TowerRefusal::NotARefinement {
                coarse: *coarse,
                fine: *fine,
            });
        }
        let gap = BigUint::from(fine - coarse);
        Ok(if face < &gap {
            Vec::new()
        } else {
            vec![face - gap]
        })
    }
}

/// The trivial tower: one face at every chart.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::unitTower`, whose verdict is
/// `unitTower_gluing`. It inhabits the `Unique` arm so that all three arms have witnesses.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct UnitTower;

impl Tower for UnitTower {
    type Index = u32;
    type Face = ();

    fn refines(&self, coarse: &u32, fine: &u32) -> bool {
        coarse <= fine
    }

    fn carries(&self, _chart: &u32, _face: &()) -> bool {
        true
    }

    fn restrict(
        &self,
        coarse: &u32,
        fine: &u32,
        _face: &(),
    ) -> Result<(), TowerRefusal<u32, ()>> {
        if !self.refines(coarse, fine) {
            return Err(TowerRefusal::NotARefinement {
                coarse: *coarse,
                fine: *fine,
            });
        }
        Ok(())
    }
}

impl EnumerableTower for UnitTower {
    fn adjacent_preimage(
        &self,
        coarse: &u32,
        fine: &u32,
        _face: &(),
    ) -> Result<Vec<()>, TowerRefusal<u32, ()>> {
        if !self.refines(coarse, fine) {
            return Err(TowerRefusal::NotARefinement {
                coarse: *coarse,
                fine: *fine,
            });
        }
        Ok(vec![()])
    }
}

/// Which component of a composite migration refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompositionStage {
    /// The migration applied first, from the source chart family to the middle one.
    First,
    /// The migration applied second, from the middle chart family to the target one.
    Second,
}

/// Which route around a naturality square is being reported.
///
/// Lean counterpart: the two composites of
/// `Foundation/ContinuingTower.lean::ResidualMigration.square_either_route_reopens`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SquareRoute {
    /// Migrate at the fine chart, then restrict in the target tower.
    MigrateThenRestrict,
    /// Restrict in the source tower, then migrate at the coarse chart.
    RestrictThenMigrate,
}

/// Why a migration refused.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Migration` carries `index_mono` and
/// `naturality` as proof fields, so they cannot fail. Here they are asked, and a failure is one of
/// these variants rather than a panic or a silent repair.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MigrationRefusal<SI, SF, TI, TF> {
    /// The source tower refused.
    Source(TowerRefusal<SI, SF>),
    /// The target tower refused.
    Target(TowerRefusal<TI, TF>),
    /// `Migration.index_mono` failed: the index map did not preserve a refinement.
    IndexNotMonotone {
        /// The coarser target chart.
        coarse: TI,
        /// The finer target chart.
        fine: TI,
        /// Which source chart the coarser one reads.
        coarse_image: SI,
        /// Which source chart the finer one reads.
        fine_image: SI,
    },
    /// `Migration.naturality` failed: restricting after migrating disagreed with migrating after
    /// restricting.
    NaturalityFailed {
        /// The coarser target chart.
        coarse: TI,
        /// The finer target chart.
        fine: TI,
        /// The source face at the finer chart's image on which they disagreed.
        source_face: SF,
        /// What migrating at `fine` and then restricting in the target tower returned.
        via_target_restriction: TF,
        /// What restricting in the source tower and then migrating at `coarse` returned.
        via_source_restriction: TF,
    },
    /// A continuing object carries no witness at the source chart a target chart reads.
    SourceChartMissing {
        /// The target chart that was asked for.
        target_chart: TI,
        /// The source chart it reads, which the object does not carry.
        source_chart: SI,
    },
    /// A target chart is above the migration's own declared aperture.
    ChartAboveDeclaredAperture {
        /// The chart that was asked for.
        target_chart: TI,
        /// The highest chart this migration declares.
        declared_ceiling: TI,
    },
    /// `ResidualMigration.reopen_apply` failed at one chart.
    ReopenFailed {
        /// Where it failed.
        target_chart: TI,
        /// The source face that was not recovered.
        source_face: SF,
        /// What the migration transported.
        migrated: TF,
        /// What reopening actually returned.
        reopened: SF,
    },
    /// One route around a naturality square did not reopen the source face.
    SquareReopenFailed {
        /// The coarser target chart.
        coarse: TI,
        /// The finer target chart.
        fine: TI,
        /// Which route failed.
        route: SquareRoute,
        /// The source face that was not recovered.
        source_face: SF,
        /// What that route actually returned.
        reopened: SF,
    },
    /// A component of a composite migration refused. The component's own refusal is stated in the
    /// **middle** family's index and face types, which this type cannot name, so the stage and the
    /// component's rendered refusal are carried instead. A caller that needs the typed middle
    /// refusal asks that component directly.
    ComponentRefused {
        /// Which component refused.
        stage: CompositionStage,
        /// The component's own refusal, rendered.
        rendered: String,
    },
}

impl<SI: Debug, SF: Debug, TI: Debug, TF: Debug> fmt::Display for MigrationRefusal<SI, SF, TI, TF> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Source(refusal) => write!(formatter, "the source tower refused: {refusal}"),
            Self::Target(refusal) => write!(formatter, "the target tower refused: {refusal}"),
            Self::IndexNotMonotone {
                coarse,
                fine,
                coarse_image,
                fine_image,
            } => write!(
                formatter,
                "the index map is not monotone: {coarse:?} <= {fine:?} but {coarse_image:?} does \
                 not refine to {fine_image:?}"
            ),
            Self::NaturalityFailed {
                coarse,
                fine,
                source_face,
                via_target_restriction,
                via_source_restriction,
            } => write!(
                formatter,
                "naturality failed on {coarse:?} <= {fine:?} for {source_face:?}: migrating then \
                 restricting returned {via_target_restriction:?}, restricting then migrating \
                 returned {via_source_restriction:?}"
            ),
            Self::SourceChartMissing {
                target_chart,
                source_chart,
            } => write!(
                formatter,
                "target chart {target_chart:?} reads source chart {source_chart:?}, which the \
                 continuing object does not carry"
            ),
            Self::ChartAboveDeclaredAperture {
                target_chart,
                declared_ceiling,
            } => write!(
                formatter,
                "target chart {target_chart:?} is above this migration's declared ceiling \
                 {declared_ceiling:?}"
            ),
            Self::ReopenFailed {
                target_chart,
                source_face,
                migrated,
                reopened,
            } => write!(
                formatter,
                "reopening {migrated:?} at chart {target_chart:?} returned {reopened:?}, not the \
                 source face {source_face:?}"
            ),
            Self::SquareReopenFailed {
                coarse,
                fine,
                route,
                source_face,
                reopened,
            } => write!(
                formatter,
                "the {route:?} route around the square {coarse:?} <= {fine:?} returned \
                 {reopened:?}, not the source face {source_face:?}"
            ),
            Self::ComponentRefused { stage, rendered } => {
                write!(formatter, "the {stage:?} component refused: {rendered}")
            }
        }
    }
}

impl<SI: Debug, SF: Debug, TI: Debug, TF: Debug> std::error::Error
    for MigrationRefusal<SI, SF, TI, TF>
{
}

/// The index type of a migration's source tower.
pub type MigrationSourceIndex<M> = <<M as Migration>::Source as Tower>::Index;
/// The face type of a migration's source tower.
pub type MigrationSourceFace<M> = <<M as Migration>::Source as Tower>::Face;
/// The index type of a migration's target tower.
pub type MigrationTargetIndex<M> = <<M as Migration>::Target as Tower>::Index;
/// The face type of a migration's target tower.
pub type MigrationTargetFace<M> = <<M as Migration>::Target as Tower>::Face;

/// A migration's own typed refusal, in its own four index and face types.
pub type MigrationRefusalOf<M> = MigrationRefusal<
    MigrationSourceIndex<M>,
    MigrationSourceFace<M>,
    MigrationTargetIndex<M>,
    MigrationTargetFace<M>,
>;

/// A migration return `V`, or that migration's own typed [`MigrationRefusal`].
pub type MigrationOutcome<M, V> = Result<V, MigrationRefusalOf<M>>;

/// Exactly which naturality squares were checked, and over how many faces.
///
/// Lean counterpart: the `naturality` field of
/// `Foundation/ContinuingTower.lean::Migration`, which Lean carries as a proof for every refinement
/// pair. Here it is asked over a declared finite aperture and this receipt names exactly what was
/// checked. The receipt is the scope of the claim; it is not a proof of the law.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct NaturalityReceipt<TI> {
    /// The `(coarse, fine)` target-chart pairs whose square commuted on at least one supplied face.
    pub checked_squares: Vec<(TI, TI)>,
    /// How many `(chart, source face)` pairs were presented.
    pub faces_checked: usize,
}

/// A checked instance of `ResidualMigration.square_either_route_reopens`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct SquareReopenReceipt {
    /// How many of the two routes around the square reopened the source face exactly. A complete
    /// receipt is `2`.
    pub routes_reopened: usize,
    /// Whether the two routes were also confirmed to transport the same face.
    pub naturality_checked: bool,
}

/// A change of the whole chart family: a functor of index categories together with a natural
/// transformation on faces.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Migration`. [`Transition`] is the
/// non-invertible chart map at **one** chart; a `Migration` is the structure one level up.
/// [`Self::index`] is Lean's `index` — for each chart of the *new* family, which chart of the *old*
/// family it reads — and [`Self::face`] is the natural transformation's component there. The
/// monotonicity of `index` and the naturality square are Lean's `index_mono` and `naturality`
/// fields; here they are checked by [`check_migration_naturality`] and returned as a
/// [`NaturalityReceipt`] or refused as a [`MigrationRefusal`], never assumed and never repaired.
///
/// The consuming motivation is schema history and lossy codecs: an object saved under one chart
/// family and read under another. [`carry_section`] is that operation, and it is Lean's
/// `Migration.carrySection`.
pub trait Migration {
    /// The chart family the object was saved under.
    type Source: Tower;
    /// The chart family it is read under.
    type Target: Tower;

    /// The source tower.
    fn source_tower(&self) -> &Self::Source;

    /// The target tower.
    fn target_tower(&self) -> &Self::Target;

    /// Which chart of the source family a target chart reads.
    ///
    /// Lean counterpart: `Migration.index`.
    fn index(&self, target_chart: &MigrationTargetIndex<Self>) -> MigrationSourceIndex<Self>
    where
        Self: Sized;

    /// The component of the natural transformation at one target chart.
    ///
    /// Lean counterpart: `Migration.face`.
    fn face(
        &self,
        target_chart: &MigrationTargetIndex<Self>,
        source_face: &MigrationSourceFace<Self>,
    ) -> MigrationOutcome<Self, MigrationTargetFace<Self>>
    where
        Self: Sized;
}

/// Check `index_mono` and `naturality` over a declared aperture of target charts and faces.
///
/// Lean counterpart: the `index_mono` and `naturality` fields of
/// `Foundation/ContinuingTower.lean::Migration`. `faces` supplies `(fine target chart, source face
/// at that chart's image)` pairs; every refining target pair `(coarse, fine)` whose fine member
/// carries a supplied face is checked, and the square that commuted is recorded.
pub fn check_migration_naturality<M: Migration>(
    migration: &M,
    target_charts: &[MigrationTargetIndex<M>],
    faces: &[(MigrationTargetIndex<M>, MigrationSourceFace<M>)],
) -> MigrationOutcome<M, NaturalityReceipt<MigrationTargetIndex<M>>> {
    let source = migration.source_tower();
    let target = migration.target_tower();
    let mut receipt = NaturalityReceipt {
        checked_squares: Vec::new(),
        faces_checked: faces.len(),
    };

    for coarse in target_charts {
        for fine in target_charts {
            if !target.refines(coarse, fine) {
                continue;
            }
            let coarse_image = migration.index(coarse);
            let fine_image = migration.index(fine);
            if !source.refines(&coarse_image, &fine_image) {
                return Err(MigrationRefusal::IndexNotMonotone {
                    coarse: coarse.clone(),
                    fine: fine.clone(),
                    coarse_image,
                    fine_image,
                });
            }
            let mut checked_here = false;
            for (chart, source_face) in faces {
                if chart != fine {
                    continue;
                }
                let migrated = migration.face(fine, source_face)?;
                let via_target_restriction = target
                    .restrict(coarse, fine, &migrated)
                    .map_err(MigrationRefusal::Target)?;
                let restricted = source
                    .restrict(&coarse_image, &fine_image, source_face)
                    .map_err(MigrationRefusal::Source)?;
                let via_source_restriction = migration.face(coarse, &restricted)?;
                if via_target_restriction != via_source_restriction {
                    return Err(MigrationRefusal::NaturalityFailed {
                        coarse: coarse.clone(),
                        fine: fine.clone(),
                        source_face: source_face.clone(),
                        via_target_restriction,
                        via_source_restriction,
                    });
                }
                checked_here = true;
            }
            if checked_here {
                receipt.checked_squares.push((coarse.clone(), fine.clone()));
            }
        }
    }

    Ok(receipt)
}

/// Read a continuing object saved under one chart family under another one.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Migration.carrySection`, whose compatibility
/// proof is naturality followed by the source object's own compatibility. Here the carried family
/// is rebuilt and re-checked with [`CompatibleSection::check`], so the result carries a
/// [`CompatibilityReceipt`] rather than an assumed invariant.
///
/// This is the schema-history operation: `section` was saved under the source family, and what
/// comes back is again **one** continuing object over `target_charts`, not a family of unrelated
/// faces.
pub fn carry_section<M: Migration>(
    migration: &M,
    section: &CompatibleSection<MigrationSourceIndex<M>, MigrationSourceFace<M>>,
    target_charts: &[MigrationTargetIndex<M>],
) -> MigrationOutcome<M, CompatibleSection<MigrationTargetIndex<M>, MigrationTargetFace<M>>> {
    let mut witnesses = BTreeMap::new();
    for chart in target_charts {
        let source_chart = migration.index(chart);
        let Some(source_face) = section.witness(&source_chart) else {
            return Err(MigrationRefusal::SourceChartMissing {
                target_chart: chart.clone(),
                source_chart,
            });
        };
        witnesses.insert(chart.clone(), migration.face(chart, source_face)?);
    }
    CompatibleSection::check(migration.target_tower(), witnesses).map_err(MigrationRefusal::Target)
}

/// A migration that carries, at each target chart, the part of the source face its component does
/// not transport.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::ResidualMigration`. The residual is
/// *supplied*, exactly as in [`TowerRestrictTransition`]: naturality says what a migration
/// preserves, never what it drops. Lean proves the two presentations are the same data —
/// `ResidualMigration.transition` and `ResidualMigration.ofTransitionFamily` are mutually inverse
/// by `rfl` — so this trait is precisely an index functor together with a family of [`Transition`]s
/// whose transported maps satisfy naturality.
pub trait ResidualMigration: Migration {
    /// What the component at one target chart does not transport.
    ///
    /// Lean counterpart: `ResidualMigration.Residual`.
    type Residual: Clone + Eq + Debug;

    /// What the component at one target chart drops, retained.
    ///
    /// Lean counterpart: `ResidualMigration.residual`.
    fn residual(
        &self,
        target_chart: &MigrationTargetIndex<Self>,
        source_face: &MigrationSourceFace<Self>,
    ) -> MigrationOutcome<Self, Self::Residual>
    where
        Self: Sized;

    /// Reconstruct the source face from the migrated face and the retained residual.
    ///
    /// Lean counterpart: `ResidualMigration.reopen`.
    fn reopen(
        &self,
        target_chart: &MigrationTargetIndex<Self>,
        target_face: &MigrationTargetFace<Self>,
        residual: &Self::Residual,
    ) -> MigrationOutcome<Self, MigrationSourceFace<Self>>
    where
        Self: Sized;

    /// Check `reopen(face(j, x), residual(j, x)) = x` at one target chart.
    ///
    /// Lean counterpart: `ResidualMigration.reopen_apply`, which is a field and cannot fail; here
    /// it is asked and a failure is [`MigrationRefusal::ReopenFailed`].
    fn check_reopen(
        &self,
        target_chart: &MigrationTargetIndex<Self>,
        source_face: &MigrationSourceFace<Self>,
    ) -> MigrationOutcome<Self, ReopenReceipt>
    where
        Self: Sized,
    {
        let migrated = self.face(target_chart, source_face)?;
        let residual = self.residual(target_chart, source_face)?;
        let reopened = self.reopen(target_chart, &migrated, &residual)?;
        if &reopened == source_face {
            Ok(ReopenReceipt {
                sources_reopened: 1,
            })
        } else {
            Err(MigrationRefusal::ReopenFailed {
                target_chart: target_chart.clone(),
                source_face: source_face.clone(),
                migrated,
                reopened,
            })
        }
    }
}

/// Check that **either** retained residual pair around one naturality square reopens the source
/// face exactly.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::ResidualMigration.square_either_route_reopens`
/// together with `square_routes_agree`. This is the schema-history and lossy-codec statement in
/// full: an object saved under the source family at chart `index(fine)`, read under the target
/// family at the coarser chart `coarse`, presents **one** transported face; the two routes around
/// the square retain *different* residual pairs, and each of them reconstructs the original source
/// face with no remainder. A reader that kept either pair has lost nothing.
///
/// The two tower restrictions supply their own residuals through [`TowerRestrictTransition`], which
/// is why both towers carry that bound.
pub fn check_migration_square_reopen<M>(
    migration: &M,
    coarse: &MigrationTargetIndex<M>,
    fine: &MigrationTargetIndex<M>,
    source_face: &MigrationSourceFace<M>,
) -> MigrationOutcome<M, SquareReopenReceipt>
where
    M: ResidualMigration,
    M::Source: TowerRestrictTransition,
    M::Target: TowerRestrictTransition,
{
    let source = migration.source_tower();
    let target = migration.target_tower();
    let coarse_image = migration.index(coarse);
    let fine_image = migration.index(fine);
    if !source.refines(&coarse_image, &fine_image) {
        return Err(MigrationRefusal::IndexNotMonotone {
            coarse: coarse.clone(),
            fine: fine.clone(),
            coarse_image,
            fine_image,
        });
    }

    // The one transported face both routes arrive at.
    let migrated_fine = migration.face(fine, source_face)?;
    let transported = target
        .restrict(coarse, fine, &migrated_fine)
        .map_err(MigrationRefusal::Target)?;

    // Route one: migrate at `fine`, then restrict in the target tower.
    let target_residual = target
        .restriction_residual(coarse, fine, &migrated_fine)
        .map_err(MigrationRefusal::Target)?;
    let migration_residual_fine = migration.residual(fine, source_face)?;
    let reopened_migrated = target
        .restriction_reopen(coarse, fine, &transported, &target_residual)
        .map_err(MigrationRefusal::Target)?;
    let route_one = migration.reopen(fine, &reopened_migrated, &migration_residual_fine)?;
    if &route_one != source_face {
        return Err(MigrationRefusal::SquareReopenFailed {
            coarse: coarse.clone(),
            fine: fine.clone(),
            route: SquareRoute::MigrateThenRestrict,
            source_face: source_face.clone(),
            reopened: route_one,
        });
    }

    // Route two: restrict in the source tower, then migrate at `coarse`.
    let restricted_source = source
        .restrict(&coarse_image, &fine_image, source_face)
        .map_err(MigrationRefusal::Source)?;
    let migrated_coarse = migration.face(coarse, &restricted_source)?;
    if migrated_coarse != transported {
        return Err(MigrationRefusal::NaturalityFailed {
            coarse: coarse.clone(),
            fine: fine.clone(),
            source_face: source_face.clone(),
            via_target_restriction: transported,
            via_source_restriction: migrated_coarse,
        });
    }
    let migration_residual_coarse = migration.residual(coarse, &restricted_source)?;
    let source_residual = source
        .restriction_residual(&coarse_image, &fine_image, source_face)
        .map_err(MigrationRefusal::Source)?;
    let reopened_restricted =
        migration.reopen(coarse, &transported, &migration_residual_coarse)?;
    let route_two = source
        .restriction_reopen(
            &coarse_image,
            &fine_image,
            &reopened_restricted,
            &source_residual,
        )
        .map_err(MigrationRefusal::Source)?;
    if &route_two != source_face {
        return Err(MigrationRefusal::SquareReopenFailed {
            coarse: coarse.clone(),
            fine: fine.clone(),
            route: SquareRoute::RestrictThenMigrate,
            source_face: source_face.clone(),
            reopened: route_two,
        });
    }

    Ok(SquareReopenReceipt {
        routes_reopened: 2,
        naturality_checked: true,
    })
}

/// The identity migration of one tower: read every chart where it was written, change nothing.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Migration.identity`, and — because its face
/// components are equivalences — the zero-residual arm that `rebaseMigration_residual_subsingleton`
/// establishes for `Holon.Rebase`. [`NoResidual`] has one value, so "this migration drops nothing"
/// is a fact about the type rather than a runtime check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IdentityMigration<T> {
    tower: T,
}

impl<T> IdentityMigration<T> {
    /// The identity migration of a tower.
    pub fn new(tower: T) -> Self {
        Self { tower }
    }

    /// The tower it migrates.
    pub fn tower(&self) -> &T {
        &self.tower
    }
}

impl<T: Tower> Migration for IdentityMigration<T> {
    type Source = T;
    type Target = T;

    fn source_tower(&self) -> &T {
        &self.tower
    }

    fn target_tower(&self) -> &T {
        &self.tower
    }

    fn index(&self, target_chart: &T::Index) -> T::Index {
        target_chart.clone()
    }

    fn face(
        &self,
        _target_chart: &T::Index,
        source_face: &T::Face,
    ) -> MigrationOutcome<Self, T::Face> {
        Ok(source_face.clone())
    }
}

impl<T: Tower> ResidualMigration for IdentityMigration<T> {
    type Residual = NoResidual;

    fn residual(
        &self,
        _target_chart: &T::Index,
        _source_face: &T::Face,
    ) -> MigrationOutcome<Self, NoResidual> {
        Ok(NoResidual)
    }

    fn reopen(
        &self,
        _target_chart: &T::Index,
        target_face: &T::Face,
        _residual: &NoResidual,
    ) -> MigrationOutcome<Self, T::Face> {
        Ok(target_face.clone())
    }
}

/// Composition of migrations: `second` after `first`.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Migration.comp`, with `comp_assoc`,
/// `comp_identity` and `identity_comp` holding by `rfl` there. Index maps compose in the opposite
/// order, as they must for a contravariant index, and `carrySection_comp` is the statement this
/// type exists for: a schema **history** may be replayed step by step or composed first, with the
/// same result.
///
/// Its residual is the pair, exactly as [`ComposedTransition`]'s is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ComposedMigration<Second, First> {
    /// The migration applied second.
    pub second: Second,
    /// The migration applied first.
    pub first: First,
}

impl<Second, First> ComposedMigration<Second, First> {
    /// Compose, second after first.
    pub fn new(second: Second, first: First) -> Self {
        Self { second, first }
    }
}

impl<Second, First> Migration for ComposedMigration<Second, First>
where
    First: Migration,
    Second: Migration<Source = First::Target>,
    MigrationSourceIndex<Second>: Debug,
    MigrationSourceFace<Second>: Debug,
{
    type Source = First::Source;
    type Target = Second::Target;

    fn source_tower(&self) -> &Self::Source {
        self.first.source_tower()
    }

    fn target_tower(&self) -> &Self::Target {
        self.second.target_tower()
    }

    fn index(&self, target_chart: &MigrationTargetIndex<Second>) -> MigrationSourceIndex<First> {
        self.first.index(&self.second.index(target_chart))
    }

    fn face(
        &self,
        target_chart: &MigrationTargetIndex<Second>,
        source_face: &MigrationSourceFace<First>,
    ) -> MigrationOutcome<Self, MigrationTargetFace<Second>> {
        let middle_chart = self.second.index(target_chart);
        let middle_face = self.first.face(&middle_chart, source_face).map_err(|refusal| {
            MigrationRefusal::ComponentRefused {
                stage: CompositionStage::First,
                rendered: refusal.to_string(),
            }
        })?;
        self.second
            .face(target_chart, &middle_face)
            .map_err(|refusal| MigrationRefusal::ComponentRefused {
                stage: CompositionStage::Second,
                rendered: refusal.to_string(),
            })
    }
}

impl<Second, First> ResidualMigration for ComposedMigration<Second, First>
where
    First: ResidualMigration,
    Second: ResidualMigration<Source = First::Target>,
    MigrationSourceIndex<Second>: Debug,
    MigrationSourceFace<Second>: Debug,
{
    type Residual = (Second::Residual, First::Residual);

    fn residual(
        &self,
        target_chart: &MigrationTargetIndex<Second>,
        source_face: &MigrationSourceFace<First>,
    ) -> MigrationOutcome<Self, Self::Residual> {
        let middle_chart = self.second.index(target_chart);
        let middle_face = self.first.face(&middle_chart, source_face).map_err(|refusal| {
            MigrationRefusal::ComponentRefused {
                stage: CompositionStage::First,
                rendered: refusal.to_string(),
            }
        })?;
        let second_residual =
            self.second
                .residual(target_chart, &middle_face)
                .map_err(|refusal| MigrationRefusal::ComponentRefused {
                    stage: CompositionStage::Second,
                    rendered: refusal.to_string(),
                })?;
        let first_residual = self
            .first
            .residual(&middle_chart, source_face)
            .map_err(|refusal| MigrationRefusal::ComponentRefused {
                stage: CompositionStage::First,
                rendered: refusal.to_string(),
            })?;
        Ok((second_residual, first_residual))
    }

    fn reopen(
        &self,
        target_chart: &MigrationTargetIndex<Second>,
        target_face: &MigrationTargetFace<Second>,
        residual: &Self::Residual,
    ) -> MigrationOutcome<Self, MigrationSourceFace<First>> {
        let middle_chart = self.second.index(target_chart);
        let middle_face = self
            .second
            .reopen(target_chart, target_face, &residual.0)
            .map_err(|refusal| MigrationRefusal::ComponentRefused {
                stage: CompositionStage::Second,
                rendered: refusal.to_string(),
            })?;
        self.first
            .reopen(&middle_chart, &middle_face, &residual.1)
            .map_err(|refusal| MigrationRefusal::ComponentRefused {
                stage: CompositionStage::First,
                rendered: refusal.to_string(),
            })
    }
}

/// A genuinely lossy schema migration on the residue tower: the new chart family reads level `j` of
/// the old family at level `2 * j` and keeps only the low half.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::padicHalfMigration`, whose naturality is
/// `Tower.restrict_trans`, whose residual at chart `j` is C2's `padicDigitGap p j j`, and whose
/// `padicHalfMigration_carrySection` proves that the `p`-adic integer saved under the old family is
/// read back as *the same* `p`-adic integer under the new one although every face map drops
/// `p ^ j` cosets. The object is the carrier; the faces are not.
///
/// The declared ceiling is not decoration: `2 * j` must not overflow the chart index, and the
/// carrier at level `2 * j` is `base ^ (2 * j)`. A chart above the ceiling is
/// [`MigrationRefusal::ChartAboveDeclaredAperture`], never a panic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HalvingMigration {
    tower: ResidueTower,
    ceiling: u32,
}

impl HalvingMigration {
    /// Build the migration over a declared ceiling on the target chart index. A ceiling above
    /// `u32::MAX / 2` is refused, because the source chart it would read does not exist.
    pub fn new(tower: ResidueTower, ceiling: u32) -> Option<Self> {
        if ceiling > u32::MAX / 2 {
            None
        } else {
            Some(Self { tower, ceiling })
        }
    }

    /// The highest target chart this migration declares.
    pub fn ceiling(&self) -> u32 {
        self.ceiling
    }

    fn checked_image(&self, target_chart: u32) -> MigrationOutcome<Self, u32> {
        if target_chart > self.ceiling {
            Err(MigrationRefusal::ChartAboveDeclaredAperture {
                target_chart,
                declared_ceiling: self.ceiling,
            })
        } else {
            Ok(target_chart * 2)
        }
    }
}

impl Migration for HalvingMigration {
    type Source = ResidueTower;
    type Target = ResidueTower;

    fn source_tower(&self) -> &ResidueTower {
        &self.tower
    }

    fn target_tower(&self) -> &ResidueTower {
        &self.tower
    }

    fn index(&self, target_chart: &u32) -> u32 {
        target_chart.saturating_mul(2)
    }

    fn face(&self, target_chart: &u32, source_face: &BigUint) -> MigrationOutcome<Self, BigUint> {
        let image = self.checked_image(*target_chart)?;
        self.tower
            .restrict(target_chart, &image, source_face)
            .map_err(MigrationRefusal::Source)
    }
}

impl ResidualMigration for HalvingMigration {
    /// The exact digit block the migration drops: one of the `base ^ j` cosets of the splitting.
    ///
    /// Lean counterpart: `padicHalfMigration`'s `Residual j := ZMod (p ^ j)`, which
    /// `padicHalfMigration_transition` identifies with C2's `padicRestrictTransition p j j` by
    /// `rfl`.
    type Residual = BigUint;

    fn residual(&self, target_chart: &u32, source_face: &BigUint) -> MigrationOutcome<Self, BigUint> {
        let image = self.checked_image(*target_chart)?;
        self.tower
            .restriction_residual(target_chart, &image, source_face)
            .map_err(MigrationRefusal::Source)
    }

    fn reopen(
        &self,
        target_chart: &u32,
        target_face: &BigUint,
        residual: &BigUint,
    ) -> MigrationOutcome<Self, BigUint> {
        let image = self.checked_image(*target_chart)?;
        self.tower
            .restriction_reopen(target_chart, &image, target_face, residual)
            .map_err(MigrationRefusal::Source)
    }
}

/// How a migration's index map relates the chart it reads to the chart it writes, at one chart.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Migration.StaysAtItsChart`,
/// `Migration.FollowsRefinement` and `Migration.ConnectsIncomparableCharts`. A tower's own passage
/// is typed `i ≤ j → Face j → Face i`, so it exists only along refinement; between incomparable
/// charts it does not exist, and a common refinement does not supply one either, because a span is
/// not a map.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChartRoute {
    /// The migration reads exactly the chart it writes.
    SameChart,
    /// The chart it reads refines the chart it writes: the tower's own restriction already offers a
    /// passage of that shape.
    FollowsRefinement,
    /// The chart it writes refines the chart it reads: the passage runs against the tower's order,
    /// which no restriction does.
    AgainstRefinement,
    /// The two charts are incomparable: neither tower relates them at all. This is the
    /// non-factoring condition, and it is decided by the index map alone.
    Incomparable,
}

/// Which route each declared chart takes.
///
/// Lean counterpart: the three predicates named on [`ChartRoute`], asked over a declared finite
/// chart aperture. The receipt is the scope of the claim; it is not a proof of the predicate.
/// [implemented-exact] The fields are private and there is no `Default`: a receipt is the record
/// of a check that ran, so the only way to obtain one is [`check_index_routes`]. Forging one — an
/// empty route list reads as "follows refinement everywhere" — is a compile error outside this
/// module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IndexRouteReceipt<TI> {
    routes: Vec<(TI, ChartRoute)>,
    orders_agreed: bool,
}

impl<TI> IndexRouteReceipt<TI> {
    /// The route taken at each declared chart.
    pub fn routes(&self) -> &[(TI, ChartRoute)] {
        &self.routes
    }

    /// Whether the source and target towers agreed on the refinement order over the declared
    /// charts. Lean shares one `Preorder Index` between the two towers by construction; here two
    /// towers may present different orders, and this records that they did not.
    pub fn orders_agreed(&self) -> bool {
        self.orders_agreed
    }

    /// Whether every declared chart reads a chart that refines it.
    ///
    /// Lean counterpart: `Migration.FollowsRefinement`.
    pub fn follows_refinement_everywhere(&self) -> bool {
        self.routes
            .iter()
            .all(|(_, route)| matches!(route, ChartRoute::SameChart | ChartRoute::FollowsRefinement))
    }

    /// Whether every declared chart reads exactly itself.
    ///
    /// Lean counterpart: `Migration.StaysAtItsChart`.
    pub fn stays_at_its_chart_everywhere(&self) -> bool {
        self.routes
            .iter()
            .all(|(_, route)| matches!(route, ChartRoute::SameChart))
    }

    /// Whether some declared chart is incomparable with the chart it reads.
    ///
    /// Lean counterpart: `Migration.ConnectsIncomparableCharts`.
    pub fn connects_incomparable_charts(&self) -> bool {
        self.routes
            .iter()
            .any(|(_, route)| matches!(route, ChartRoute::Incomparable))
    }

    /// The declared charts that are incomparable with the charts they read.
    pub fn incomparable_charts(&self) -> Vec<&TI> {
        self.routes
            .iter()
            .filter(|(_, route)| matches!(route, ChartRoute::Incomparable))
            .map(|(chart, _)| chart)
            .collect()
    }
}

/// Classify a migration's index route at each declared chart.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Migration.StaysAtItsChart`,
/// `Migration.FollowsRefinement` and `Migration.ConnectsIncomparableCharts`, which are decided by
/// the index map alone and say nothing about the face maps. Both towers must be indexed by the same
/// type, as they are in Lean, and the refinement order is read off the target tower; whether the
/// source tower agreed is recorded in the receipt.
pub fn check_index_routes<M>(
    migration: &M,
    target_charts: &[MigrationTargetIndex<M>],
) -> IndexRouteReceipt<MigrationTargetIndex<M>>
where
    M: Migration,
    M::Source: Tower<Index = MigrationTargetIndex<M>>,
{
    let source = migration.source_tower();
    let target = migration.target_tower();
    let mut orders_agreed = true;
    let mut routes = Vec::with_capacity(target_charts.len());

    for left in target_charts {
        for right in target_charts {
            if source.refines(left, right) != target.refines(left, right) {
                orders_agreed = false;
            }
        }
    }

    for chart in target_charts {
        let image = migration.index(chart);
        let route = if &image == chart {
            ChartRoute::SameChart
        } else if target.refines(chart, &image) {
            ChartRoute::FollowsRefinement
        } else if target.refines(&image, chart) {
            ChartRoute::AgainstRefinement
        } else {
            ChartRoute::Incomparable
        };
        routes.push((chart.clone(), route));
    }

    IndexRouteReceipt {
        routes,
        orders_agreed,
    }
}

/// Which declared charts a migration's component really is the tower's own restriction at.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Migration.FactorsThroughRefinement`, whose
/// two fields are exactly `refines` (recorded here as membership in
/// [`Self::restriction_charts`] rather than [`Self::no_route_charts`]) and `isRestriction`.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct FactorisationReceipt<TI> {
    /// Charts whose component was the tower's own restriction on every supplied face.
    pub restriction_charts: Vec<TI>,
    /// Charts whose component differed from the tower's restriction on some supplied face.
    pub non_restriction_charts: Vec<TI>,
    /// Charts with no restriction route at all: the chart read does not refine the chart written,
    /// so the tower supplies nothing to compare against. A chart here is why the migration cannot
    /// factor through refinement.
    pub no_route_charts: Vec<TI>,
    /// How many `(chart, source face)` pairs were presented.
    pub faces_checked: usize,
}

impl<TI> FactorisationReceipt<TI> {
    /// Whether every declared chart factored through the tower's own restriction.
    ///
    /// Lean counterpart: `Migration.FactorsThroughRefinement` holding, over this aperture.
    pub fn factors_through_refinement(&self) -> bool {
        self.non_restriction_charts.is_empty() && self.no_route_charts.is_empty()
    }
}

/// Check whether a migration of one tower is that tower's own restriction family.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Migration.FactorsThroughRefinement` and
/// `Migration.not_factorsThroughRefinement_of_connectsIncomparableCharts`. A chart whose read chart
/// does not refine the chart written lands in [`FactorisationReceipt::no_route_charts`]: there is no
/// refinement route there, so the migration supplies passage the tower does not have.
pub fn check_factors_through_restriction<M>(
    migration: &M,
    target_charts: &[MigrationTargetIndex<M>],
    faces: &[(MigrationTargetIndex<M>, MigrationSourceFace<M>)],
) -> MigrationOutcome<M, FactorisationReceipt<MigrationTargetIndex<M>>>
where
    M: Migration,
    M::Source: Tower<Index = MigrationTargetIndex<M>, Face = MigrationTargetFace<M>>,
{
    let target = migration.target_tower();
    let mut receipt = FactorisationReceipt {
        restriction_charts: Vec::new(),
        non_restriction_charts: Vec::new(),
        no_route_charts: Vec::new(),
        faces_checked: faces.len(),
    };

    for chart in target_charts {
        let image = migration.index(chart);
        if !target.refines(chart, &image) {
            receipt.no_route_charts.push(chart.clone());
            continue;
        }
        let mut agreed = true;
        for (supplied_chart, source_face) in faces {
            if supplied_chart != chart {
                continue;
            }
            let migrated = migration.face(chart, source_face)?;
            let restricted = target
                .restrict(chart, &image, source_face)
                .map_err(MigrationRefusal::Target)?;
            if migrated != restricted {
                agreed = false;
                break;
            }
        }
        if agreed {
            receipt.restriction_charts.push(chart.clone());
        } else {
            receipt.non_restriction_charts.push(chart.clone());
        }
    }

    Ok(receipt)
}

/// Whether the passage at one chart is two-way from the migrated face **alone**, over a declared
/// population of source faces.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Migration.ReversePassage`, together with
/// `Migration.injective_of_reversePassage` and `Migration.not_reversePassage_of_not_injective`: a
/// reverse passage from the face alone exists exactly when the component is injective.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReversePassageReceipt<SF> {
    /// No two supplied source faces were merged, so over this population the component is injective
    /// and a reverse passage from the migrated face alone exists.
    FromTheFaceAlone {
        /// How many source faces were presented.
        faces_checked: usize,
    },
    /// Two source faces were merged. There is no reverse passage from the migrated face alone: the
    /// passage is one-way unless the residual is retained.
    OnlyWithTheResidual {
        /// One of the merged source faces.
        merged_left: SF,
        /// The other.
        merged_right: SF,
    },
}

/// Decide, over a declared population of source faces, whether the passage at one chart is two-way
/// from the migrated face alone.
///
/// Lean counterpart: `Migration.ReversePassage` and the two theorems that bracket it. Lean
/// quantifies over the whole face type; this asks a declared finite population and the receipt is
/// the scope of the claim.
pub fn check_reverse_passage<M: Migration>(
    migration: &M,
    target_chart: &MigrationTargetIndex<M>,
    source_faces: &[MigrationSourceFace<M>],
) -> MigrationOutcome<M, ReversePassageReceipt<MigrationSourceFace<M>>> {
    let mut migrated = Vec::with_capacity(source_faces.len());
    for source_face in source_faces {
        migrated.push(migration.face(target_chart, source_face)?);
    }
    for (left, left_face) in migrated.iter().enumerate() {
        for (right, right_face) in migrated.iter().enumerate().skip(left + 1) {
            if left_face == right_face && source_faces[left] != source_faces[right] {
                return Ok(ReversePassageReceipt::OnlyWithTheResidual {
                    merged_left: source_faces[left].clone(),
                    merged_right: source_faces[right].clone(),
                });
            }
        }
    }
    Ok(ReversePassageReceipt::FromTheFaceAlone {
        faces_checked: source_faces.len(),
    })
}

/// Two charts with no refinement between them, and therefore no common refinement at all.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::TwoCharts` with its discrete `Preorder`, and
/// `twoCharts_no_common_refinement`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum TwoCharts {
    /// One chart.
    Left,
    /// The other.
    Right,
}

/// One face type at both charts of that discrete index; the only admitted restriction is the
/// identity at each chart.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::twoChartTower`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct TwoChartTower;

impl TwoChartTower {
    /// Whether any chart refines both of the two: nothing does, which is
    /// `twoCharts_no_common_refinement`.
    pub fn has_common_refinement(&self) -> bool {
        [TwoCharts::Left, TwoCharts::Right]
            .iter()
            .any(|k| self.refines(&TwoCharts::Left, k) && self.refines(&TwoCharts::Right, k))
    }
}

impl Tower for TwoChartTower {
    type Index = TwoCharts;
    type Face = BigUint;

    fn refines(&self, coarse: &TwoCharts, fine: &TwoCharts) -> bool {
        coarse == fine
    }

    fn carries(&self, _chart: &TwoCharts, _face: &BigUint) -> bool {
        true
    }

    fn restrict(
        &self,
        coarse: &TwoCharts,
        fine: &TwoCharts,
        face: &BigUint,
    ) -> Result<BigUint, TowerRefusal<TwoCharts, BigUint>> {
        if coarse != fine {
            return Err(TowerRefusal::NotARefinement {
                coarse: *coarse,
                fine: *fine,
            });
        }
        Ok(face.clone())
    }
}

/// The migration that reads the *other* chart at every chart of [`TwoChartTower`].
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::swapMigration`, with
/// `swapMigration_connectsIncomparableCharts` and `swapMigration_not_factorsThroughRefinement`. It
/// is a lawful migration — its index map is monotone vacuously and all its naturality squares are
/// reflexive — and it supplies passage between two charts the tower relates in no way at all. It is
/// the witness that the non-factoring condition is **not vacuous**.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct SwapMigration {
    tower: TwoChartTower,
}

impl SwapMigration {
    /// The swap migration of the two-chart tower.
    pub fn new() -> Self {
        Self {
            tower: TwoChartTower,
        }
    }
}

impl Migration for SwapMigration {
    type Source = TwoChartTower;
    type Target = TwoChartTower;

    fn source_tower(&self) -> &TwoChartTower {
        &self.tower
    }

    fn target_tower(&self) -> &TwoChartTower {
        &self.tower
    }

    fn index(&self, target_chart: &TwoCharts) -> TwoCharts {
        match target_chart {
            TwoCharts::Left => TwoCharts::Right,
            TwoCharts::Right => TwoCharts::Left,
        }
    }

    fn face(
        &self,
        _target_chart: &TwoCharts,
        source_face: &BigUint,
    ) -> MigrationOutcome<Self, BigUint> {
        Ok(source_face.clone())
    }
}

impl ResidualMigration for SwapMigration {
    type Residual = NoResidual;

    fn residual(
        &self,
        _target_chart: &TwoCharts,
        _source_face: &BigUint,
    ) -> MigrationOutcome<Self, NoResidual> {
        Ok(NoResidual)
    }

    fn reopen(
        &self,
        _target_chart: &TwoCharts,
        target_face: &BigUint,
        _residual: &NoResidual,
    ) -> MigrationOutcome<Self, BigUint> {
        Ok(target_face.clone())
    }
}

#[cfg(test)]
mod tests;
