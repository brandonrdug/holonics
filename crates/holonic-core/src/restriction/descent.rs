//! **Descent: whether a fine object passes through a restriction, or the typed defect it leaves.**
//!
//! [definition] A restriction `π` ([`Transition`], `Foundation/ContinuingTower.lean::Transition`)
//! transports [`Transition::apply`] and retains [`Transition::residual`], and the residual is
//! exactly the dropped part (`Foundation/ContinuingTower.lean::Transition.reopen_apply`). Two
//! things can be asked to *descend* through it, and each returns one [`Descent`]:
//!
//! ```text
//! square    a fine motion A_f and a coarse motion A_c:   π A_f x = A_c π x        (the scale square)
//! factor    a reading ρ on the fine side:                π x = π y  ⇒  ρ x = ρ y  (ρ = ρ̄ ∘ π)
//! ```
//!
//! [definition] **Witness** — the object descends and the witness carries its coarse form: the
//! common coarse image of each declared source for a square, the induced coarse reading `ρ̄` on
//! the image for a factoring. **Defect** — it does not, and the defect retains the fibre: a square
//! break keeps both routes and the residual `π.residual(A_f x)` that, with `π A_f x`, reopens the
//! fine motion exactly (a failed square is holonomy, not loss:
//! `Transport/ContinuingTube.lean::grainSquare_defect_is_not_a_loss`); a factor break keeps the
//! two sources `π` merges, the residuals that still separate them
//! (`Foundation/ContinuingTower.lean::Transition.residual_separates`) and the two readings. The
//! matrix defect `π A_fine − A_coarse π` of [`crate::restriction::SquareDefect`]
//! (`Holon/Restriction.lean::squareDefect`) is the operator of which every square break is one
//! column reading; the equality is tested on [`crate::restriction::LinearRestriction`].
//!
//! [proved-derived; formal-checked] The Lean owner is `Holon/Restriction.lean::Descent`, total by
//! `Holon/Restriction.lean::descent_total` (every reading factors through a restriction or
//! exhibits a merged pair it separates); the pointwise square is the operator defect read at a
//! state (`Holon/Restriction.lean::squareDefect_mulVec_eq_zero_iff`), propagating to every horizon
//! by `Holon/Restriction.lean::scale_square_pow`. The factoring at a standing is
//! `Foundation/Standing.lean::standingLaw_exists_iff_future_factors` (a quotient is a lawful
//! standing exactly when the future factors through it). A square break's retained residual
//! reopening the fine motion is `Transition.reopen_apply` at `A_f x`, not a new law. The engine instances
//! read through this owner: `continuing_tube::SquareVerdict::descent` (the tube square, including
//! the grain tube), `receiver_release::CoarseningTower::descent`, `standing::sufficiency_descent`
//! and `receiver_exact_compression::one_shot_descent`.
//!
//! Every declared population is bounded ([`DESCENT_SOURCE_CEILING`]) before any transition runs;
//! a factoring is quadratic in it.

use std::fmt::Debug;

use super::tower::{
    TowerFaceOutcome, TowerOutcome, TowerRefusal, TowerRestrictTransition, Transition,
};

/// The largest source population one descent may be asked over.
pub const DESCENT_SOURCE_CEILING: usize = 4096;

/// Why a descent was not taken.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum DescentRefusal {
    /// The declared source population exceeds [`DESCENT_SOURCE_CEILING`]. Nothing ran.
    #[error("declared {declared} sources, above the descent ceiling of {ceiling}")]
    SourcesAboveCeiling { declared: usize, ceiling: usize },
    /// A precomputed reading population does not match the source population one for one.
    #[error("{readings} readings were supplied for {sources} sources")]
    ReadingsMismatch { sources: usize, readings: usize },
}

fn bound(sources: usize) -> Result<(), DescentRefusal> {
    if sources > DESCENT_SOURCE_CEILING {
        Err(DescentRefusal::SourcesAboveCeiling {
            declared: sources,
            ceiling: DESCENT_SOURCE_CEILING,
        })
    } else {
        Ok(())
    }
}

/// [definition] **The descent of a fine object through a restriction**: its coarse witness, or
/// the typed defect retaining the fibre.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Descent<W, D> {
    /// The object descends; the witness carries its coarse form.
    Witness(W),
    /// It does not; the defect retains what separates the routes.
    Defect(D),
}

impl<W, D> Descent<W, D> {
    /// Whether the object descends.
    pub fn descends(&self) -> bool {
        matches!(self, Self::Witness(_))
    }

    /// The witness, when the object descends.
    pub fn witness(&self) -> Option<&W> {
        match self {
            Self::Witness(witness) => Some(witness),
            Self::Defect(_) => None,
        }
    }

    /// The defect, when it does not.
    pub fn defect(&self) -> Option<&D> {
        match self {
            Self::Defect(defect) => Some(defect),
            Self::Witness(_) => None,
        }
    }
}

/// The square descends: each declared source's common coarse image `π A_f x = A_c π x`, in
/// declaration order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SquareWitness<T> {
    coarse_images: Vec<T>,
}

impl<T> SquareWitness<T> {
    pub fn coarse_images(&self) -> &[T] {
        &self.coarse_images
    }
}

/// One source at which the scale square breaks, with both routes and the retained fine residual.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SquareBreak<S, T, R> {
    index: usize,
    source: S,
    fine_then_restricted: T,
    restricted_then_coarse: T,
    fine_residual: R,
}

impl<S, T, R> SquareBreak<S, T, R> {
    /// The source's position in the declared population.
    pub fn index(&self) -> usize {
        self.index
    }

    /// The fine source `x`.
    pub fn source(&self) -> &S {
        &self.source
    }

    /// `π A_f x`.
    pub fn fine_then_restricted(&self) -> &T {
        &self.fine_then_restricted
    }

    /// `A_c π x`.
    pub fn restricted_then_coarse(&self) -> &T {
        &self.restricted_then_coarse
    }

    /// `π.residual(A_f x)`: with [`Self::fine_then_restricted`] it reopens the fine motion.
    pub fn fine_residual(&self) -> &R {
        &self.fine_residual
    }
}

impl<S, T, R> SquareBreak<S, T, R> {
    /// Reopen the fine motion `A_f x` from the fine route's coarse face and the retained residual:
    /// the break is not a loss (`Foundation/ContinuingTower.lean::Transition.reopen_apply`).
    pub fn reopen_fine<P>(&self, restriction: &P) -> S
    where
        P: Transition<Source = S, Target = T, Residual = R>,
    {
        restriction.reopen(&self.fine_then_restricted, &self.fine_residual)
    }
}

/// Every break of a square over a declared population.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SquareBreaks<S, T, R> {
    breaks: Vec<SquareBreak<S, T, R>>,
    checked: usize,
}

impl<S, T, R> SquareBreaks<S, T, R> {
    /// The breaks, in declaration order; never empty.
    pub fn breaks(&self) -> &[SquareBreak<S, T, R>] {
        &self.breaks
    }

    /// The first break, which is the one a first-defect check (`tube::check_commuting_square`)
    /// returns.
    pub fn first(&self) -> &SquareBreak<S, T, R> {
        &self.breaks[0]
    }

    /// How many sources were checked.
    pub fn checked(&self) -> usize {
        self.checked
    }
}

/// The square descent's return.
pub type SquareDescent<S, T, R> = Descent<SquareWitness<T>, SquareBreaks<S, T, R>>;

fn descend_square<S, T, R, E>(
    sources: &[S],
    mut restrict: impl FnMut(&S) -> Result<T, E>,
    mut residual: impl FnMut(&S) -> Result<R, E>,
    mut fine: impl FnMut(&S) -> Result<S, E>,
    mut coarse: impl FnMut(&T) -> Result<T, E>,
) -> Result<SquareDescent<S, T, R>, E>
where
    S: Clone,
    T: Clone + Eq,
{
    let mut images = Vec::with_capacity(sources.len());
    let mut breaks = Vec::new();
    for (index, source) in sources.iter().enumerate() {
        let moved = fine(source)?;
        let fine_then_restricted = restrict(&moved)?;
        let restricted_then_coarse = coarse(&restrict(source)?)?;
        if fine_then_restricted == restricted_then_coarse {
            images.push(fine_then_restricted);
        } else {
            breaks.push(SquareBreak {
                index,
                source: source.clone(),
                fine_then_restricted,
                restricted_then_coarse,
                fine_residual: residual(&moved)?,
            });
        }
    }
    Ok(if breaks.is_empty() {
        Descent::Witness(SquareWitness {
            coarse_images: images,
        })
    } else {
        Descent::Defect(SquareBreaks {
            breaks,
            checked: sources.len(),
        })
    })
}

/// [definition] **The scale square through a transition** at each declared source
/// (`Holon/Restriction.lean::scale_square_pow` at horizon one; `squareDefect` pointwise).
pub fn square_descent<P>(
    restriction: &P,
    fine: impl Fn(&P::Source) -> P::Source,
    coarse: impl Fn(&P::Target) -> P::Target,
    sources: &[P::Source],
) -> Result<SquareDescent<P::Source, P::Target, P::Residual>, DescentRefusal>
where
    P: Transition,
{
    bound(sources.len())?;
    let result: Result<_, std::convert::Infallible> = descend_square(
        sources,
        |x| Ok(restriction.apply(x)),
        |x| Ok(restriction.residual(x)),
        |x| Ok(fine(x)),
        |y| Ok(coarse(y)),
    );
    Ok(match result {
        Ok(descent) => descent,
        Err(never) => match never {},
    })
}

/// A tower-level descent's refusal: the declared population, or the tower's own refusal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TowerDescentRefusal<I, F> {
    Descent(DescentRefusal),
    Tower(TowerRefusal<I, F>),
}

/// [definition] **The scale square through one restriction of a tower**, with the residual the
/// tower supplies (`Foundation/ContinuingTower.lean::Tower.restrictTransition`: a tower's
/// restriction becomes a [`Transition`] only once its residual is supplied). The fine and coarse
/// motions may refuse in the tower's own vocabulary.
#[allow(clippy::type_complexity)]
pub fn tower_square_descent<T>(
    tower: &T,
    coarse_chart: &T::Index,
    fine_chart: &T::Index,
    fine: impl Fn(&T::Face) -> TowerFaceOutcome<T>,
    coarse: impl Fn(&T::Face) -> TowerFaceOutcome<T>,
    sources: &[T::Face],
) -> Result<
    SquareDescent<T::Face, T::Face, T::RestrictionResidual>,
    TowerDescentRefusal<T::Index, T::Face>,
>
where
    T: TowerRestrictTransition,
{
    bound(sources.len()).map_err(TowerDescentRefusal::Descent)?;
    let result: TowerOutcome<T, _> = descend_square(
        sources,
        |x| tower.restrict(coarse_chart, fine_chart, x),
        |x| tower.restriction_residual(coarse_chart, fine_chart, x),
        fine,
        coarse,
    );
    result.map_err(TowerDescentRefusal::Tower)
}

/// The reading descends: the induced coarse reading `ρ̄` on the image of `π`, one entry per
/// distinct coarse image in first-occurrence order, and how many merged pairs agreed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FactorWitness<T, V> {
    factored: Vec<(T, V)>,
    merged_pairs: usize,
}

impl<T, V> FactorWitness<T, V> {
    /// `ρ̄` on the image: `(π x, ρ x)`.
    pub fn factored(&self) -> &[(T, V)] {
        &self.factored
    }

    /// How many declared pairs `π` merges (including repeated sources).
    pub fn merged_pairs(&self) -> usize {
        self.merged_pairs
    }
}

/// Two sources `π` merges that the reading separates, with the residuals that still separate them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FactorBreak<R, V> {
    left: usize,
    right: usize,
    residuals: (R, R),
    readings: (V, V),
}

impl<R, V> FactorBreak<R, V> {
    /// The two sources' positions, `left < right`.
    pub fn pair(&self) -> (usize, usize) {
        (self.left, self.right)
    }

    /// `(π.residual(x_left), π.residual(x_right))`, which differ.
    pub fn residuals(&self) -> &(R, R) {
        &self.residuals
    }

    /// `(ρ x_left, ρ x_right)`, which differ.
    pub fn readings(&self) -> &(V, V) {
        &self.readings
    }
}

/// Every break of a factoring over a declared population.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FactorBreaks<R, V> {
    breaks: Vec<FactorBreak<R, V>>,
    merged_pairs: usize,
}

impl<R, V> FactorBreaks<R, V> {
    /// The breaks in lexicographic pair order; never empty.
    pub fn breaks(&self) -> &[FactorBreak<R, V>] {
        &self.breaks
    }

    /// The first break in lexicographic pair order.
    pub fn first(&self) -> &FactorBreak<R, V> {
        &self.breaks[0]
    }

    /// How many declared pairs `π` merges.
    pub fn merged_pairs(&self) -> usize {
        self.merged_pairs
    }
}

/// The factor descent's return.
pub type FactorDescent<T, R, V> = Descent<FactorWitness<T, V>, FactorBreaks<R, V>>;

/// [definition] **Does the reading factor through the restriction?** For every declared pair
/// `π x = π y`, `ρ x = ρ y` (`Foundation/Standing.lean::standingLaw_exists_iff_future_factors`).
/// Pairs are visited lexicographically, so the first break is the first pair a pairwise scan meets.
pub fn factor_descent<P, V>(
    restriction: &P,
    reading: impl Fn(&P::Source) -> V,
    sources: &[P::Source],
) -> Result<FactorDescent<P::Target, P::Residual, V>, DescentRefusal>
where
    P: Transition,
    V: Clone + Eq + Debug,
{
    bound(sources.len())?;
    let readings: Vec<V> = sources.iter().map(&reading).collect();
    factor_descent_over(restriction, sources, &readings)
}

/// [`factor_descent`] with the reading already taken, one value per source in declaration order —
/// for a reading that can refuse, which its owner takes (and refuses) before the descent runs.
pub fn factor_descent_over<P, V>(
    restriction: &P,
    sources: &[P::Source],
    readings: &[V],
) -> Result<FactorDescent<P::Target, P::Residual, V>, DescentRefusal>
where
    P: Transition,
    V: Clone + Eq + Debug,
{
    bound(sources.len())?;
    if readings.len() != sources.len() {
        return Err(DescentRefusal::ReadingsMismatch {
            sources: sources.len(),
            readings: readings.len(),
        });
    }
    let images: Vec<P::Target> = sources.iter().map(|x| restriction.apply(x)).collect();
    let mut merged_pairs = 0usize;
    let mut breaks = Vec::new();
    for left in 0..sources.len() {
        for right in (left + 1)..sources.len() {
            if images[left] != images[right] {
                continue;
            }
            merged_pairs += 1;
            if readings[left] != readings[right] {
                breaks.push(FactorBreak {
                    left,
                    right,
                    residuals: (
                        restriction.residual(&sources[left]),
                        restriction.residual(&sources[right]),
                    ),
                    readings: (readings[left].clone(), readings[right].clone()),
                });
            }
        }
    }
    if !breaks.is_empty() {
        return Ok(Descent::Defect(FactorBreaks {
            breaks,
            merged_pairs,
        }));
    }
    let mut factored: Vec<(P::Target, V)> = Vec::new();
    for (image, value) in images.into_iter().zip(readings) {
        if !factored.iter().any(|(seen, _)| *seen == image) {
            factored.push((image, value.clone()));
        }
    }
    Ok(Descent::Witness(FactorWitness {
        factored,
        merged_pairs,
    }))
}
