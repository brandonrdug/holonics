//! **The retained fibre and its separator: what a restriction's defect keeps.**
//!
//! [definition] A restriction `π : X → T` merges the sources of one fibre `π⁻¹(t)`
//! (`Foundation/Holon.Holon.PreimageFibre`); a reading `ρ` descends through `π` exactly when
//! it is constant on every fibre (`Holon/Restriction.descent_total`). When it does not, the
//! typed defect ([`crate::holon::restriction::Descent::Defect`]) retains two things and nothing else is
//! owed: the **fibre** — every source `π` merges, no representative selected — and the
//! **separator** — a merged pair with the witness that separates it and the two readings
//! (`Holon/Restriction.Descent.defect`). A retained separated pair refutes every coarse
//! reading (`Holon/Restriction.descent_defect_refutes_factoring`).
//!
//! ```text
//! PreimageFibre   (t, π⁻¹(t))                          a class fibre of a discrete quotient
//! AffineFibre     particular + span(radical) = A⁻¹(y)  a linear preimage (Holon/Restriction.affineFibre_mem)
//! Separation      (x, y, witness, ρ x, ρ y), π x = π y, ρ x ≠ ρ y
//! ShortestSeparator  a Separation whose witness is a shortest input word and its separating receiver
//! FibreDefect     every retained fibre and every separator of one failed descent
//! ```

use num_traits::Zero;

use crate::ratio::Rat;
use crate::ratio::linear::{ExactLinearError, ExactRatMatrix};

/// [definition] **One fibre `π⁻¹(t)` of a discrete quotient**, retained whole: the coarse (native)
/// image and every member `π` sends there, no representative selected
/// (Lean `Foundation/Holon.Holon.PreimageFibre`). `C` is the member container the instance
/// keeps (an ordered `Vec` or a `BTreeSet`).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PreimageFibre<T, C> {
    /// The coarse image `t`.
    pub native: T,
    /// `π⁻¹(t)`.
    pub members: C,
}

impl<T, C> PreimageFibre<T, C> {
    pub fn new(native: T, members: C) -> Self {
        Self { native, members }
    }

    /// Read the image and the members through charts (e.g. an index population into its items).
    pub fn map<U, D>(
        self,
        image: impl FnOnce(T) -> U,
        members: impl FnOnce(C) -> D,
    ) -> PreimageFibre<U, D> {
        PreimageFibre::new(image(self.native), members(self.members))
    }
}

/// Why a declared affine fibre is not the preimage it claims to be.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum AffineFibreDefect {
    /// The particular point, a radical direction or the target has the wrong length.
    #[error("the fibre's coordinates do not match a {rows}×{columns} operator")]
    Shape { rows: usize, columns: usize },
    /// `A · particular ≠ target`.
    #[error("the particular point does not reach the target")]
    ParticularMisses,
    /// A radical direction is zero, repeated, or not in `ker A`.
    #[error("radical direction {index} is zero, repeated or outside the kernel")]
    Radical { index: usize },
}

/// [definition] **The affine preimage `A⁻¹(y) = particular + span(radical)`**, retained instead of
/// choosing the particular point as if it were an inverse (Lean `Holon/Restriction.affineFibre_mem`:
/// every point of the span reaches the target). [`ExactRatMatrix::preimage_fibre`] returns one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AffineFibre {
    /// One point with `A · particular = y`.
    pub particular: Vec<Rat>,
    /// Directions spanning the retained part of `ker A`.
    pub radical: Vec<Vec<Rat>>,
}

impl AffineFibre {
    pub fn new(particular: Vec<Rat>, radical: Vec<Vec<Rat>>) -> Self {
        Self {
            particular,
            radical,
        }
    }

    /// The fibre's retained dimension.
    pub fn dimension(&self) -> usize {
        self.radical.len()
    }

    /// `particular + Σ cᵢ radicalᵢ`, or `None` when the coefficient count or a length disagrees.
    pub fn point(&self, coefficients: &[Rat]) -> Option<Vec<Rat>> {
        if coefficients.len() != self.radical.len() {
            return None;
        }
        let mut point = self.particular.clone();
        for (coefficient, direction) in coefficients.iter().zip(&self.radical) {
            if direction.len() != point.len() {
                return None;
            }
            for (coordinate, entry) in point.iter_mut().zip(direction) {
                *coordinate += coefficient * entry;
            }
        }
        Some(point)
    }

    /// **Is this the affine preimage of `target` under `operator`?** `A · particular = target`,
    /// and every radical direction is nonzero, distinct and in `ker A`. The span then lies in
    /// the fibre (`Holon/Restriction.affineFibre_mem`).
    pub fn check_preimage(
        &self,
        operator: &ExactRatMatrix,
        target: &[Rat],
    ) -> Result<(), AffineFibreDefect> {
        let (rows, columns) = (operator.rows(), operator.columns());
        let shape = AffineFibreDefect::Shape { rows, columns };
        if self.particular.len() != columns || target.len() != rows {
            return Err(shape);
        }
        let reached = operator
            .apply(&self.particular)
            .map_err(|_: ExactLinearError| shape.clone())?;
        if reached != target {
            return Err(AffineFibreDefect::ParticularMisses);
        }
        for (index, direction) in self.radical.iter().enumerate() {
            let repeated = self.radical[..index].contains(direction);
            let image = if direction.len() == columns {
                operator.apply(direction).ok()
            } else {
                None
            };
            let in_kernel = image.is_some_and(|image| image.iter().all(Zero::is_zero));
            if repeated || direction.iter().all(Zero::is_zero) || !in_kernel {
                return Err(AffineFibreDefect::Radical { index });
            }
        }
        Ok(())
    }
}

impl ExactRatMatrix {
    /// [`Self::preimage_fibre`] as the core [`AffineFibre`].
    pub fn affine_fibre(&self, target: &[Rat]) -> Result<Option<AffineFibre>, ExactLinearError> {
        Ok(self
            .preimage_fibre(target)?
            .map(|(particular, radical)| AffineFibre::new(particular, radical)))
    }
}

/// [definition] **A separated merged pair** — the Lean defect `Descent.defect x y merged separated`
/// (`Holon/Restriction.Descent`): two members of one fibre, the witness that separates them
/// (the residuals, a word and receiver, a coordinate) and the two readings, which differ.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Separation<M, W, V> {
    left: M,
    right: M,
    witness: W,
    readings: (V, V),
}

impl<M, W, V> Separation<M, W, V> {
    pub fn new(left: M, right: M, witness: W, readings: (V, V)) -> Self {
        Self {
            left,
            right,
            witness,
            readings,
        }
    }

    pub fn left(&self) -> &M {
        &self.left
    }

    pub fn right(&self) -> &M {
        &self.right
    }

    /// The two members, `(left, right)`.
    pub fn pair(&self) -> (M, M)
    where
        M: Clone,
    {
        (self.left.clone(), self.right.clone())
    }

    /// What separates them.
    pub fn witness(&self) -> &W {
        &self.witness
    }

    /// `(ρ left, ρ right)`.
    pub fn readings(&self) -> &(V, V) {
        &self.readings
    }
}

impl<M, R, V> Separation<M, (R, R), V> {
    /// A factor break's witness: `(π.residual(x_left), π.residual(x_right))`, which differ
    /// (`Foundation/ContinuingTower.Transition.residual_separates`).
    pub fn residuals(&self) -> &(R, R) {
        &self.witness
    }
}

/// [definition] **A shortest separator**: a pair one quotient merged that later conduct separates,
/// with the shortest input word after which a receiver sees the difference and what that receiver
/// returned (`Foundation/CausalRelevance.futureHistory_quotientNe_returns_separator`). A
/// terminus — one continues and the other does not — is itself a distinction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShortestSeparator<M, I, R, O> {
    pub left: M,
    pub right: M,
    /// The shortest word; never empty (an empty word is the one-shot reading, which merged them).
    pub distinguishing_word: Vec<I>,
    /// The receiver that finally sees it, and what the two returned.
    pub witness: Option<(R, O, O)>,
    /// True when the word separates them by a terminus rather than by two observations.
    pub separated_by_terminus: bool,
}

impl<M, I, R, O> ShortestSeparator<M, I, R, O> {
    /// The separating receiver, when one returned.
    pub fn receiver(&self) -> Option<&R> {
        self.witness.as_ref().map(|(receiver, _, _)| receiver)
    }

    /// What the left member returned to the separating receiver.
    pub(crate) fn left_observation(&self) -> Option<&O> {
        self.witness.as_ref().map(|(_, left, _)| left)
    }

    /// What the right member returned to the separating receiver.
    pub(crate) fn right_observation(&self) -> Option<&O> {
        self.witness.as_ref().map(|(_, _, right)| right)
    }

    /// Read members, word letters, receiver and observations through charts (a naming chart, an
    /// index population).
    pub fn map<M2, I2, R2, O2>(
        self,
        mut member: impl FnMut(M) -> M2,
        letter: impl FnMut(I) -> I2,
        receiver: impl FnOnce(R) -> R2,
        mut observation: impl FnMut(O) -> O2,
    ) -> ShortestSeparator<M2, I2, R2, O2> {
        ShortestSeparator {
            left: member(self.left),
            right: member(self.right),
            distinguishing_word: self.distinguishing_word.into_iter().map(letter).collect(),
            witness: self
                .witness
                .map(|(r, left, right)| (receiver(r), observation(left), observation(right))),
            separated_by_terminus: self.separated_by_terminus,
        }
    }

    /// The core separation: witness `(word, receiver)`, readings the two observations (absent on
    /// a terminus).
    pub fn separation(&self) -> Separation<M, (Vec<I>, Option<R>), Option<O>>
    where
        M: Clone,
        I: Clone,
        R: Clone,
        O: Clone,
    {
        Separation::new(
            self.left.clone(),
            self.right.clone(),
            (self.distinguishing_word.clone(), self.receiver().cloned()),
            (
                self.left_observation().cloned(),
                self.right_observation().cloned(),
            ),
        )
    }
}

/// [definition] **The typed defect of a failed descent retains its fibres and its separators**:
/// every fibre the restriction merges and every merged pair a reading separates. Nothing further
/// is owed to reconstruct what the restriction hid.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FibreDefect<F, S> {
    fibres: Vec<F>,
    separators: Vec<S>,
}

impl<F, S> FibreDefect<F, S> {
    pub fn new(fibres: Vec<F>, separators: Vec<S>) -> Self {
        Self { fibres, separators }
    }

    /// The retained fibres.
    pub fn fibres(&self) -> &[F] {
        &self.fibres
    }

    /// The separators, in the owner's declared order.
    pub fn separators(&self) -> &[S] {
        &self.separators
    }

    /// The first separator (the one a first-defect scan meets); `None` only for a defect built
    /// without one.
    pub fn first(&self) -> Option<&S> {
        self.separators.first()
    }
}

impl<T, S> FibreDefect<PreimageFibre<T, Vec<usize>>, S> {
    /// How many declared pairs the restriction merges: `Σ C(|fibre|, 2)` over the retained fibres.
    pub fn merged_pairs(&self) -> usize {
        self.fibres
            .iter()
            .map(|fibre| fibre.members.len() * fibre.members.len().saturating_sub(1) / 2)
            .sum()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64) -> Rat {
        Rat::from_integer(n.into())
    }

    #[test]
    fn the_affine_fibre_is_the_preimage_and_every_span_point_reaches_the_target() {
        // A = [1 1 0; 0 0 1], y = (2, 3): fibre (2,0,3) + span((-1,1,0)).
        let operator =
            ExactRatMatrix::new(vec![vec![q(1), q(1), q(0)], vec![q(0), q(0), q(1)]]).unwrap();
        let target = vec![q(2), q(3)];
        let fibre = operator.affine_fibre(&target).unwrap().unwrap();
        assert_eq!(fibre.dimension(), 1);
        fibre.check_preimage(&operator, &target).unwrap();
        for c in -2..=2 {
            let point = fibre.point(&[q(c)]).unwrap();
            assert_eq!(operator.apply(&point).unwrap(), target);
        }
        let mut wrong = fibre.clone();
        wrong.radical.push(vec![q(1), q(0), q(0)]);
        assert_eq!(
            wrong.check_preimage(&operator, &target),
            Err(AffineFibreDefect::Radical { index: 1 })
        );
        let mut repeated = fibre.clone();
        repeated.radical.push(repeated.radical[0].clone());
        assert_eq!(
            repeated.check_preimage(&operator, &target),
            Err(AffineFibreDefect::Radical { index: 1 })
        );
        assert_eq!(
            fibre.check_preimage(&operator, &[q(2), q(4)]),
            Err(AffineFibreDefect::ParticularMisses)
        );
    }

    #[test]
    fn a_shortest_separator_reads_as_a_separation() {
        let separator: ShortestSeparator<u8, char, &str, u32> = ShortestSeparator {
            left: 1,
            right: 2,
            distinguishing_word: vec!['a', 'b'],
            witness: Some(("r", 10, 11)),
            separated_by_terminus: false,
        };
        let separation = separator.separation();
        assert_eq!(separation.pair(), (1, 2));
        assert_eq!(separation.witness(), &(vec!['a', 'b'], Some("r")));
        assert_eq!(separation.readings(), &(Some(10), Some(11)));
        let named = separator.clone().map(
            |m| m.to_string(),
            |c| c.to_string(),
            |r| Some(r.to_owned()),
            |o| Some(o.to_string()),
        );
        assert_eq!(named.receiver(), Some(&Some("r".to_owned())));
        assert_eq!(named.left_observation(), Some(&Some("10".to_owned())));
    }
}
