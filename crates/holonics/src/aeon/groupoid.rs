//! **The aeon groupoid: occurrences, passages and the aeons between them.**
//!
//! [definition] Lean `Aeon/Clock/Groupoid`. A Holarchy's parametric orientation is carried by an
//! oriented complex up to dimension two ([`ParametricComplex`]): occurrences, oriented passages of
//! the motion, and two-cells bounded by closed words of signed passages (a place where two
//! passages commute, or any declared circuit). An [`Aeon`] from `u` to `v` is a chained word of
//! signed passages. Aeons compose by concatenation, orientation reversal is the inverse, and the
//! elementary moves (insert a backtrack `s s⁻¹`, insert a two-cell boundary) generate homotopy:
//! occurrences and homotopy classes of aeons form a groupoid (`instGroupoid`).
//!
//! Two complexes are provided. [`FiniteComplex`] is a finite cell complex
//! ([`crate::geometry::complex::CellComplex`]) whose two-cells carry their boundary words.
//! [`ClockLift`] is the lift of the navigators' joint clock torus (Lean `Aeon/Clock/Winding.clockLift`):
//! lattice points of micro-step potentials, one passage per navigator micro-step, one square
//! wherever two navigators commute; its circles' periods are the navigators' ring periods
//! ([`crate::navigator::Clock::period`]). An aeon there retains the winding its projection to the
//! torus forgets, and a [`Cycle`] is an aeon that closes on the torus.

use std::fmt;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};

use crate::aeon::AeonError;
use crate::geometry::complex::CellComplex;
use crate::navigator::Clock as NavigatorClock;
use crate::ratio::Rat;
use crate::ratio::linear::vector::at;

/// [definition] **A signed step**: a passage traversed along (`forward`) or against its
/// orientation. Lean `E × Bool`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Step<P> {
    pub passage: P,
    pub forward: bool,
}

impl<P: Clone> Step<P> {
    pub fn along(passage: P) -> Self {
        Self {
            passage,
            forward: true,
        }
    }

    pub fn against(passage: P) -> Self {
        Self {
            passage,
            forward: false,
        }
    }

    /// The step traversed the other way. Lean `reverseStep`.
    pub fn reversed(&self) -> Self {
        Self {
            passage: self.passage.clone(),
            forward: !self.forward,
        }
    }
}

/// The reversed word: the steps in reverse order, each traversed the other way. Lean `reverseWord`.
fn reverse_word<P: Clone>(word: &[Step<P>]) -> Vec<Step<P>> {
    word.iter().rev().map(Step::reversed).collect()
}

/// [definition] **The parametric complex** of a Holarchy's orientation. Lean `ParametricComplex`:
/// `ends` is `(src, tgt)` and `cell` is `(base, boundary)`. Each cell's boundary word is a loop at
/// its base (`WellFormed`); the implementations below establish it.
pub trait ParametricComplex {
    type Occurrence: Clone + Eq + fmt::Debug;
    type Passage: Clone + Eq + fmt::Debug;
    type Cell: Clone + fmt::Debug;

    /// The occurrences a passage runs from and to, or `None` when it is not a passage here.
    fn ends(&self, passage: &Self::Passage) -> Option<(Self::Occurrence, Self::Occurrence)>;

    /// The base occurrence and boundary word of a two-cell, or `None` when it is not a cell here.
    fn cell(&self, cell: &Self::Cell) -> Option<(Self::Occurrence, Vec<Step<Self::Passage>>)>;

    /// Whether the motion is back in its phase state: equality of occurrences on the complex
    /// itself; the lift of a torus overrides it with closure on the torus (`torus_closes_iff`).
    fn returns(&self, from: &Self::Occurrence, to: &Self::Occurrence) -> bool {
        from == to
    }

    /// The occurrence a signed step leaves and the one it reaches. Lean `start`, `finish`.
    fn step_ends(
        &self,
        step: &Step<Self::Passage>,
    ) -> Option<(Self::Occurrence, Self::Occurrence)> {
        let (source, target) = self.ends(&step.passage)?;
        Some(if step.forward {
            (source, target)
        } else {
            (target, source)
        })
    }
}

/// [definition] **An aeon**: a chained word of signed passages, with the occurrences it visits.
/// Lean `Aeon`; the stored occurrences are the `Chained` certificate read out.
pub struct Aeon<K: ParametricComplex> {
    occurrences: Vec<K::Occurrence>,
    steps: Vec<Step<K::Passage>>,
}

impl<K: ParametricComplex> Clone for Aeon<K> {
    fn clone(&self) -> Self {
        Self {
            occurrences: self.occurrences.clone(),
            steps: self.steps.clone(),
        }
    }
}

impl<K: ParametricComplex> PartialEq for Aeon<K> {
    fn eq(&self, other: &Self) -> bool {
        self.occurrences == other.occurrences && self.steps == other.steps
    }
}

impl<K: ParametricComplex> Eq for Aeon<K> {}

impl<K: ParametricComplex> fmt::Debug for Aeon<K> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Aeon")
            .field("occurrences", &self.occurrences)
            .field("steps", &self.steps)
            .finish()
    }
}

impl<K: ParametricComplex> Aeon<K> {
    /// The aeon of a word from `start`, refused at the first step that is not a passage or does
    /// not leave the occurrence reached (Lean `Chained`).
    pub fn new(
        complex: &K,
        start: K::Occurrence,
        steps: Vec<Step<K::Passage>>,
    ) -> Result<Self, AeonError> {
        let mut occurrences = Vec::with_capacity(steps.len() + 1);
        occurrences.push(start);
        for (position, step) in steps.iter().enumerate() {
            let (from, to) = complex
                .step_ends(step)
                .ok_or(AeonError::NotAPassage { position })?;
            if occurrences.last() != Some(&from) {
                return Err(AeonError::NotChained { position });
            }
            occurrences.push(to);
        }
        Ok(Self { occurrences, steps })
    }

    /// The motionless aeon at an occurrence. Lean `Aeon.rest`.
    pub fn rest(at: K::Occurrence) -> Self {
        Self {
            occurrences: vec![at],
            steps: Vec::new(),
        }
    }

    pub fn start(&self) -> &K::Occurrence {
        &self.occurrences[0]
    }

    pub fn end(&self) -> &K::Occurrence {
        &self.occurrences[self.occurrences.len() - 1]
    }

    pub fn steps(&self) -> &[Step<K::Passage>] {
        &self.steps
    }

    /// The occurrences visited, `steps + 1` of them: the aeon's micro-states.
    pub fn occurrences(&self) -> &[K::Occurrence] {
        &self.occurrences
    }

    /// **Concatenation**: this aeon, then `next`. Lean `Aeon.concat`; refused unless this aeon ends
    /// where `next` begins.
    pub fn concat(&self, next: &Self) -> Result<Self, AeonError> {
        if self.end() != next.start() {
            return Err(AeonError::NotComposable);
        }
        let mut occurrences = self.occurrences.clone();
        occurrences.extend(next.occurrences.iter().skip(1).cloned());
        let mut steps = self.steps.clone();
        steps.extend(next.steps.iter().cloned());
        Ok(Self { occurrences, steps })
    }

    /// **Orientation reversal** `Rγ`: the same occurrences, run backwards. Lean `Aeon.reverse`.
    pub fn reverse(&self) -> Self {
        Self {
            occurrences: self.occurrences.iter().rev().cloned().collect(),
            steps: reverse_word(&self.steps),
        }
    }

    /// A loop repeated `times` times, rest for zero. Lean `Reading.iterate`; refused unless the
    /// aeon ends where it begins.
    pub fn repeated(&self, times: usize) -> Result<Self, AeonError> {
        if self.start() != self.end() {
            return Err(AeonError::NotALoop);
        }
        let mut result = Self::rest(self.start().clone());
        for _ in 0..times {
            result = result.concat(self)?;
        }
        Ok(result)
    }

    /// **The backtrack move**: insert `s s⁻¹` before step `position`. Lean
    /// `Aeon/Clock/Groupoid.Move.backtrack`.
    pub fn with_backtrack(
        &self,
        complex: &K,
        position: usize,
        step: Step<K::Passage>,
    ) -> Result<Self, AeonError> {
        if position > self.steps.len() {
            return Err(AeonError::PositionOutside { position });
        }
        let reversed = step.reversed();
        self.inserted(complex, position, vec![step, reversed])
    }

    /// **The face move**: insert the boundary of a two-cell, in either orientation, before step
    /// `position`, where the aeon stands at the cell's base. Lean `Move.face`, `Move.faceReversed`.
    pub fn with_cell(
        &self,
        complex: &K,
        position: usize,
        cell: &K::Cell,
        forward: bool,
    ) -> Result<Self, AeonError> {
        let occurrence = self
            .occurrences
            .get(position)
            .ok_or(AeonError::PositionOutside { position })?;
        let (base, word) = complex.cell(cell).ok_or(AeonError::NotACell)?;
        if &base != occurrence {
            return Err(AeonError::NotAtBase { position });
        }
        let word = if forward { word } else { reverse_word(&word) };
        self.inserted(complex, position, word)
    }

    fn inserted(
        &self,
        complex: &K,
        position: usize,
        word: Vec<Step<K::Passage>>,
    ) -> Result<Self, AeonError> {
        let mut steps = self.steps[..position].to_vec();
        steps.extend(word);
        steps.extend(self.steps[position..].iter().cloned());
        Self::new(complex, self.start().clone(), steps)
    }

    /// **The free reduction**: every adjacent backtrack `s s⁻¹` cancelled. Each cancellation is a
    /// backtrack move read backwards, so the result is homotopic to the aeon; an aeon followed by
    /// its reversal reduces to rest (Lean `concat_reverse_homotopic`).
    pub fn reduced(&self) -> Self {
        let mut occurrences = vec![self.start().clone()];
        let mut steps: Vec<Step<K::Passage>> = Vec::with_capacity(self.steps.len());
        for (step, reached) in self.steps.iter().zip(self.occurrences.iter().skip(1)) {
            if steps.last() == Some(&step.reversed()) {
                steps.pop();
                occurrences.pop();
            } else {
                steps.push(step.clone());
                occurrences.push(reached.clone());
            }
        }
        Self { occurrences, steps }
    }
}

/// [definition] **A cycle**: an aeon that returns to its phase state — completeness, not a
/// duration. On a complex that is equality of its two occurrences; on the lift of the clock torus
/// it is closure on the torus (Lean `Winding.torus_closes_iff`).
pub struct Cycle<K: ParametricComplex> {
    aeon: Aeon<K>,
}

impl<K: ParametricComplex> Clone for Cycle<K> {
    fn clone(&self) -> Self {
        Self {
            aeon: self.aeon.clone(),
        }
    }
}

impl<K: ParametricComplex> fmt::Debug for Cycle<K> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Cycle")
            .field("aeon", &self.aeon)
            .finish()
    }
}

impl<K: ParametricComplex> Cycle<K> {
    /// The aeon as a cycle, refused when it does not return to its phase state.
    pub fn close(complex: &K, aeon: Aeon<K>) -> Result<Self, AeonError> {
        if !complex.returns(aeon.start(), aeon.end()) {
            return Err(AeonError::NotACycle);
        }
        Ok(Self { aeon })
    }

    pub fn aeon(&self) -> &Aeon<K> {
        &self.aeon
    }
}

// ---------------------------------------------------------------------------------------------
// The finite complex
// ---------------------------------------------------------------------------------------------

/// [definition] **A finite parametric complex**: a [`CellComplex`] of dimension one or two whose
/// every edge column of `∂₁` is an oriented passage (`−1` at its source, `+1` at its target) and
/// whose every two-cell carries a boundary word: a closed chained loop at its base whose chain is
/// the cell's column of `∂₂` (Lean `incidence₂`). Occurrences, passages and cells are indices.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteComplex {
    cells: CellComplex,
    sources: Vec<usize>,
    targets: Vec<usize>,
    faces: Vec<(usize, Vec<Step<usize>>)>,
}

impl FiniteComplex {
    /// Validate the passages and every face word against the complex's own boundaries.
    pub fn new(
        cells: CellComplex,
        faces: Vec<(usize, Vec<Step<usize>>)>,
    ) -> Result<Self, AeonError> {
        if !(1..=2).contains(&cells.dimension()) {
            return Err(AeonError::Shape {
                what: "parametric complex dimension (one or two)",
                expected: 2,
                found: cells.dimension(),
            });
        }
        if faces.len() != cells.cells(2) {
            return Err(AeonError::Shape {
                what: "face words (one per two-cell)",
                expected: cells.cells(2),
                found: faces.len(),
            });
        }
        let passages = cells.connection(vec![Rat::one(); cells.cells(1)])?;
        let complex = Self {
            sources: passages.sources().to_vec(),
            targets: passages.targets().to_vec(),
            cells,
            faces: Vec::new(),
        };
        for (face, (base, word)) in faces.iter().enumerate() {
            if *base >= complex.occurrences() {
                return Err(AeonError::FaceNotALoop { face });
            }
            let aeon = Aeon::new(&complex, *base, word.clone())
                .map_err(|_| AeonError::FaceNotALoop { face })?;
            if aeon.end() != base {
                return Err(AeonError::FaceNotALoop { face });
            }
            let boundary = complex
                .cells
                .boundary(2)
                .ok_or(AeonError::FaceNotItsBoundary { face })?;
            let chain = complex.chain(&aeon);
            if (0..complex.passages()).any(|edge| chain[edge] != at(boundary, edge, face)) {
                return Err(AeonError::FaceNotItsBoundary { face });
            }
        }
        Ok(Self { faces, ..complex })
    }

    /// An oriented graph as a parametric complex with no two-cells ([`CellComplex::graph`]).
    pub fn graph(vertices: usize, sources: &[usize], targets: &[usize]) -> Result<Self, AeonError> {
        Self::new(CellComplex::graph(vertices, sources, targets)?, Vec::new())
    }

    pub fn cell_complex(&self) -> &CellComplex {
        &self.cells
    }

    pub fn occurrences(&self) -> usize {
        self.cells.cells(0)
    }

    pub fn passages(&self) -> usize {
        self.cells.cells(1)
    }

    pub fn two_cells(&self) -> usize {
        self.faces.len()
    }

    /// [definition] **The 1-chain of an aeon**: the signed number of traversals of each passage.
    /// Lean `chainOf`; a clock's reading is its pairing with this chain (`wordReading_eq_dotProduct`).
    pub fn chain(&self, aeon: &Aeon<Self>) -> Vec<Rat> {
        let mut chain = vec![Rat::zero(); self.passages()];
        for step in aeon.steps() {
            if let Some(entry) = chain.get_mut(step.passage) {
                if step.forward {
                    *entry += Rat::one();
                } else {
                    *entry -= Rat::one();
                }
            }
        }
        chain
    }
}

impl ParametricComplex for FiniteComplex {
    type Occurrence = usize;
    type Passage = usize;
    type Cell = usize;

    fn ends(&self, passage: &usize) -> Option<(usize, usize)> {
        Some((*self.sources.get(*passage)?, *self.targets.get(*passage)?))
    }

    fn cell(&self, cell: &usize) -> Option<(usize, Vec<Step<usize>>)> {
        self.faces.get(*cell).cloned()
    }
}

// ---------------------------------------------------------------------------------------------
// The lift of the navigators' joint clock torus
// ---------------------------------------------------------------------------------------------

/// [definition] **A passage of the lift**: navigator `navigator` advances one micro-step from the
/// lattice point `from`. Lean `clockLift` edge `(x, i)`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LiftPassage {
    pub from: Vec<BigInt>,
    pub navigator: usize,
}

/// [definition] **A square of the lift**: navigators `first` and `second` commute at `base`.
/// Lean `clockLift` two-cell `(x, i, j)`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LiftSquare {
    pub base: Vec<BigInt>,
    pub first: usize,
    pub second: usize,
}

/// [definition] **The lift of the navigators' joint clock torus** `Π ℤ/dᵢ` to the lattice `ℤᵏ` of
/// micro-step potentials. Lean `Aeon/Clock/Winding.clockLift`; each square closes because two
/// navigators commute (`clockLift_wellFormed`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClockLift {
    periods: Vec<BigUint>,
}

impl ClockLift {
    /// The lift of a torus of declared periods, each at least one micro-step.
    pub fn new(periods: Vec<BigUint>) -> Result<Self, AeonError> {
        if periods.iter().any(Zero::is_zero) {
            return Err(AeonError::ZeroPeriod);
        }
        Ok(Self { periods })
    }

    /// The lift of the navigators' joint clock torus: one circle per navigator clock, of its ring
    /// period.
    pub fn of_clocks(clocks: &[NavigatorClock]) -> Self {
        Self {
            periods: clocks.iter().map(NavigatorClock::period).collect(),
        }
    }

    pub fn periods(&self) -> &[BigUint] {
        &self.periods
    }

    pub fn navigators(&self) -> usize {
        self.periods.len()
    }

    /// One micro-step of `navigator` from `at`, forward or back.
    pub fn step(&self, at: &[BigInt], navigator: usize, forward: bool) -> Step<LiftPassage> {
        let mut from = at.to_vec();
        if !forward && let Some(coordinate) = from.get_mut(navigator) {
            *coordinate -= BigInt::one();
        }
        Step {
            passage: LiftPassage { from, navigator },
            forward,
        }
    }

    /// The aeon of a sequence of micro-steps `(navigator, forward)` from `start`.
    pub fn walk(
        &self,
        start: Vec<BigInt>,
        moves: &[(usize, bool)],
    ) -> Result<Aeon<Self>, AeonError> {
        let mut at = start.clone();
        let mut steps = Vec::with_capacity(moves.len());
        for (position, (navigator, forward)) in moves.iter().enumerate() {
            let step = self.step(&at, *navigator, *forward);
            let (_, reached) = self
                .step_ends(&step)
                .ok_or(AeonError::NotAPassage { position })?;
            at = reached;
            steps.push(step);
        }
        Aeon::new(self, start, steps)
    }

    /// The torus point of a lift point: each coordinate's residue modulo its period. Lean
    /// `torusPoint`.
    pub fn torus_point(&self, point: &[BigInt]) -> Vec<BigUint> {
        point
            .iter()
            .zip(&self.periods)
            .map(|(coordinate, period)| {
                let period = BigInt::from(period.clone());
                let mut residue = coordinate % &period;
                if residue.is_negative() {
                    residue += &period;
                }
                residue.magnitude().clone()
            })
            .collect()
    }

    fn translated(&self, point: &[BigInt], navigator: usize) -> Vec<BigInt> {
        let mut reached = point.to_vec();
        reached[navigator] += BigInt::one();
        reached
    }
}

impl ParametricComplex for ClockLift {
    type Occurrence = Vec<BigInt>;
    type Passage = LiftPassage;
    type Cell = LiftSquare;

    fn ends(&self, passage: &LiftPassage) -> Option<(Vec<BigInt>, Vec<BigInt>)> {
        if passage.from.len() != self.navigators() || passage.navigator >= self.navigators() {
            return None;
        }
        Some((
            passage.from.clone(),
            self.translated(&passage.from, passage.navigator),
        ))
    }

    fn cell(&self, cell: &LiftSquare) -> Option<(Vec<BigInt>, Vec<Step<LiftPassage>>)> {
        let k = self.navigators();
        if cell.base.len() != k || cell.first >= k || cell.second >= k {
            return None;
        }
        let passage = |from: Vec<BigInt>, navigator: usize| LiftPassage { from, navigator };
        let x = &cell.base;
        Some((
            x.clone(),
            vec![
                Step::along(passage(x.clone(), cell.first)),
                Step::along(passage(self.translated(x, cell.first), cell.second)),
                Step::against(passage(self.translated(x, cell.second), cell.first)),
                Step::against(passage(x.clone(), cell.second)),
            ],
        ))
    }

    /// Closure on the torus: every navigator's displacement is a whole number of its periods.
    /// Lean `torus_closes_iff`.
    fn returns(&self, from: &Vec<BigInt>, to: &Vec<BigInt>) -> bool {
        from.len() == self.navigators()
            && to.len() == self.navigators()
            && from
                .iter()
                .zip(to)
                .zip(&self.periods)
                .all(|((a, b), period)| ((b - a) % BigInt::from(period.clone())).is_zero())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lattice(values: &[i64]) -> Vec<BigInt> {
        values.iter().map(|value| BigInt::from(*value)).collect()
    }

    /// **The aeon groupoid.** Concatenation is associative with rest as unit, reversal is an
    /// involution that reverses a composite, and an aeon followed by its reversal is homotopic to
    /// rest (its free reduction is rest). Lean `Aeon/Clock/Groupoid.instGroupoid`, over
    /// `Aeon.concat_assoc`, `Aeon.rest_concat`, `Aeon.concat_rest`, `Aeon.reverse_reverse`,
    /// `Aeon.reverse_concat`, `concat_reverse_homotopic`, `reverse_concat_homotopic`.
    #[test]
    fn aeons_form_a_groupoid() {
        let lift = ClockLift::new(vec![BigUint::from(3u32), BigUint::from(2u32)]).unwrap();
        let gamma = lift
            .walk(lattice(&[0, 0]), &[(0, true), (1, true), (0, true)])
            .unwrap();
        let delta = lift
            .walk(gamma.end().clone(), &[(1, false), (0, true)])
            .unwrap();
        let epsilon = lift
            .walk(delta.end().clone(), &[(1, true), (1, true), (0, false)])
            .unwrap();
        let left = gamma.concat(&delta).unwrap().concat(&epsilon).unwrap();
        let right = gamma.concat(&delta.concat(&epsilon).unwrap()).unwrap();
        assert_eq!(left, right);
        assert_eq!(
            Aeon::rest(gamma.start().clone()).concat(&gamma).unwrap(),
            gamma
        );
        assert_eq!(
            gamma.concat(&Aeon::rest(gamma.end().clone())).unwrap(),
            gamma
        );
        assert_eq!(gamma.reverse().reverse(), gamma);
        assert_eq!(
            gamma.concat(&delta).unwrap().reverse(),
            delta.reverse().concat(&gamma.reverse()).unwrap()
        );
        assert_eq!(
            gamma.concat(&gamma.reverse()).unwrap().reduced(),
            Aeon::rest(gamma.start().clone())
        );
        assert_eq!(
            gamma.reverse().concat(&gamma).unwrap().reduced(),
            Aeon::rest(gamma.end().clone())
        );
        assert_eq!(epsilon.concat(&gamma), Err(AeonError::NotComposable));
    }
}
