//! **Hodge-decomposed time on a finite cell complex.**
//!
//! [definition] Lean `Aeon/Production/HodgeTime` and the aeon record (A2). A time form `ω` on the
//! passages of a [`FiniteComplex`] splits, in a declared positive metric on each degree, as
//!
//! ```text
//! ω = dφ + δβ + h          state (exact) + production (coexact) + winding (harmonic)
//! ```
//!
//! ([`hodge_split`]): `dφ` is the metric projection onto the image of `d₀`, found from the exact
//! rational solve `δ₀ d₀ φ = δ₀ ω`; `δβ` the projection onto the image of the codifferential
//! `δ₁ = W₁⁻¹ d₁ᵀ W₂`, from `d₁ δ₁ β = d₁ ω`; `h` the remainder, certified by `d₁ h = 0` and
//! `δ₀ h = 0`. The three parts are three kinds of time, read on the same
//! [`Aeon`](crate::aeon::Aeon)s as every clock ([`Form::read`], the pairing with the aeon's chain):
//!
//! - **state time** is read by the aeon's two bounding occurrences, `φ(v) − φ(u)` (Stokes);
//! - **winding time** is closed, so homologous cycles read it alike;
//! - **production time** is the curvature: on a cell boundary only it reads, and its reading is
//!   the curvature flux `d₁ω` through the cell. It vanishes exactly when the form is a clock
//!   (`production_ne_zero_iff_not_closed`; on a groupoid aeon, `isClosed_iff_production_zero`).
//!
//! The linear solves are [`crate::ratio::linear::ExactRatMatrix::preimage_fibre`]; the metric
//! adjoints are [`CellComplex::codifferential`].

use num_traits::Zero;

use crate::aeon::AeonError;
use crate::aeon::groupoid::FiniteComplex;
use crate::aeon::reading::Form;
use crate::geometry::complex::CellComplex;
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::inertia::SymmetricForm;
use crate::ratio::linear::vector::{is_zero, sub};

/// [definition] **The Hodge split of a time form**, with the potential `φ` of its state part (one
/// representative of its fibre). Lean `Aeon/Production/HodgeTime.TimeSplit`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TimeSplit {
    pub state: Form,
    pub production: Form,
    pub winding: Form,
    pub potential: Vec<Rat>,
}

/// [definition] **The Hodge split** of `form` under the declared metrics `W₀, W₁, W₂` (one per
/// degree; a one-dimensional complex takes two). Existence and uniqueness are Lean
/// `Aeon/Production/HodgeTime.timeSplit_nonempty`, `timeSplit_unique`.
pub fn hodge_split(
    complex: &FiniteComplex,
    metrics: &[SymmetricForm],
    form: &Form,
) -> Result<TimeSplit, AeonError> {
    let cells = complex.cell_complex();
    if metrics.len() != cells.dimension() + 1 {
        return Err(AeonError::Shape {
            what: "metrics (one per degree)",
            expected: cells.dimension() + 1,
            found: metrics.len(),
        });
    }
    if form.values().len() != complex.passages() {
        return Err(AeonError::Shape {
            what: "form values (one per passage)",
            expected: complex.passages(),
            found: form.values().len(),
        });
    }
    let omega = form.values();
    let d0 = coboundary(cells, 0)?;
    let delta0 = cells.codifferential(0, &metrics[0], &metrics[1])?;
    let potential = solve(&delta0.multiply(&d0)?, &delta0.apply(omega)?)?;
    let state = d0.apply(&potential)?;
    let (production, curvature_operator) = if complex.two_cells() == 0 {
        (vec![Rat::zero(); complex.passages()], None)
    } else {
        let d1 = coboundary(cells, 1)?;
        let delta1 = cells.codifferential(1, &metrics[1], &metrics[2])?;
        let circulation = solve(&d1.multiply(&delta1)?, &d1.apply(omega)?)?;
        (delta1.apply(&circulation)?, Some(d1))
    };
    let winding = sub(&sub(omega, &state), &production);
    let closed = match &curvature_operator {
        Some(d1) => is_zero(&d1.apply(&winding)?),
        None => true,
    };
    if !closed || !is_zero(&delta0.apply(&winding)?) {
        return Err(AeonError::NotHarmonic);
    }
    Ok(TimeSplit {
        state: Form::new(state),
        production: Form::new(production),
        winding: Form::new(winding),
        potential,
    })
}

/// `d_k = ∂_(k+1)ᵀ`, the coboundary of degree `k`.
fn coboundary(cells: &CellComplex, degree: usize) -> Result<ExactRatMatrix, AeonError> {
    let boundary = cells.boundary(degree + 1).ok_or(AeonError::Shape {
        what: "complex dimension for a coboundary",
        expected: degree + 1,
        found: cells.dimension(),
    })?;
    Ok(boundary.transpose()?)
}

/// One solution of `A x = b`; the fibre's kernel does not move the projection `x ↦ M x` that the
/// caller reads, because `A = N M` with `ker A = ker M`.
fn solve(operator: &ExactRatMatrix, target: &[Rat]) -> Result<Vec<Rat>, AeonError> {
    match operator.preimage_fibre(target)? {
        Some((particular, _kernel)) => Ok(particular),
        None => Err(AeonError::NotHarmonic),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aeon::groupoid::{Aeon, Step};
    use crate::aeon::reading::ClosedForm;
    use crate::ratio::integer;
    use crate::ratio::linear::vector::{dot, form_matrix, integer_matrix, ints};
    use crate::ratio::rat;
    use num_traits::One;

    /// The filled triangle `0→1→2→0` and the hollow triangle `2→3→0` sharing the passage `2→0`.
    fn filled_and_hollow() -> FiniteComplex {
        let boundary_one = integer_matrix(&[
            &[-1, 0, 1, 0, 1],
            &[1, -1, 0, 0, 0],
            &[0, 1, -1, -1, 0],
            &[0, 0, 0, 1, -1],
        ])
        .unwrap();
        let boundary_two = integer_matrix(&[&[1], &[1], &[1], &[0], &[0]]).unwrap();
        FiniteComplex::new(
            CellComplex::new(vec![4, 5, 1], vec![boundary_one, boundary_two]).unwrap(),
            vec![(0, vec![Step::along(0), Step::along(1), Step::along(2)])],
        )
        .unwrap()
    }

    fn metrics() -> Vec<SymmetricForm> {
        vec![
            SymmetricForm::from_diagonal(ints(&[1, 2, 1, 3])),
            SymmetricForm::from_diagonal(ints(&[2, 1, 1, 3, 1])),
            SymmetricForm::from_diagonal(ints(&[5])),
        ]
    }

    fn unit(extent: usize) -> SymmetricForm {
        SymmetricForm::from_diagonal(vec![Rat::one(); extent])
    }

    /// **Every time form splits into state, production and winding time**, orthogonally in the
    /// declared metric, and the split is unique: splitting a part returns it. Lean
    /// `HodgeTime.timeSplit_nonempty`, `timeSplit_unique`.
    #[test]
    fn every_time_form_splits_into_three_kinds_of_time() {
        let complex = filled_and_hollow();
        let metrics = metrics();
        let form = Form::new(vec![
            rat(3, 2),
            integer(-1),
            integer(4),
            rat(2, 3),
            integer(1),
        ]);
        let split = hodge_split(&complex, &metrics, &form).unwrap();
        for part in [&split.state, &split.production, &split.winding] {
            assert!(!is_zero(part.values()), "each kind of time is present");
        }
        let total: Vec<Rat> = (0..5)
            .map(|edge| {
                &split.state.values()[edge]
                    + &split.production.values()[edge]
                    + &split.winding.values()[edge]
            })
            .collect();
        assert_eq!(total, form.values());
        let w1 = form_matrix(&metrics[1]);
        let inner = |a: &Form, b: &Form| dot(&w1.apply(a.values()).unwrap(), b.values());
        assert!(inner(&split.state, &split.production).is_zero());
        assert!(inner(&split.state, &split.winding).is_zero());
        assert!(inner(&split.production, &split.winding).is_zero());
        for part in [&split.state, &split.production, &split.winding] {
            let again = hodge_split(&complex, &metrics, part).unwrap();
            let zero = Form::new(vec![Rat::zero(); 5]);
            let expected = [&split.state, &split.production, &split.winding].map(|kind| {
                if std::ptr::eq(kind, part) {
                    part.clone()
                } else {
                    zero.clone()
                }
            });
            assert_eq!([again.state, again.production, again.winding], expected);
        }
    }

    /// **The three kinds of time read as stated.** State time is read by the bounding occurrences,
    /// `φ(v) − φ(u)`; winding time reads homologous cycles alike; on a cell boundary only
    /// production time reads, and it reads the curvature flux; the production part of a clock is
    /// zero. Lean `HodgeTime.state_reading_of_walk`, `winding_reading_homology_invariant`,
    /// `cell_boundary_reads_production`, `cell_boundary_reading_is_curvature_flux`,
    /// `production_ne_zero_iff_not_closed`.
    #[test]
    fn the_three_kinds_of_time_read_as_stated() {
        let complex = filled_and_hollow();
        let metrics = metrics();
        let form = Form::new(vec![
            rat(3, 2),
            integer(-1),
            integer(4),
            rat(2, 3),
            integer(1),
        ]);
        let split = hodge_split(&complex, &metrics, &form).unwrap();
        let walk = Aeon::new(&complex, 1, vec![Step::along(1), Step::along(3)]).unwrap();
        assert_eq!(
            split.state.read(&walk).unwrap(),
            &split.potential[3] - &split.potential[1]
        );
        let loop_b = Aeon::new(
            &complex,
            2,
            vec![Step::along(3), Step::along(4), Step::against(2)],
        )
        .unwrap();
        let through_face = Aeon::new(
            &complex,
            0,
            vec![
                Step::along(0),
                Step::along(1),
                Step::along(3),
                Step::along(4),
            ],
        )
        .unwrap();
        assert_eq!(
            split.winding.read(&loop_b).unwrap(),
            split.winding.read(&through_face).unwrap()
        );
        let cell_boundary = Aeon::rest(0).with_cell(&complex, 0, &0, true).unwrap();
        let curvature = form.curvature(&complex).unwrap();
        assert_eq!(form.read(&cell_boundary).unwrap(), curvature[0]);
        assert_eq!(split.production.read(&cell_boundary).unwrap(), curvature[0]);
        assert!(split.state.read(&cell_boundary).unwrap().is_zero());
        assert!(split.winding.read(&cell_boundary).unwrap().is_zero());
        let clock = ClosedForm::new(&complex, split.winding.clone()).unwrap();
        let clock_split = hodge_split(&complex, &metrics, clock.form()).unwrap();
        assert!(is_zero(clock_split.production.values()));
    }

    /// [counterexample] **A non-closed form has production time.** On the filled triangle with the
    /// unit metric the single tick `(1,0,0)` splits as `(2/3,−1/3,−1/3)` of state time plus
    /// `(1/3,1/3,1/3)` of production time, with no winding time, and its production part reads `1`
    /// around the loop that bounds the face. Lean `HodgeTime.FilledTriangle.filledTriangle_split`,
    /// `filledTriangle_production_reads_the_loop`.
    #[test]
    fn a_nonclosed_tick_has_production_time() {
        let boundary_one = integer_matrix(&[&[-1, 0, 1], &[1, -1, 0], &[0, 1, -1]]).unwrap();
        let boundary_two = integer_matrix(&[&[1], &[1], &[1]]).unwrap();
        let triangle = FiniteComplex::new(
            CellComplex::new(vec![3, 3, 1], vec![boundary_one, boundary_two]).unwrap(),
            vec![(0, vec![Step::along(0), Step::along(1), Step::along(2)])],
        )
        .unwrap();
        let tick = Form::new(ints(&[1, 0, 0]));
        let split = hodge_split(&triangle, &[unit(3), unit(3), unit(1)], &tick).unwrap();
        assert_eq!(
            split.state,
            Form::new(vec![rat(2, 3), rat(-1, 3), rat(-1, 3)])
        );
        assert_eq!(split.production, Form::new(vec![rat(1, 3); 3]));
        assert!(is_zero(split.winding.values()));
        let loop_aeon = Aeon::rest(0).with_cell(&triangle, 0, &0, true).unwrap();
        assert_eq!(split.production.read(&loop_aeon).unwrap(), integer(1));
    }

    /// [counterexample] **Winding time is not boundary-determined.** On the hollow triangle the
    /// harmonic form `(1,1,1)` reads `3` on the loop and `0` on rest, and both have no boundary.
    /// Lean `HodgeTime.HollowTriangle.hollowTriangle_winding_not_boundary_determined`.
    #[test]
    fn winding_time_is_not_boundary_determined() {
        let hollow = FiniteComplex::graph(3, &[0, 1, 2], &[1, 2, 0]).unwrap();
        let loop_form = Form::new(ints(&[1, 1, 1]));
        let split = hodge_split(&hollow, &[unit(3), unit(3)], &loop_form).unwrap();
        assert_eq!(split.winding, loop_form);
        let loop_aeon = Aeon::new(
            &hollow,
            0,
            vec![Step::along(0), Step::along(1), Step::along(2)],
        )
        .unwrap();
        assert_eq!(loop_aeon.start(), loop_aeon.end());
        assert_eq!(split.winding.read(&loop_aeon).unwrap(), integer(3));
        assert!(split.winding.read(&Aeon::rest(0)).unwrap().is_zero());
    }
}
