//! Non-closed clocks: Sagnac and the gravitational redshift as production time on a cycle.

use num_traits::{One, Zero};

use crate::aeon::{Aeon, ClosedForm, FiniteComplex, Form, Step, hodge_split, rate};
use crate::geometry::complex::CellComplex;
use crate::ratio::linear::inertia::SymmetricForm;
use crate::ratio::linear::vector::matrix;
use crate::ratio::{Presentation, Rat};

use super::SpacetimeError;

/// The passages' sources and targets on the square `0 → 1 → 2 → 3 → 0`.
const SOURCES: [usize; 4] = [0, 1, 2, 3];
const TARGETS: [usize; 4] = [1, 2, 3, 0];

/// [definition] **The oriented square with its face** (Lean `NonClosedClock.square`): four
/// occurrences, the passages `0 → 1 → 2 → 3 → 0`, and one two-cell whose boundary word is the loop.
pub fn square_complex() -> Result<FiniteComplex, SpacetimeError> {
    // `∂₁`: occurrences × passages, `−1` at each passage's source and `+1` at its target.
    let boundary_one = matrix(4, 4, |occurrence, passage| {
        if occurrence == SOURCES[passage] {
            -Rat::one()
        } else if occurrence == TARGETS[passage] {
            Rat::one()
        } else {
            Rat::zero()
        }
    })?;
    // `∂₂`: the face's boundary is the loop through all four passages.
    let boundary_two = matrix(4, 1, |_, _| Rat::one())?;
    Ok(FiniteComplex::new(
        CellComplex::new(vec![4, 4, 1], vec![boundary_one, boundary_two])?,
        vec![(0, (0..4).map(Step::along).collect())],
    )?)
}

/// [definition] **A clock rotating at `Ω`** (with `1/c²` absorbed) on the quadrilateral with the
/// given corners: each straight passage `s → t` desynchronizes by `Ω(x_s y_t − x_t y_s)` (Lean
/// `sagnacForm`). First order in `Ω`.
pub fn sagnac_clock(omega: &Rat, corners: &[(Rat, Rat); 4]) -> Form {
    Form::new(
        (0..4)
            .map(|e| {
                let (xs, ys) = &corners[SOURCES[e]];
                let (xt, yt) = &corners[TARGETS[e]];
                omega * (xs * yt - xt * ys)
            })
            .collect(),
    )
}

/// [definition] **A static clock** `ω = N dt` on the `(t, x)` rectangle
/// `(t₀, x₁), (t₁, x₁), (t₁, x₂), (t₀, x₂)`: the time passages read `N₁Δt` and `−N₂Δt`, the space
/// passages nothing (Lean `staticForm`).
pub fn static_clock(near_lapse: &Rat, far_lapse: &Rat, coordinate_tick: &Rat) -> Form {
    Form::new(vec![
        near_lapse * coordinate_tick,
        Rat::zero(),
        -(far_lapse * coordinate_tick),
        Rat::zero(),
    ])
}

/// [definition] **A clock read on the square's cycle**: its reading of the loop, its curvature
/// through the face, the production part of its Hodge split and that part's reading of the loop,
/// and whether it is a clock (closed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CycleReading {
    pub loop_reading: Rat,
    pub curvature: Vec<Rat>,
    pub production: Form,
    pub production_reading: Rat,
    pub is_clock: bool,
}

/// [proved-derived; implemented-exact] **A clock read on a cycle that bounds a cell** (Lean
/// `sagnac_reading`, `sagnac_is_curvature_flux`, `sagnac_is_production`, `static_reading`,
/// `static_is_production`, `inertial_clock_silent`): the loop reads the curvature flux, only the
/// production part of the Hodge split (unit metrics) reads it, and the form is a clock exactly when
/// both vanish. The loop is built by the face move from rest ([`Aeon::with_cell`]).
pub fn read_on_cycle(complex: &FiniteComplex, form: &Form) -> Result<CycleReading, SpacetimeError> {
    let loop_aeon = Aeon::rest(0).with_cell(complex, 0, &0, true)?;
    let cells = complex.cell_complex();
    let metrics: Vec<SymmetricForm> = (0..=cells.dimension())
        .map(|degree| {
            let extent = cells.cells(degree);
            SymmetricForm::from_rows(
                (0..extent)
                    .map(|i| {
                        (0..extent)
                            .map(|j| if i == j { Rat::one() } else { Rat::zero() })
                            .collect()
                    })
                    .collect(),
            )
        })
        .collect::<Result<_, _>>()
        .map_err(crate::holon::HolonError::from)?;
    let split = hodge_split(complex, &metrics, form)?;
    Ok(CycleReading {
        loop_reading: form.read(&loop_aeon)?,
        curvature: form.curvature(complex)?,
        production_reading: split.production.read(&loop_aeon)?,
        production: split.production,
        is_clock: ClosedForm::new(complex, form.clone()).is_ok(),
    })
}

/// [proved-derived; implemented-exact] **The redshift is the owner's rate of two static clocks**
/// (Lean `redshift_rate`). The static receiver at `x₁` reads the coordinate interval as passage `0`
/// of the static form, the one at `x₂` as its reversed passage `2`; as clocks on the one-passage
/// complex, the owner's [`rate`] of the two on the passage is the undivided pair `(N₁Δt : N₂Δt)`,
/// projectively the lapse ratio `(N₁ : N₂)`. The undetermined `(0 : 0)`, a zero interval or two
/// zero lapses, is refused by the owner (`AeonError::Undetermined`).
pub fn redshift_rate(
    near_lapse: &Rat,
    far_lapse: &Rat,
    coordinate_tick: &Rat,
) -> Result<Presentation, SpacetimeError> {
    let form = static_clock(near_lapse, far_lapse, coordinate_tick);
    let passage = FiniteComplex::graph(2, &[0], &[1])?;
    let aeon = Aeon::new(&passage, 0, vec![Step::along(0)])?;
    let near = ClosedForm::new(&passage, Form::new(vec![form.values()[0].clone()]))?;
    let far = ClosedForm::new(&passage, Form::new(vec![-form.values()[2].clone()]))?;
    Ok(rate(&near, &far, &aeon)?)
}
