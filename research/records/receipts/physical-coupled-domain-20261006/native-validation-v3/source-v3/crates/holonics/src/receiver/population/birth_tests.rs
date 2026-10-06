//! The founding law checked exactly on the smallest fixtures that exhibit it: the closure of a
//! ring's polarized sheet is its Krylov space with `E T = U E` and `D E = ρ`; the strict-step bound
//! `d − dim V₀` is attained by a shift; two noncommuting transports intertwine together; each
//! refusal; the reached covector of a comparison; the founded family on a coprime moiré codes at its
//! truth with the founded dimension its emission's Hankel rank; and the section's founding in a
//! population.

use super::birth::{BirthError, Closure, SectionFounding, TransportBirth};
use super::tests::Fixed;
use super::*;
use crate::holarchy::terrain::{Grating, Moire, MoireClass};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::rat;

fn ints(values: &[i64]) -> Vec<Rat> {
    values.iter().map(|&v| rat(v, 1)).collect()
}

fn matrix(rows: &[&[i64]]) -> ExactRatMatrix {
    ExactRatMatrix::new(rows.iter().map(|row| ints(row)).collect()).unwrap()
}

/// The rotation `e_s ↦ e_(s+1)` of `ℤ/4`: column `s` holds its one at row `s + 1`.
fn rotation(q: usize) -> ExactRatMatrix {
    let mut rows = vec![vec![rat(0, 1); q]; q];
    for s in 0..q {
        rows[(s + 1) % q][s] = rat(1, 1);
    }
    ExactRatMatrix::new(rows).unwrap()
}

/// **A ring's polarized sheet founds its Krylov space.** On `ℤ/4` turning one port a tick, the
/// sheet `[0, 0, 1, 1]` polarized is `λ = [−1, −1, 1, 1]`; with the mass form held, `T*λ = [−1, 1,
/// 1, −1]` opens one rung and `T*²λ = −λ` closes it: `dim V = 3 = q/2 + 1`, one strict step, `U` the
/// companion of `x² + 1` beside the fixed mass form, and `E T = U E`, `D E = ρ` exactly.
#[test]
fn a_rings_polarized_sheet_founds_its_krylov_space() {
    let t = rotation(4);
    let closure = Closure::found(
        4,
        &[t.clone()],
        &[ints(&[1, 1, 1, 1])],
        &ints(&[-1, -1, 1, 1]),
    )
    .unwrap();
    assert_eq!(closure.dimension(), 3);
    assert_eq!(closure.held(), 1);
    assert_eq!(closure.rungs(), &[2, 3]);
    assert_eq!(closure.strict_steps(), 1);
    assert_eq!(closure.forms()[2], ints(&[-1, 1, 1, -1]));
    assert_eq!(
        closure.transport(0).unwrap(),
        matrix(&[&[1, 0, 0], &[0, 0, 1], &[0, -1, 0]])
    );
    closure.check(&[t.clone()]).unwrap();
    // E T x = U E x on every state.
    let u = closure.transport(0).unwrap();
    for s in 0..4 {
        let mut x = vec![rat(0, 1); 4];
        x[s] = rat(1, 1);
        let moved = t.apply(&x).unwrap();
        assert_eq!(
            closure.encode(&moved).unwrap(),
            u.apply(&closure.encode(&x).unwrap()).unwrap()
        );
    }
    // D E = ρ: ρ_1 = (1 + λ)/2, ρ_0 = (1 − λ)/2.
    let d = closure
        .readout(&[ints(&[1, 1, 0, 0]), ints(&[0, 0, 1, 1])])
        .unwrap();
    assert_eq!(
        d.to_rows(),
        vec![
            vec![rat(1, 2), rat(-1, 2), rat(0, 1)],
            vec![rat(1, 2), rat(1, 2), rat(0, 1)]
        ]
    );
}

/// **The bound `d − dim V₀` is attained** (Lean `strict_steps_le_chart`; `Compression/Core/FaceMap`'s
/// `Shift.horizon_sharp` dualized): the shift `(a, b, c) ↦ (b, c, 0)` read at `a` founds `e₀*`,
/// `e₁*`, `e₂*` over two strict steps, and `T*e₂* = 0` closes it.
#[test]
fn the_strict_step_bound_is_attained_by_a_shift() {
    let shift = matrix(&[&[0, 1, 0], &[0, 0, 1], &[0, 0, 0]]);
    let closure = Closure::found(3, &[shift.clone()], &[], &ints(&[1, 0, 0])).unwrap();
    assert_eq!(closure.rungs(), &[1, 2, 3]);
    assert_eq!(closure.strict_steps(), 2);
    assert_eq!(closure.dimension(), 3);
    closure.check(&[shift]).unwrap();
}

/// **Two noncommuting transports intertwine together**: the rotation of `ℤ/3` and the swap of its
/// first two ports, closed from `e₀*`, found all of `ℚ³` in one strict step with `E T_a = U_a E`
/// for both.
#[test]
fn two_noncommuting_transports_intertwine_together() {
    let turn = rotation(3);
    let swap = matrix(&[&[0, 1, 0], &[1, 0, 0], &[0, 0, 1]]);
    assert_ne!(turn.multiply(&swap).unwrap(), swap.multiply(&turn).unwrap());
    let closure = Closure::found(3, &[turn.clone(), swap.clone()], &[], &ints(&[1, 0, 0])).unwrap();
    assert_eq!(closure.dimension(), 3);
    assert_eq!(closure.rungs(), &[1, 3]);
    closure.check(&[turn, swap]).unwrap();
}

/// **Each refusal is typed**: a chart of no dimension or a covector off it; no transport, or one
/// that is not a map of the chart; a covector in the span of the forms held; a reading outside the
/// founded forms.
#[test]
fn a_founding_refuses_what_the_law_does_not_admit() {
    let t = rotation(4);
    assert!(matches!(
        Closure::found(0, &[t.clone()], &[], &[]),
        Err(BirthError::ChartNotFinite { .. })
    ));
    assert!(matches!(
        Closure::found(4, &[t.clone()], &[], &ints(&[1, 0, 0])),
        Err(BirthError::ChartNotFinite { .. })
    ));
    assert!(matches!(
        Closure::found(4, &[], &[], &ints(&[1, 0, 0, 0])),
        Err(BirthError::TransportUndeclared { .. })
    ));
    assert!(matches!(
        Closure::found(4, &[rotation(3)], &[], &ints(&[1, 0, 0, 0])),
        Err(BirthError::TransportUndeclared { .. })
    ));
    assert_eq!(
        Closure::found(
            4,
            &[t.clone()],
            &[ints(&[1, 1, 1, 1])],
            &ints(&[2, 2, 2, 2])
        ),
        Err(BirthError::NotSeparating)
    );
    // The sheet's closure does not hold the reading of one port.
    let closure = Closure::found(4, &[t], &[ints(&[1, 1, 1, 1])], &ints(&[-1, -1, 1, 1])).unwrap();
    assert!(matches!(
        closure.readout(&[ints(&[1, 0, 0, 0])]),
        Err(BirthError::ReadingOutside { class: 0 })
    ));
}

/// **The comparison reaches through the coupling's adjoint**: on a binary alphabet `κ = e_y − q`
/// pulls back to `q_(y′)(ρ_y − ρ_(y′))`, the polarized reading scaled by the surprise mass.
#[test]
fn the_comparison_reaches_as_the_polarized_reading() {
    let birth = TransportBirth::moire(&[(1, 4)], MoireClass::Parity, 2).unwrap();
    let reached = birth.reached(&[rat(-1, 4), rat(1, 4)]).unwrap();
    assert_eq!(reached, vec![rat(-1, 4), rat(-1, 4), rat(1, 4), rat(1, 4)]);
    assert!(matches!(
        birth.reached(&[rat(1, 1)]),
        Err(BirthError::Comparison { .. })
    ));
}

/// The Hankel rank of a periodic word: the rank of `[w_((i+j) mod L)]_(i,j<L)`.
fn hankel_rank(word: &[usize]) -> usize {
    let l = word.len();
    let rows = (0..l)
        .map(|i| (0..l).map(|j| rat(word[(i + j) % l] as i64, 1)).collect())
        .collect();
    ExactRatMatrix::new(rows).unwrap().rank().unwrap()
}

/// **The founded family codes a coprime moiré at its truth.** Rings `1/3` and `1/4` read by their
/// parity color: the joint torus `ℤ/3 × ℤ/4` is one orbit, so the founded dimension is the
/// emission's Hankel rank, and survivor filtering in the founded chart keeps exactly the phases the
/// terrain's own emission leaves (its code `log₂ 12 − log₂ #S`).
#[test]
fn the_founded_family_codes_a_coprime_moire_at_its_truth() {
    let birth = TransportBirth::moire(&[(1, 3), (1, 4)], MoireClass::Parity, 2).unwrap();
    let founded = birth
        .found(&birth.reached(&[rat(-1, 1), rat(1, 1)]).unwrap())
        .unwrap();
    let moire = Moire::new(
        vec![
            Grating::new(1, 3, 2).unwrap(),
            Grating::new(1, 4, 1).unwrap(),
        ],
        MoireClass::Parity,
    )
    .unwrap();
    let cells = moire.emit(24);
    assert_eq!(founded.closure.dimension(), hankel_rank(&cells[..12]));
    assert!(founded.closure.strict_steps() + 2 <= 12);
    let mut family = founded.family;
    for &cell in &cells {
        assert!(!family.receive(cell).unwrap().is_zero());
    }
    // The truth: the phases whose emission is the passage.
    let fibre = (0..3u64)
        .flat_map(|a| (0..4u64).map(move |b| (a, b)))
        .filter(|&(a, b)| {
            let candidate = Moire::new(
                vec![
                    Grating::new(1, 3, a).unwrap(),
                    Grating::new(1, 4, b).unwrap(),
                ],
                MoireClass::Parity,
            )
            .unwrap();
            candidate.emit(24) == cells
        })
        .count() as u64;
    assert_eq!(family.count(), fibre);
    assert_eq!(
        family.likelihood(),
        Likelihood::Exact(Rat::new(fibre.into(), 12u64.into()))
    );
    assert!(family.work().of(Act::Transport) > 0);
}

/// **The section's founding in a population**: a flat family pays a bit a cell, so the second
/// section's residual passes the founding's two bits; the family founded there from the comparison
/// is born from the reserved mass, and the population codes the rest of the passage within the
/// newborn's charge of its truth. A non-binary coupling is refused.
#[test]
fn the_section_founds_from_the_residual_and_the_population_codes_at_the_truth() {
    let birth = TransportBirth::moire(&[(1, 3), (1, 4)], MoireClass::Parity, 2).unwrap();
    let mut section = SectionFounding::new(birth, 4).unwrap();
    let mut population =
        Population::new(vec![Box::new(Fixed::new(vec![rat(1, 2), rat(1, 2)], 1))]).unwrap();
    let moire = Moire::new(
        vec![
            Grating::new(1, 3, 2).unwrap(),
            Grating::new(1, 4, 1).unwrap(),
        ],
        MoireClass::Parity,
    )
    .unwrap();
    let cells = moire.emit(36);
    let mut at_birth = None;
    for &cell in &cells {
        section.receive(&mut population, cell).unwrap();
        if at_birth.is_none() && section.receipt().is_some() {
            at_birth = Some(population.code().unwrap());
        }
    }
    let receipt = section.receipt().unwrap().clone();
    assert_eq!(receipt.birth.cell, 8);
    assert_eq!(receipt.birth.mass, rat(1, 4));
    assert_eq!(receipt.chart, 12);
    // The newborn codes the rest at its truth: every phase of the torus but those the cells after
    // the birth exclude.
    let newborn = population.receipt().unwrap().families[1].clone();
    let founded_code = newborn.code.unwrap();
    let after = &cells[8..];
    let fibre = (0..12u64)
        .filter(|&state| {
            let (a, b) = (state % 3, state / 3);
            let candidate = Moire::new(
                vec![
                    Grating::new(1, 3, a).unwrap(),
                    Grating::new(1, 4, b).unwrap(),
                ],
                MoireClass::Parity,
            )
            .unwrap();
            candidate.emit(after.len()) == after
        })
        .count() as u64;
    let truth =
        crate::compression::landmark::context::ratio_code_length(&fibre.into(), &12u64.into())
            .unwrap();
    assert_eq!(founded_code, truth);
    // −log₂ W_n ≤ −log₂ W_(t_g) + charge + truth, the charge −log₂(m_g/M_n) = −log₂((1/4)/(3/4)).
    let charge =
        crate::compression::landmark::context::ratio_code_length(&1u64.into(), &3u64.into())
            .unwrap();
    let code = population.code().unwrap();
    let before = at_birth.unwrap();
    assert!(code.lower <= &(&before.upper + &charge.upper) + &truth.upper);
    let wide = TransportBirth::moire(&[(1, 3), (1, 4)], MoireClass::Sheets, 2).unwrap();
    assert!(matches!(
        SectionFounding::new(wide, 4),
        Err(BirthError::Comparison { .. })
    ));
}
