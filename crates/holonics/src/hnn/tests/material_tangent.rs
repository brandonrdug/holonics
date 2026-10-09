//! The contact material's forward tangent (Refs #73 #62; the held-carry record §2 (e), §3).
//!
//! On 0279's field and constitution, with one contact's factors declared as a test chart, the
//! tangent `χ` carried beside an exact Word along one factor direction `H` is checked against the
//! Word itself run at `θ ± εH`: the passage is a rational function of `ε`, so the central residual
//! `(x(ε) − x(−ε))/2ε − χ` is `O(ε²)`. That is read as exact inequalities on the dyadic ladder
//! `ε = 2⁻ʲ`, never a decimal tolerance. A wrong or missing material forcing leaves the residual
//! at `O(1)`, and the ladder fails. The crossing into the next opening (eq. 3) is checked the same
//! way against the next Word's actual opening change.

use std::sync::Arc;

use num_traits::{Signed, Zero};

use super::support::{contact, encoded, ring};
use crate::compression::landmark::context::{BaseMeasure, StopPrior};
use crate::hnn::constitution::{Constitution, Locus};
use crate::hnn::field::{CribDeclaration, Current, Field, FieldDeclaration, ReceiverDeclaration};
use crate::hnn::moment::SourceMoment;
use crate::hnn::prediction::DamagedSection;
use crate::hnn::receiving::ReceivingPhases;
use crate::hnn::word::continuation::{MaterialDirection, MaterialTangent};
use crate::hnn::word::{Absorption, EndChange, Word, WordOpening};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer, rat};

// 0279's own fixture (`tests/finite_decrease.rs`), declared before any observation.

fn receiver() -> ReceiverDeclaration {
    ReceiverDeclaration {
        ring: 0,
        aperture: 3,
        tolerance: rat(1, 16),
        depth: 1,
        prior: StopPrior::half(),
        mass: 1,
        base: BaseMeasure::Even,
        receiving_prior: 0,
    }
}

fn field() -> Field {
    Field::declare(
        FieldDeclaration {
            rings: vec![ring(4, (0..4).collect()), ring(3, Vec::new())],
            contacts: vec![contact(0, 1, 3, 0)],
            loops: Vec::new(),
            sources: vec![0],
            offsets: Vec::new(),
            alphabet: 4,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![receiver()],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 16,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .unwrap()
}

fn material(field: &Field) -> Constitution {
    let reads = crate::hnn::retention::loci(field).into_iter().collect();
    super::learning::generic(field, 81)
        .rebased(Locus::Channel(0), 7, &reads)
        .unwrap()
}

/// 0279's exact Word on `theta` (source `[0, 1]`) opened on `opening` and left unrun, with its
/// junction steps.
fn unrun<'f>(
    field: &'f Field,
    theta: &Constitution,
    current: &Current,
    opening: &WordOpening,
) -> (Word<'f>, usize) {
    let declared = receiver();
    let chart = encoded(field, &[0, 1]);
    let section =
        DamagedSection::of_runs(declared.aperture, &chart, vec![(0, chart.clone())]).unwrap();
    let phases = ReceivingPhases::declare(field, theta, current, &declared).unwrap();
    section.admit(field, theta, &phases).unwrap();
    let mut moment = SourceMoment::open_with(field, current, theta).unwrap();
    for &g in field.sources() {
        moment = moment
            .station_section(field, current, g, &section.placed())
            .unwrap();
    }
    let (word, _) =
        Word::open_source_exact_received(field, theta, current, Arc::new(moment), opening).unwrap();
    (word, phases.junction_steps())
}

/// A `rows × rows` test-chart factor with exact entries `diagonal(i)` on the diagonal and
/// `upper` just above it.
fn factor(rows: usize, diagonal: impl Fn(usize) -> Rat, upper: Rat) -> ExactRatMatrix {
    ExactRatMatrix::new(
        (0..rows)
            .map(|i| {
                (0..rows)
                    .map(|j| {
                        if i == j {
                            diagonal(i)
                        } else if j == i + 1 {
                            upper.clone()
                        } else {
                            Rat::zero()
                        }
                    })
                    .collect()
            })
            .collect(),
    )
    .unwrap()
}

fn plus(a: &ExactRatMatrix, b: &ExactRatMatrix, s: &Rat) -> ExactRatMatrix {
    ExactRatMatrix::new(
        (0..a.rows())
            .map(|i| {
                (0..a.columns())
                    .map(|j| a.get(i, j).unwrap() + s * b.get(i, j).unwrap())
                    .collect()
            })
            .collect(),
    )
    .unwrap()
}

/// The declared material at `θ + εH` on contact 0's storage factor.
struct Declared {
    base: Constitution,
    storage: ExactRatMatrix,
    stiffness: ExactRatMatrix,
    dissipation: ExactRatMatrix,
    direction: ExactRatMatrix,
}

impl Declared {
    fn at(&self, epsilon: &Rat) -> Constitution {
        self.base
            .clone()
            .with_channel(
                0,
                plus(&self.storage, &self.direction, epsilon),
                self.stiffness.clone(),
                self.dissipation.clone(),
            )
            .unwrap()
    }
}

fn declared(field: &Field, current: &Current) -> Declared {
    let base = material(field);
    let (word, _) = unrun(field, &base, current, &WordOpening::Rest);
    let width = word.operands().contacts()[0].width();
    drop(word);
    Declared {
        base,
        storage: factor(width, |i| rat(2 + i as i64, 3), rat(1, 4)),
        stiffness: factor(width, |i| rat(1, 2 + i as i64), rat(1, 8)),
        dissipation: factor(width, |_| rat(1, 3), Rat::zero()),
        direction: factor(
            width,
            |i| if i == 0 { integer(1) } else { Rat::zero() },
            rat(1, 2),
        ),
    }
}

/// The storage form `C` of contact 0 that a Word on `theta` executes.
fn storage_form(field: &Field, theta: &Constitution, current: &Current) -> ExactRatMatrix {
    let (word, _) = unrun(field, theta, current, &WordOpening::Rest);
    word.operands().contacts()[0].forms().0.clone()
}

/// Every coordinate of a change, in one order.
fn flat(change: &EndChange) -> Vec<Rat> {
    let mut out = Vec::new();
    for wave in &change.storage {
        out.extend(wave.iter().cloned());
    }
    for [g, h] in &change.arrivals {
        out.extend(g.iter().cloned());
        out.extend(h.iter().cloned());
    }
    for [u, w] in &change.states {
        out.extend(u.iter().cloned());
        out.extend(w.iter().cloned());
    }
    for state in change.resonators.iter().flatten() {
        out.extend(state[0].iter().cloned());
        out.extend(state[1].iter().cloned());
    }
    out
}

fn l1(v: &[Rat]) -> Rat {
    v.iter().map(|x| x.abs()).sum()
}

/// The central residual's L1 norm, `‖(x(ε) − x(−ε))/2ε − χ‖₁`.
fn central(up: &[Rat], down: &[Rat], epsilon: &Rat, tangent: &[Rat]) -> Rat {
    let two_epsilon = integer(2) * epsilon;
    l1(&up
        .iter()
        .zip(down)
        .zip(tangent)
        .map(|((a, b), t)| (a - b) / &two_epsilon - t)
        .collect::<Vec<_>>())
}

/// The ladder's law: on `ε_j = 2⁻ʲ` an `O(ε²)` residual `r_j` satisfies `r_(j+1) ≤ r_j / 2` once
/// the expansion holds, and its scaled reading `4ʲ r_j` stays within twice the first one's.
fn second_order(residuals: &[(Rat, Rat)]) {
    let (first_epsilon, first) = &residuals[0];
    let scaled_first = first / (first_epsilon * first_epsilon);
    for pair in residuals.windows(2) {
        let ((_, r0), (_, r1)) = (&pair[0], &pair[1]);
        assert!(
            r1 * integer(2) <= *r0,
            "the central residual halves at least along the ladder: {r0} then {r1}"
        );
    }
    for (epsilon, residual) in residuals {
        assert!(
            residual / (epsilon * epsilon) <= &scaled_first * integer(2),
            "the central residual stays O(ε²): {residual} at ε = {epsilon}"
        );
    }
}

/// **(e), within one Word: the tangent is the passage's exact derivative.** The declared storage
/// direction's form derivative is read from the Words' own executed forms (`C(ε) − C(−ε)` over
/// `2ε`, exact for the quadratic `c cᵀ`). The tangent follows every full tick of the Word on `θ`,
/// and it is compared with the same Word run on `θ ± εH`.
#[test]
fn the_material_tangent_is_the_exact_derivative_of_its_passage() {
    let field = field();
    let current = Current::at_rest(&field);
    let declared = declared(&field, &current);
    let theta = declared.at(&Rat::zero());
    let one = Rat::from_integer(1.into());
    let delta_storage = plus(
        &storage_form(&field, &declared.at(&one), &current),
        &storage_form(&field, &declared.at(&-one.clone()), &current),
        &-one.clone(),
    );
    let delta_storage = plus(&delta_storage, &delta_storage, &-rat(1, 2));
    let direction = MaterialDirection {
        contact: 0,
        storage: Some(delta_storage),
        stiffness: None,
        dissipation: None,
    };

    let (mut word, steps) = unrun(&field, &theta, &current, &WordOpening::Rest);
    let mut tangent = MaterialTangent::held_opening(&word, theta.commit(), direction).unwrap();
    for _ in 0..steps {
        word.tick().unwrap();
        tangent.step(&word).unwrap();
    }
    let chi = flat(tangent.tangent());
    assert!(
        chi.iter().any(|x| !x.is_zero()),
        "the direction moves the passage"
    );

    let run = |epsilon: &Rat| {
        let (mut word, steps) = unrun(&field, &declared.at(epsilon), &current, &WordOpening::Rest);
        word.run(steps).unwrap();
        flat(&word.change().unwrap())
    };
    let residuals: Vec<(Rat, Rat)> = (4..9)
        .map(|j| {
            let epsilon = rat(1, 1i64 << j);
            let r = central(&run(&epsilon), &run(&-epsilon.clone()), &epsilon, &chi);
            println!("material tangent: ε = 2^-{j}: central residual {r}");
            (epsilon, r)
        })
        .collect();
    second_order(&residuals);
}

/// **(e), across the passage boundary: the crossing is eq. (3).** The tangent of the first Word's
/// carry, crossed by [`MaterialTangent::opened`], equals the derivative of the next Word's actual
/// opening change on the same material (opened on that carry with nothing absorbed), to `O(ε²)`
/// on the ladder. The same-`C` crossing keeps `χ_w`; a crossing that held the recorded momentum
/// parameter-constant would leave an `O(1)` residual here.
#[test]
fn the_material_tangent_crosses_into_the_next_opening() {
    let field = field();
    let current = Current::at_rest(&field);
    let declared = declared(&field, &current);
    let theta = declared.at(&Rat::zero());
    let one = Rat::from_integer(1.into());
    let delta_storage = plus(
        &storage_form(&field, &declared.at(&one), &current),
        &storage_form(&field, &declared.at(&-one.clone()), &current),
        &-one.clone(),
    );
    let delta_storage = plus(&delta_storage, &delta_storage, &-rat(1, 2));
    let direction = MaterialDirection {
        contact: 0,
        storage: Some(delta_storage),
        stiffness: None,
        dissipation: None,
    };

    let (mut word, steps) = unrun(&field, &theta, &current, &WordOpening::Rest);
    let mut tangent = MaterialTangent::held_opening(&word, theta.commit(), direction).unwrap();
    for _ in 0..steps {
        word.tick().unwrap();
        tangent.step(&word).unwrap();
    }
    let carry = word.reception_end().unwrap();
    let opening = WordOpening::Received {
        carry: carry.clone(),
        absorption: Absorption::Nothing,
    };
    let (second, _) = unrun(&field, &theta, &current, &opening);
    let conductances: Vec<Rat> = second
        .operands()
        .contacts()
        .iter()
        .map(|c| c.conductance().clone())
        .collect();
    drop(second);
    let opened = flat(&tangent.opened(&carry, &conductances, &field).unwrap());
    assert!(
        opened.iter().any(|x| !x.is_zero()),
        "the tangent survives the crossing"
    );

    let next_opening = |epsilon: &Rat| {
        let theta = declared.at(epsilon);
        let (mut first, steps) = unrun(&field, &theta, &current, &WordOpening::Rest);
        first.run(steps).unwrap();
        let opening = WordOpening::Received {
            carry: first.reception_end().unwrap(),
            absorption: Absorption::Nothing,
        };
        let (second, _) = unrun(&field, &theta, &current, &opening);
        flat(&second.change().unwrap())
    };
    let residuals: Vec<(Rat, Rat)> = (4..9)
        .map(|j| {
            let epsilon = rat(1, 1i64 << j);
            let r = central(
                &next_opening(&epsilon),
                &next_opening(&-epsilon.clone()),
                &epsilon,
                &opened,
            );
            println!("material tangent crossing: ε = 2^-{j}: central residual {r}");
            (epsilon, r)
        })
        .collect();
    second_order(&residuals);
}
