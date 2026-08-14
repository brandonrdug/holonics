//! **What `congruence` refuses, returned as a bound: `n₊(PᵀAP) ≤ n₊(A)` for any `P` whatever.**
//!
//! ```text
//! cargo run --release --example the_pullback_bounds_the_inertia
//! ```
//!
//! `research/records/2026-08-11_THE_RUNG_REFUSES_BY_NAME_AND_THE_UNRESOLVED_PAIR_IS_THE_REMAINDER.md`
//! §5.3 records that `inertia::congruence` *"refuses where the finite core of §1 lives"*: it returns
//! `SingularChangeOfBasis` for a singular change of basis, where the lawful return is the pull-back
//! bound with rank and kernel testimony. Two models converged on the construction independently —
//! one from restriction of forms, one from the finite core of the external kernel-verified zeta
//! certificate — including the same strict control.
//!
//! The bound holds for every `P`, invertible or not, and the argument is one line: a subspace on
//! which `PᵀAP` is positive definite maps forward under `P` to a subspace on which `A` is positive
//! definite, so `n₊(A)` is at least as large. `congruence` is the equality case and is subsumed.
//!
//! # The three controls, and what each would take to break
//!
//! 1. **The collapse witness the module's own doc already carried.** `[[1,1],[1,1]]` against
//!    `diag(1,−1)` gives the zero form. It must return **strict** inequality on both sides, with the
//!    collapsed direction exhibited — never the refusal.
//! 2. **The tightness fixture.** On a declared block structure the rank–trace equality
//!    `2c·tr(M) − ‖M‖²_F = Σⱼ k_c(mⱼ) + c²·b` holds exactly over `Rat`, with `k_c(m) = 2cm − m²`.
//!    The fixture carries a **negative** level so the identity is not resting on positive
//!    semidefiniteness, a nonzero `b` so the `c²·b` term carries, and directions at rest.
//! 3. **Invertible `P` reproduces `congruence` exactly.** Sylvester's law as the saturated case,
//!    over the same fixtures the congruence test already uses.
//!
//! And one negative control, because a bound that is always strict is not a bound: an injective
//! restriction tightens one side with an **empty** kernel, so strictness and collapse are separated
//! rather than conflated.
//!
//! # What this does not establish
//!
//! Nothing here proves, approaches, or schedules any Millennium problem. The rank–trace identity is
//! elementary arithmetic over `ℚ`; its identification with the external artifact's own `k_c` is
//! `interpretation` read from the record's restatement, not from the Lean source.

use num_bigint::BigInt;
use num_traits::Zero;
use relational_geometry::Rat;

use holonic_engine::exact_linear::ExactRatMatrix;
use holonic_engine::inertia::{
    InertiaError, PullbackInertia, SymmetricForm, block_defect, congruence, inertia,
    pullback_inertia_bound, rank_trace_defect,
};

fn rat(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn integers(rows: &[Vec<i64>]) -> SymmetricForm {
    SymmetricForm::from_integers(rows).expect("fixture is square and symmetric")
}

fn matrix(rows: &[Vec<i64>]) -> ExactRatMatrix {
    ExactRatMatrix::new(
        rows.iter()
            .map(|row| row.iter().map(|entry| rat(*entry)).collect())
            .collect(),
    )
    .expect("fixture is rectangular")
}

fn fractional(rows: &[Vec<(i64, i64)>]) -> ExactRatMatrix {
    ExactRatMatrix::new(
        rows.iter()
            .map(|row| {
                row.iter()
                    .map(|(numerator, denominator)| {
                        Rat::new(BigInt::from(*numerator), BigInt::from(*denominator))
                    })
                    .collect()
            })
            .collect(),
    )
    .expect("fixture is rectangular")
}

/// `E10 = U ⊕ E8(−1)`, signature `(1, 9)`: the Néron–Severi lattice of a rational elliptic surface,
/// and the fixture the zero-diagonal branch of the elimination exists for.
fn e10() -> SymmetricForm {
    let hyperbolic = integers(&[vec![0, 1], vec![1, 0]]);
    let e8 = integers(&[
        vec![2, 0, -1, 0, 0, 0, 0, 0],
        vec![0, 2, 0, -1, 0, 0, 0, 0],
        vec![-1, 0, 2, -1, 0, 0, 0, 0],
        vec![0, -1, -1, 2, -1, 0, 0, 0],
        vec![0, 0, 0, -1, 2, -1, 0, 0],
        vec![0, 0, 0, 0, -1, 2, -1, 0],
        vec![0, 0, 0, 0, 0, -1, 2, -1],
        vec![0, 0, 0, 0, 0, 0, -1, 2],
    ]);
    hyperbolic.direct_sum(&e8.negated())
}

fn report(label: &str, pullback: &PullbackInertia) {
    println!(
        "  {label:<34} source ({}, {}, {})  pulled ({}, {}, {})  rank P {}  ker {}",
        pullback.source.positive,
        pullback.source.zero,
        pullback.source.negative,
        pullback.pulled_back.positive,
        pullback.pulled_back.zero,
        pullback.pulled_back.negative,
        pullback.basis_rank,
        pullback.collapsed_extent()
    );
    println!(
        "  {:<34} bounds hold {}   strict +{} -{}   rank lost {}",
        "",
        pullback.bounds_hold(),
        pullback.positive_is_strict(),
        pullback.negative_is_strict(),
        pullback.rank_lost()
    );
}

fn main() {
    println!("== the pull-back bound, exact over Rat ==");

    // ---------------------------------------------------------------------------------------
    println!();
    println!("-- control 1: the collapse witness --");
    let indefinite = SymmetricForm::from_diagonal(vec![rat(1), rat(-1)]);
    let collapsing = matrix(&[vec![1, 1], vec![1, 1]]);
    match congruence(&indefinite, &collapsing) {
        Err(InertiaError::SingularChangeOfBasis) => {
            println!("  congruence(diag(1,-1), [[1,1],[1,1]]) REFUSED: singular change of basis");
            println!("  and that refusal is correct: Sylvester's law is about invertible maps.");
        }
        other => println!("  congruence returned {other:?}, which is not the refusal it owes"),
    }
    let pullback = pullback_inertia_bound(&indefinite, &collapsing).expect("the shapes meet");
    report("pullback of the same material", &pullback);
    println!(
        "  PᵀAP is the zero form: {}",
        pullback.form == SymmetricForm::zeros(2)
    );
    for vector in &pullback.kernel {
        let image = collapsing.apply(vector).expect("the extents meet");
        let written: Vec<String> = vector.iter().map(ToString::to_string).collect();
        println!(
            "  the collapsed direction ({}) has P x = 0: {}",
            written.join(", "),
            image.iter().all(Zero::is_zero)
        );
    }
    println!(
        "  a rank-{} collapse cost {} directions of the form -- strictness and collapse differ",
        pullback.collapsed_extent(),
        pullback.rank_lost()
    );

    // ---------------------------------------------------------------------------------------
    println!();
    println!("-- the negative control: strict without a collapse --");
    let restriction = matrix(&[vec![1], vec![0]]);
    let pullback = pullback_inertia_bound(&indefinite, &restriction).expect("the shapes meet");
    report("an injective restriction", &pullback);
    println!(
        "  injective {} -- one side tightened with an empty kernel, so a strict bound is not \
         evidence of a collapse",
        pullback.is_injective()
    );

    // ---------------------------------------------------------------------------------------
    println!();
    println!("-- control 2: the tightness fixture --");
    let at = rat(4);
    let levels = [rat(3), rat(5), rat(-2)];
    let repeats = 2usize;
    let at_rest = 2usize;
    let mut diagonal: Vec<Rat> = levels.to_vec();
    diagonal.extend(std::iter::repeat_n(at.clone(), repeats));
    diagonal.extend(std::iter::repeat_n(Rat::zero(), at_rest));
    let block = SymmetricForm::from_diagonal(diagonal);

    let terms: Vec<String> = levels
        .iter()
        .map(|level| format!("k_{at}({level}) = {}", block_defect(&at, level)))
        .collect();
    let right = levels
        .iter()
        .map(|level| block_defect(&at, level))
        .fold(Rat::zero(), |sum, term| sum + term)
        + &at * &at * rat(repeats as i64);
    let left = rank_trace_defect(&block, &at);
    println!("  M = diag(3, 5, -2) (+) 4·I_2 (+) 0_2,   c = {at},  b = {repeats}");
    println!("  2c·tr(M) - ||M||^2_F        = {left}");
    println!(
        "  sum_j k_c(m_j) + c^2·b      = {right}     [{}]",
        terms.join(", ")
    );
    println!("  equality holds exactly: {}", left == right);
    println!(
        "  the fixture is not resting on positivity: one level is negative, k_c(-2) = {}",
        block_defect(&at, &levels[2])
    );

    // the same identity through a pull-back that keeps one level, one repeat, one rest direction
    let mut columns = vec![vec![0i64; 3]; block.extent()];
    columns[0][0] = 1;
    columns[3][1] = 1;
    columns[5][2] = 1;
    let selection = matrix(&columns);
    let restricted = pullback_inertia_bound(&block, &selection).expect("the shapes meet");
    let after = rank_trace_defect(&restricted.form, &at);
    let expected = block_defect(&at, &levels[0]) + &at * &at;
    println!(
        "  after restricting to (m=3, c, 0):  left {after}  right {expected}  equal {}",
        after == expected
    );
    report("the restricted block", &restricted);

    // ---------------------------------------------------------------------------------------
    println!();
    println!("-- control 3: invertible P reproduces congruence exactly --");
    let forms = [
        SymmetricForm::from_diagonal(vec![rat(1), rat(-1)]),
        integers(&[vec![0, 1], vec![1, 0]]),
        integers(&[vec![2, 1], vec![1, 2]]),
        integers(&[vec![1, 1], vec![1, 1]]),
    ];
    let bases = [
        fractional(&[vec![(1, 1), (1, 1)], vec![(0, 1), (1, 1)]]),
        fractional(&[vec![(2, 1), (0, 1)], vec![(0, 1), (3, 1)]]),
        fractional(&[vec![(1, 1), (2, 1)], vec![(3, 1), (4, 1)]]),
        fractional(&[vec![(1, 2), (1, 3)], vec![(1, 1), (1, 1)]]),
    ];
    let mut agreed = 0usize;
    let mut saturated = 0usize;
    for form in &forms {
        for change in &bases {
            let by_congruence = congruence(form, change).expect("the basis is invertible");
            let pullback = pullback_inertia_bound(form, change).expect("the shapes meet");
            if pullback.form == by_congruence && pullback.pulled_back == inertia(&by_congruence) {
                agreed += 1;
            }
            if !pullback.positive_is_strict() && !pullback.negative_is_strict() {
                saturated += 1;
            }
        }
    }
    println!(
        "  {agreed} of {} form/basis pairs reproduce congruence exactly; {saturated} saturate the \
         bound",
        forms.len() * bases.len()
    );

    // ---------------------------------------------------------------------------------------
    println!();
    println!("-- the bound on a rank-ten indefinite lattice --");
    let lattice = e10();
    println!(
        "  E10 signature {:?}, and the Hodge index theorem says (1, rho-1)",
        inertia(&lattice).signature()
    );
    let mut columns = vec![vec![0i64; 3]; 10];
    columns[0][0] = 1;
    columns[1][0] = 1;
    columns[2][1] = 1;
    columns[5][1] = -2;
    columns[0][2] = 1;
    columns[1][2] = 1;
    let pullback = pullback_inertia_bound(&lattice, &matrix(&columns)).expect("the shapes meet");
    report("E10 along a 10x3 map", &pullback);
    let written: Vec<String> = pullback
        .kernel
        .iter()
        .map(|vector| {
            let entries: Vec<String> = vector.iter().map(ToString::to_string).collect();
            format!("({})", entries.join(", "))
        })
        .collect();
    println!("  the collapsed population: {}", written.join(" "));

    // ---------------------------------------------------------------------------------------
    println!();
    println!("-- the refusal the shape owes --");
    let mismatched = pullback_inertia_bound(&SymmetricForm::zeros(3), &matrix(&[vec![1], vec![0]]));
    println!("  a pull-back whose rows miss the extent: {mismatched:?}");
}
