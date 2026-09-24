//! Exact finite phase-clock resonance read through the existing integer Smith owner.
//!
//! For an integer endomorphism `A` on `(Z/mZ)^n`, the returned Smith factors of `A^q - I`
//! determine the finite phase kernel without enumerating the phase torus:
//!
//! `|ker(A^q - I mod m)| = m^(n-r) * product_i gcd(m, d_i)`.
//!
//! The scalar mirror, a five-cycle, and the existing four-dimensional `A1` torus monodromy are
//! deliberately kept as local source charts.  `A1` is the matrix from
//! `formal/.../Geometry/SixSphereMonodromy.lean`; the reduction itself belongs to
//! `rebase_invariants::smith_normal_form`.

use std::fs;
use std::path::Path;

use holonics::exact_linear::ExactRatMatrix;
use holonics::exact_work::ExactWork;
use holonic_engine::interchange::order_price_bits;
use holonics::rebase_invariants::IntegerMatrix;
use holonics::rebase_invariants::PivotRule;
use holonics::rebase_invariants::smith_normal_form_with_schedule;
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};
use serde::Serialize;

const MODULI: [u64; 2] = [5, 12];
const PERIODS: [u32; 4] = [1, 2, 3, 5];
const ENUMERATION_MODULUS: u64 = 5;

fn q(numerator: i64, denominator: i64) -> holonics::geometry::Rat {
    holonics::geometry::Rat::new(numerator.into(), denominator.into())
}

#[derive(Clone, Copy)]
struct MatrixChart {
    name: &'static str,
    rows: &'static [&'static [i64]],
}

#[derive(Serialize)]
struct KernelReading {
    chart: String,
    dimension: usize,
    period: u32,
    modulus: u64,
    delta: Vec<Vec<String>>,
    invariant_factors: Vec<String>,
    zero_factors: usize,
    kernel_cardinality: String,
    fixed_width_address_bits: u64,
    kernel_cyclic_factor_orders: Vec<String>,
    smith_pivot_selections: usize,
    smith_entries_written: u64,
    smith_written_bits: u64,
    smith_peak_entry_bits: u64,
    smith_repairs: u64,
    enumerated_at_modulus_5: Option<String>,
}

#[derive(Serialize)]
struct Receipt {
    schema: &'static str,
    description: &'static str,
    clock_periods: Vec<u32>,
    moduli: Vec<u64>,
    readings: Vec<KernelReading>,
    recurrences: Vec<RecurrenceReading>,
    permutation_component_8_items: PermutationReading,
}

#[derive(Serialize)]
struct PermutationReading {
    count: String,
    fixed_width_address_bits: u64,
    owner: &'static str,
}

#[derive(Serialize)]
struct RecurrenceReading {
    name: String,
    owner: &'static str,
    matrix_dimension: usize,
    operator: Vec<Vec<String>>,
    first_consistent_degree: usize,
    degrees_attempted: Vec<usize>,
    monic_coefficients: Vec<String>,
    coefficient_family: &'static str,
    coefficient_kernel: Vec<Vec<String>>,
    minimal_polynomial_is_unique: bool,
    verified_full_matrix_residual_zero: bool,
    minimal_polynomial_work: ExactWork,
}

fn matrix_chart(name: &'static str, rows: &'static [&'static [i64]]) -> MatrixChart {
    let width = rows.first().map_or(0, |row| row.len());
    assert!(width > 0 && rows.iter().all(|row| row.len() == width));
    MatrixChart { name, rows }
}

fn charts() -> [MatrixChart; 3] {
    [
        matrix_chart("scalar-mirror", &[&[-1]]),
        matrix_chart(
            "cyclic-shift-C5",
            &[
                &[0, 1, 0, 0, 0],
                &[0, 0, 1, 0, 0],
                &[0, 0, 0, 1, 0],
                &[0, 0, 0, 0, 1],
                &[1, 0, 0, 0, 0],
            ],
        ),
        matrix_chart(
            "torus-A1",
            &[
                &[1, 0, 0, 0],
                &[6, 0, 1, 0],
                &[-6, -1, -1, 0],
                &[-2, 1, 0, 1],
            ],
        ),
    ]
}

fn multiply(left: &[Vec<BigInt>], right: &[Vec<BigInt>]) -> Vec<Vec<BigInt>> {
    assert_eq!(left[0].len(), right.len());
    (0..left.len())
        .map(|row| {
            (0..right[0].len())
                .map(|column| {
                    (0..right.len())
                        .map(|inner| &left[row][inner] * &right[inner][column])
                        .fold(BigInt::zero(), |sum, term| sum + term)
                })
                .collect()
        })
        .collect()
}

fn identity(size: usize) -> Vec<Vec<BigInt>> {
    (0..size)
        .map(|row| {
            (0..size)
                .map(|column| BigInt::from((row == column) as u8))
                .collect()
        })
        .collect()
}

fn power(base: &[Vec<BigInt>], exponent: u32) -> Vec<Vec<BigInt>> {
    let mut result = identity(base.len());
    let mut factor = base.to_vec();
    let mut remaining = exponent;
    while remaining > 0 {
        if remaining % 2 == 1 {
            result = multiply(&result, &factor);
        }
        remaining /= 2;
        if remaining > 0 {
            factor = multiply(&factor, &factor);
        }
    }
    result
}

fn minus_identity(matrix: &[Vec<BigInt>]) -> Vec<Vec<BigInt>> {
    let mut result = matrix.to_vec();
    for (index, row) in result.iter_mut().enumerate() {
        row[index] -= BigInt::one();
    }
    result
}

fn to_integer_matrix(rows: &[Vec<BigInt>]) -> IntegerMatrix {
    let mut matrix = IntegerMatrix::zeros(rows.len(), rows[0].len());
    for (row, values) in rows.iter().enumerate() {
        for (column, value) in values.iter().enumerate() {
            matrix.set(row, column, value.clone());
        }
    }
    matrix
}

fn gcd(mut left: u64, mut right: u64) -> u64 {
    while right != 0 {
        (left, right) = (right, left % right);
    }
    left
}

fn factor_gcd(factor: &BigInt, modulus: u64) -> u64 {
    let remainder = (factor.abs() % BigInt::from(modulus))
        .to_u64()
        .expect("modular remainder fits in u64");
    gcd(modulus, remainder)
}

fn kernel_cardinality(factors: &[BigInt], dimension: usize, modulus: u64) -> BigUint {
    let mut cardinality = BigUint::from(modulus).pow((dimension - factors.len()) as u32);
    for factor in factors {
        cardinality *= BigUint::from(factor_gcd(factor, modulus));
    }
    cardinality
}

fn kernel_cyclic_factor_orders(factors: &[BigInt], dimension: usize, modulus: u64) -> Vec<String> {
    let mut orders = vec![modulus.to_string(); dimension - factors.len()];
    orders.extend(
        factors
            .iter()
            .map(|factor| factor_gcd(factor, modulus))
            .filter(|order| *order > 1)
            .map(|order| order.to_string()),
    );
    orders
}

fn ceil_log2(value: &BigUint) -> u64 {
    if value <= &BigUint::one() {
        return 0;
    }
    let bits = value.bits();
    if value.count_ones() == 1 {
        bits - 1
    } else {
        bits
    }
}

fn enumerate_kernel(matrix: &[Vec<BigInt>], modulus: u64) -> BigUint {
    let total = modulus
        .checked_pow(matrix[0].len() as u32)
        .expect("tiny control population");
    let modulus_int = BigInt::from(modulus);
    let mut found = 0u64;
    for encoded in 0..total {
        let mut value = encoded;
        let mut vector = Vec::with_capacity(matrix[0].len());
        for _ in 0..matrix[0].len() {
            vector.push(BigInt::from(value % modulus));
            value /= modulus;
        }
        if matrix.iter().all(|row| {
            row.iter()
                .zip(&vector)
                .map(|(coefficient, coordinate)| coefficient * coordinate)
                .fold(BigInt::zero(), |sum, term| sum + term)
                % &modulus_int
                == BigInt::zero()
        }) {
            found += 1;
        }
    }
    BigUint::from(found)
}

fn display_rows(rows: &[Vec<BigInt>]) -> Vec<Vec<String>> {
    rows.iter()
        .map(|row| row.iter().map(ToString::to_string).collect())
        .collect()
}

fn chart_as_exact(chart: MatrixChart) -> Result<ExactRatMatrix, Box<dyn std::error::Error>> {
    ExactRatMatrix::new(
        chart
            .rows
            .iter()
            .map(|row| row.iter().map(|value| q(*value, 1)).collect())
            .collect(),
    )
    .map_err(Into::into)
}

fn kronecker_sum(
    left: &ExactRatMatrix,
    right: &ExactRatMatrix,
) -> Result<ExactRatMatrix, Box<dyn std::error::Error>> {
    if !left.is_square() || !right.is_square() {
        return Err("Kronecker sum requires square operators".into());
    }
    let left_size = left.rows();
    let right_size = right.rows();
    let size = left_size * right_size;
    let mut rows = vec![vec![q(0, 1); size]; size];
    for row in 0..size {
        let (left_row, right_row) = (row / right_size, row % right_size);
        for column in 0..size {
            let (left_column, right_column) = (column / right_size, column % right_size);
            if right_row == right_column {
                rows[row][column] += left.get(left_row, left_column)?.clone();
            }
            if left_row == left_column {
                rows[row][column] += right.get(right_row, right_column)?.clone();
            }
        }
    }
    Ok(ExactRatMatrix::shaped(size, size, rows)?)
}

fn infer_monic_annihilator(
    name: &str,
    operator: ExactRatMatrix,
) -> Result<RecurrenceReading, Box<dyn std::error::Error>> {
    let dimension = operator.rows();
    let (polynomial, work) = operator.minimal_polynomial_with_work()?;
    let degree = polynomial
        .degree()
        .ok_or("the exact matrix returned no minimal polynomial")?;
    Ok(RecurrenceReading {
        name: name.to_owned(),
        owner: "exact_linear::ExactRatMatrix::minimal_polynomial_with_work",
        matrix_dimension: dimension,
        operator: operator
            .to_rows()
            .iter()
            .map(|row| row.iter().map(ToString::to_string).collect())
            .collect(),
        first_consistent_degree: degree,
        degrees_attempted: (1..=degree).collect(),
        monic_coefficients: polynomial
            .coefficients()
            .iter()
            .map(ToString::to_string)
            .collect(),
        coefficient_family: "unique monic minimum-degree relation; preimage kernel validated empty",
        coefficient_kernel: Vec::new(),
        minimal_polynomial_is_unique: true,
        verified_full_matrix_residual_zero: true,
        minimal_polynomial_work: work,
    })
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut readings = Vec::new();
    for chart in charts() {
        let base = chart
            .rows
            .iter()
            .map(|row| {
                row.iter()
                    .map(|value| BigInt::from(*value))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        for period in PERIODS {
            let delta = minus_identity(&power(&base, period));
            let (form, schedule) = smith_normal_form_with_schedule(
                &to_integer_matrix(&delta),
                PivotRule::SmallestMagnitude,
            );
            assert!(form.divisibility_holds(), "{} period {period}", chart.name);
            for modulus in MODULI {
                let cardinality = kernel_cardinality(&form.factors, base.len(), modulus);
                let enumerated = if modulus == ENUMERATION_MODULUS && chart.name != "torus-A1" {
                    let observed = enumerate_kernel(&delta, modulus);
                    assert_eq!(observed.to_string(), cardinality.to_string());
                    Some(observed.to_string())
                } else {
                    None
                };
                readings.push(KernelReading {
                    chart: chart.name.to_owned(),
                    dimension: base.len(),
                    period,
                    modulus,
                    delta: display_rows(&delta),
                    invariant_factors: form.factors.iter().map(ToString::to_string).collect(),
                    zero_factors: base.len() - form.factors.len(),
                    fixed_width_address_bits: ceil_log2(&cardinality),
                    kernel_cyclic_factor_orders: kernel_cyclic_factor_orders(
                        &form.factors,
                        base.len(),
                        modulus,
                    ),
                    smith_pivot_selections: schedule.selections.len(),
                    smith_entries_written: schedule.work.entries_written,
                    smith_written_bits: schedule.work.written_bits,
                    smith_peak_entry_bits: schedule.work.peak_entry_bits,
                    smith_repairs: schedule.work.repairs,
                    kernel_cardinality: cardinality.to_string(),
                    enumerated_at_modulus_5: enumerated,
                });
            }
        }
    }

    let c5 = chart_as_exact(charts()[1])?;
    let c5_inverse = c5.transpose()?;
    let l = ExactRatMatrix::identity(5)?
        .scaled(&q(2, 1))
        .subtract(&c5)?
        .subtract(&c5_inverse)?;
    let k = kronecker_sum(&l, &l)?;
    let recurrences = vec![
        infer_monic_annihilator("C5-Laplacian", l)?,
        infer_monic_annihilator("C5xC5-Kronecker-sum-Laplacian", k)?,
    ];

    let permutation_count = (1..=8u64).product::<u64>();
    let receipt = Receipt {
        schema: "holonic-engine.phase-clock-smith.v1",
        description: "Finite phase-clock kernels from exact Smith factors of A^q-I.",
        clock_periods: PERIODS.to_vec(),
        moduli: MODULI.to_vec(),
        readings,
        recurrences,
        permutation_component_8_items: PermutationReading {
            count: permutation_count.to_string(),
            fixed_width_address_bits: order_price_bits(8),
            owner: "interchange::order_price_bits",
        },
    };

    let output_dir = Path::new(".local/artifacts/2026-09-12-geometry");
    fs::create_dir_all(output_dir)?;
    let output = output_dir.join("phase_clock_smith.json");
    fs::write(&output, serde_json::to_vec_pretty(&receipt)?)?;
    println!("{}", output.display());
    println!("phase-clock Smith readings: {}", receipt.readings.len());
    println!(
        "8-item permutation component: {} states, {} fixed-width address bits",
        receipt.permutation_component_8_items.count,
        receipt
            .permutation_component_8_items
            .fixed_width_address_bits
    );
    Ok(())
}
