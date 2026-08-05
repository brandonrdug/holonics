#pragma once

#include <holonics/organ/variation_invariant_law.hpp>

namespace holonics::organ::variation_operator_detail {

namespace rational = exact::small_rational_law;
namespace polynomial = variation_polynomial_detail;
namespace connection = variation_connection_detail;

[[nodiscard]] HOLONICS_CALLABLE constexpr exact::small_rational connection_derivative(
    const algebraic_variation_receipt& out, exact::small_rational parameter,
    std::uint8_t row, std::uint8_t column) noexcept {
  const auto numerator = connection::affine_value(out.connection.numerator[row][column], parameter);
  const auto numerator_derivative = rational::make(
      out.connection.numerator[row][column].parameter);
  const auto pole = polynomial::evaluate(out.connection.pole_polynomial, parameter);
  parameter_polynomial derivative{};
  for (std::uint8_t slot = 1; slot <= out.connection.pole_polynomial.degree; ++slot) {
    derivative.coefficients[slot - 1U] =
        out.connection.pole_polynomial.coefficients[slot] * slot;
  }
  polynomial::normalize(derivative);
  const auto denominator = rational::multiply(
      rational::make(out.connection.denominator_scale), pole);
  const auto denominator_derivative = rational::multiply(
      rational::make(out.connection.denominator_scale), polynomial::evaluate(derivative, parameter));
  return rational::divide(rational::subtract(
      rational::multiply(numerator_derivative, denominator),
      rational::multiply(numerator, denominator_derivative)),
      rational::multiply(denominator, denominator));
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool derive_kernel(
    algebraic_variation_receipt& out, exact::small_rational vector[6],
    std::uint8_t& returned_rank) noexcept {
  exact::small_rational matrix[18][7]{}; std::uint8_t rows = 0;
  for (std::uint8_t sample = 0; sample < out.mounted.discovery_count; ++sample) {
    const auto t = out.samples[sample].parameter;
    for (std::uint8_t state = 0; state < 2; ++state) {
      const auto u = rational::make(state == 0 ? 1 : 0);
      const auto up = out.samples[sample].connection[0][state];
      auto upp = connection_derivative(out, t, 0, state);
      for (std::uint8_t inner = 0; inner < 2; ++inner) {
        upp = rational::add(upp, rational::multiply(
            out.samples[sample].connection[0][inner],
            out.samples[sample].connection[inner][state]));
      }
      matrix[rows][0] = upp; matrix[rows][1] = rational::multiply(t, upp);
      matrix[rows][2] = rational::multiply(t, matrix[rows][1]);
      matrix[rows][3] = up; matrix[rows][4] = rational::multiply(t, up);
      matrix[rows][5] = u; matrix[rows][6] = rational::make(0); ++rows;
    }
  }
  std::uint8_t pivot_columns[6]{}; std::uint8_t rank = 0;
  for (std::uint8_t column = 0; column < 6 && rank < rows; ++column) {
    std::uint8_t pivot = rank;
    while (pivot < rows && matrix[pivot][column].numerator == 0) { ++pivot; }
    if (pivot == rows) { continue; }
    if (pivot != rank) {
      for (std::uint8_t slot = column; slot < 7; ++slot) {
        const auto held = matrix[rank][slot]; matrix[rank][slot] = matrix[pivot][slot];
        matrix[pivot][slot] = held;
      }
    }
    const auto divisor = matrix[rank][column];
    for (std::uint8_t slot = column; slot < 7; ++slot) {
      matrix[rank][slot] = rational::divide(matrix[rank][slot], divisor);
    }
    for (std::uint8_t row = 0; row < rows; ++row) {
      if (row == rank) { continue; }
      const auto factor = matrix[row][column];
      for (std::uint8_t slot = column; slot < 7; ++slot) {
        matrix[row][slot] = rational::subtract(matrix[row][slot],
            rational::multiply(factor, matrix[rank][slot]));
      }
    }
    pivot_columns[rank] = column; ++rank;
  }
  returned_rank = rank;
  if (rank != 5) { return false; }
  bool is_pivot[6]{};
  for (std::uint8_t row = 0; row < rank; ++row) { is_pivot[pivot_columns[row]] = true; }
  std::uint8_t free_column = 0;
  while (free_column < 6 && is_pivot[free_column]) { ++free_column; }
  if (free_column == 6) { return false; }
  for (std::uint8_t slot = 0; slot < 6; ++slot) { vector[slot] = rational::make(0); }
  vector[free_column] = rational::make(1);
  for (std::uint8_t row = 0; row < rank; ++row) {
    vector[pivot_columns[row]] = rational::make(-matrix[row][free_column].numerator,
        matrix[row][free_column].denominator);
  }
  return true;
}

HOLONICS_CALLABLE constexpr void derive_scalar(algebraic_variation_receipt& out) noexcept {
  exact::small_rational kernel[6]{};
  if (!out.invariant.exact || !derive_kernel(out, kernel, out.scalar.constraint_rank)) {
    out.obstruction = variation_obstruction::operator_refused; return;
  }
  std::int64_t common = 1;
  for (const auto value : kernel) {
    common = rational::quotient(common * value.denominator,
        rational::gcd(common, value.denominator));
  }
  std::int64_t integers[6]{}; std::int64_t divisor = 0;
  for (std::uint8_t slot = 0; slot < 6; ++slot) {
    integers[slot] = kernel[slot].numerator * rational::quotient(common,
        kernel[slot].denominator);
    divisor = divisor == 0 ? rational::absolute(integers[slot]) :
        rational::gcd(divisor, integers[slot]);
  }
  for (auto& value : integers) { value = rational::quotient(value, divisor); }
  std::uint8_t first = 0; while (first < 6 && integers[first] == 0) { ++first; }
  if (first == 6) { out.obstruction = variation_obstruction::operator_refused; return; }
  if (integers[first] < 0) { for (auto& value : integers) { value = -value; } }
  for (std::uint8_t slot = 0; slot < 3; ++slot) { out.scalar.second[slot] = integers[slot]; }
  out.scalar.first[0] = integers[3]; out.scalar.first[1] = integers[4];
  out.scalar.zeroth = integers[5]; out.scalar.primitive = true;
  out.scalar.discovery_only = true; out.scalar.holdouts_exact = true;
  for (std::uint8_t sample = out.mounted.discovery_count;
      sample < out.mounted.sample_count; ++sample) {
    const auto t = out.samples[sample].parameter;
    for (std::uint8_t state = 0; state < 2; ++state) {
      const auto u = rational::make(state == 0 ? 1 : 0);
      const auto up = out.samples[sample].connection[0][state];
      auto upp = connection_derivative(out, t, 0, state);
      for (std::uint8_t inner = 0; inner < 2; ++inner) {
        upp = rational::add(upp, rational::multiply(
            out.samples[sample].connection[0][inner],
            out.samples[sample].connection[inner][state]));
      }
      const auto second = rational::add(rational::make(out.scalar.second[0]),
          rational::multiply(t, rational::add(rational::make(out.scalar.second[1]),
              rational::multiply(t, rational::make(out.scalar.second[2])))));
      const auto first_value = rational::add(rational::make(out.scalar.first[0]),
          rational::multiply(t, rational::make(out.scalar.first[1])));
      const auto residual = rational::add(rational::multiply(second, upp),
          rational::add(rational::multiply(first_value, up),
              rational::multiply(rational::make(out.scalar.zeroth), u)));
      out.scalar.holdouts_exact = out.scalar.holdouts_exact && residual.numerator == 0;
    }
  }
  out.scalar.series[0] = rational::make(1);
  out.scalar.series_count = static_cast<std::uint8_t>(out.mounted.series_depth + 1U);
  out.scalar.recurrence_exact = true;
  for (std::uint8_t n = 0; n < out.mounted.series_depth; ++n) {
    const std::int64_t index = n;
    const std::int64_t denominator = (index + 1) *
        (out.scalar.second[1] * index + out.scalar.first[0]);
    const std::int64_t numerator = -(out.scalar.second[2] * index * (index - 1) +
        out.scalar.first[1] * index + out.scalar.zeroth);
    out.scalar.series[n + 1U] = rational::multiply(out.scalar.series[n],
        rational::make(numerator, denominator));
    out.scalar.recurrence_exact = out.scalar.recurrence_exact &&
        out.scalar.series[n + 1U].denominator != 0;
  }
  out.scalar.identity = exact::word{191'550};
  out.scalar.lineage = exact::word{out.mounted.lineage.value() + 160U};
  out.foils.operator_without_zeroth_rejected = out.scalar.zeroth != 0;
  out.scalar.exact = out.scalar.holdouts_exact && out.scalar.recurrence_exact;
  if (!out.scalar.exact) { out.obstruction = variation_obstruction::operator_refused; }
}

}  // namespace holonics::organ::variation_operator_detail
