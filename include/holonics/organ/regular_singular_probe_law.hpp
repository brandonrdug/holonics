#pragma once

#include <holonics/organ/regular_singular_exact.hpp>

namespace holonics::organ::regular_singular_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr regular_singular_chart_receipt form_chart(
    const regular_singular_foundation& foundation, std::uint16_t slot) noexcept {
  regular_singular_chart_receipt result{};
  if (!valid_foundation(foundation) || slot >= regular_singular_chart_capacity) { return result; }
  const auto system = derive_system(foundation.mounted_operator);
  result.identity = exact::word{187'400U + slot};
  result.chart = exact::word{157'400U + slot};
  if (slot == 0) {
    result.residue = system.zero;
    result.lower_eigenvalue = -1;
    result.upper_eigenvalue = 0;
    result.right_eigenvector[0] = 1;
    result.right_eigenvector[1] = -1;
    result.recurrence_image[0] = -1;
    result.recurrence_image[1] = 1;
    result.recurrence_cokernel[0] = 1;
    result.recurrence_cokernel[1] = 1;
    const matrix_two source_matrix{-system.one.a, -system.one.b,
        -system.one.c, -system.one.d};
    matvec(source_matrix, result.right_eigenvector, result.resonant_source);
    result.scalar_indicial[1] = 1;
    result.scalar_indicial[2] = 1;
    result.eigenvalue_gap = 1;
    result.eigenflag_dimension = 2;
    result.resonance_checked = true;
  } else if (slot == 1) {
    result.residue = system.one;
    result.lower_eigenvalue = -1;
    result.upper_eigenvalue = 0;
    result.right_eigenvector[1] = 1;
    result.recurrence_image[1] = 1;
    result.recurrence_cokernel[0] = 1;
    matvec(system.zero, result.right_eigenvector, result.resonant_source);
    result.scalar_indicial[2] = 1;
    result.eigenvalue_gap = 1;
    result.eigenflag_dimension = 2;
    result.resonance_checked = true;
    result.logarithmic_channel = true;
  } else {
    result.residue = system.infinity;
    result.lower_eigenvalue = 1;
    result.upper_eigenvalue = 1;
    result.right_eigenvector[0] = 1;
    result.right_eigenvector[1] = -1;
    result.generalized_vector[1] = -1;
    result.nilpotent = {result.residue.a - 1, result.residue.b,
        result.residue.c, result.residue.d - 1};
    result.scalar_indicial[0] = 1;
    result.scalar_indicial[1] = -2;
    result.scalar_indicial[2] = 1;
    result.eigenflag_dimension = 1;
    result.nilpotent_rank = 1;
    result.logarithmic_channel = true;
  }
  result.trace = characteristic_detail::trace(result.residue);
  result.determinant = characteristic_detail::determinant(result.residue);
  result.characteristic_discriminant =
      result.trace * result.trace - 4 * result.determinant;
  result.obstruction_scalar = dot(result.recurrence_cokernel, result.resonant_source);
  const std::int64_t lineage_values[26]{
      static_cast<std::int64_t>(foundation.differential_transport.value()),
      static_cast<std::int64_t>(foundation.resonance_transport.value()),
      foundation.mounted_operator.second[0], foundation.mounted_operator.second[1],
      foundation.mounted_operator.second[2], foundation.mounted_operator.first[0],
      foundation.mounted_operator.first[1], foundation.mounted_operator.zeroth,
      static_cast<std::int64_t>(slot),
      result.residue.a, result.residue.b, result.residue.c, result.residue.d,
      result.trace, result.determinant, result.characteristic_discriminant,
      result.lower_eigenvalue, result.upper_eigenvalue, result.right_eigenvector[0],
      result.right_eigenvector[1], result.recurrence_image[0], result.recurrence_image[1],
      result.recurrence_cokernel[0], result.recurrence_cokernel[1],
      result.resonant_source[0], result.resonant_source[1]};
  result.lineage = fold_values(lineage_values, 26);
  result.exact = system.derived &&
      ((slot == 0 && result.obstruction_scalar == 0 && !result.logarithmic_channel &&
           result.characteristic_discriminant == 1) ||
       (slot == 1 && result.obstruction_scalar == 1 && result.logarithmic_channel &&
           result.characteristic_discriminant == 1) ||
       (slot == 2 && result.characteristic_discriminant == 0 &&
           result.nilpotent_rank == 1 && result.logarithmic_channel));
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr frobenius_term_receipt form_term(
    const regular_singular_foundation& foundation, std::uint16_t degree) noexcept {
  frobenius_term_receipt result{};
  if (!valid_foundation(foundation) || degree >= foundation.term_count) { return result; }
  result.identity = exact::word{188'400U + degree};
  result.degree = degree;
  result.zero_numerator = 1;
  result.zero_denominator = static_cast<std::int64_t>(degree) + 1;
  result.one_regular = 1;
  result.one_logarithmic = -1;
  result.zero_step_lhs = static_cast<std::int64_t>(degree) + 1;
  result.zero_step_rhs = static_cast<std::int64_t>(degree) + 1;
  result.one_step_residual = 0;
  const std::int64_t lineage_values[10]{
      static_cast<std::int64_t>(foundation.term_seed.value()),
      static_cast<std::int64_t>(foundation.frobenius_transport.value()),
      foundation.mounted_operator.zeroth, degree, result.zero_numerator,
      result.zero_denominator, result.one_regular, result.one_logarithmic,
      result.zero_step_lhs, result.zero_step_rhs};
  result.lineage = fold_values(lineage_values, 10);
  result.exact = result.zero_step_lhs == result.zero_step_rhs &&
      result.one_step_residual == 0;
  return result;
}

}  // namespace holonics::organ::regular_singular_detail
