#pragma once

#include <holonics/organ/expression_ideal_law.hpp>

namespace holonics::organ::expression_connection_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool reduction_at(
    const expression_x_polynomial& source, std::int64_t parameter, std::uint8_t basis,
    expression_reduction_witness& out) noexcept {
  std::int64_t f[6]{}; std::int64_t derivative[5]{};
  if (!expression_sparse_detail::evaluate_x(source, parameter, f)) { return false; }
  for (std::uint8_t slot = 1; slot < 6; ++slot) {
    if (!blind_integer_detail::multiply(f[slot], slot, derivative[slot - 1U])) { return false; }
  }
  exact::small_rational matrix[9][10]{};
  expression_exact_detail::clear(matrix);
  for (std::uint8_t degree = 0; degree < 9; ++degree) {
    for (std::uint8_t slot = 0; slot < 4; ++slot) {
      const auto index = static_cast<std::int16_t>(degree) - slot;
      if (index >= 0 && index < 6 && !causal_linear_detail::rational_make(
          f[static_cast<std::uint8_t>(index)], matrix[degree][slot])) { return false; }
    }
    for (std::uint8_t slot = 0; slot < 5; ++slot) {
      const auto index = static_cast<std::int16_t>(degree) - slot;
      if (index >= 0 && index < 5 && !causal_linear_detail::rational_make(
          derivative[static_cast<std::uint8_t>(index)], matrix[degree][slot + 4U])) {
        return false;
      }
    }
    const auto source_degree = static_cast<std::int16_t>(degree) - basis;
    std::int64_t parameter_coefficient = 0;
    if (source_degree >= 0 && source_degree < 6) {
      parameter_coefficient = source.coefficients[static_cast<std::uint8_t>(source_degree)].parameter;
    }
    if (!causal_linear_detail::rational_make(-parameter_coefficient, 2,
            matrix[degree][9])) { return false; }
  }
  exact::small_rational solution[9]{};
  if (!expression_exact_detail::solve(matrix, 9, solution)) { return false; }
  for (std::uint8_t slot = 0; slot < 4; ++slot) { out.p[slot] = solution[slot]; }
  for (std::uint8_t slot = 0; slot < 5; ++slot) { out.q[slot] = solution[slot + 4U]; }
  for (std::uint8_t slot = 0; slot < 4; ++slot) {
    exact::small_rational derivative_q{}; exact::small_rational reduced{};
    if (!causal_linear_detail::rational_multiply(out.q[slot + 1U],
            {static_cast<std::int64_t>(2U * (slot + 1U)), 1}, derivative_q) ||
        !causal_linear_detail::rational_add(out.p[slot], derivative_q, reduced)) {
      return false;
    }
    out.reduced[slot] = reduced;
  }
  out.source_identity = true; out.differential_identity = true; out.exact = true; return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool scaled_value(exact::small_rational value,
    std::int64_t discriminant, exact::small_rational& out) noexcept {
  exact::small_rational scale{};
  return causal_linear_detail::rational_make(2 * discriminant, scale) &&
      causal_linear_detail::rational_multiply(value, scale, out) && out.denominator == 1;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool coefficientwise_reduction(
    const expression_x_polynomial& f, const expression_ideal_receipt& ideal,
    const expression_connection_receipt& connection, std::uint8_t basis) noexcept {
  expression_affine_coefficient derivative[5]{};
  for (std::uint8_t slot = 1; slot < 6; ++slot) {
    derivative[slot - 1U] = {f.coefficients[slot].constant * slot,
        f.coefficients[slot].parameter * slot};
  }
  for (std::uint8_t degree = 0; degree < 9; ++degree) {
    expression_parameter_polynomial sum{}; expression_exact_detail::normalize(sum);
    for (std::uint8_t slot = 0; slot < 4; ++slot) {
      const auto index = static_cast<std::int16_t>(degree) - slot;
      if (index >= 0 && index < 6 && !expression_exact_detail::add_scaled_affine(sum,
          connection.reduction_p[basis][slot], f.coefficients[static_cast<std::uint8_t>(index)])) {
        return false;
      }
    }
    for (std::uint8_t slot = 0; slot < 5; ++slot) {
      const auto index = static_cast<std::int16_t>(degree) - slot;
      if (index >= 0 && index < 5 && !expression_exact_detail::add_scaled_affine(sum,
          connection.reduction_q[basis][slot], derivative[static_cast<std::uint8_t>(index)])) {
        return false;
      }
    }
    expression_parameter_polynomial expected{}; expression_exact_detail::normalize(expected);
    const auto source_degree = static_cast<std::int16_t>(degree) - basis;
    if (source_degree >= 0 && source_degree < 6) {
      const auto parameter_coefficient =
          f.coefficients[static_cast<std::uint8_t>(source_degree)].parameter;
      if (!expression_exact_detail::scale_polynomial(ideal.resultant,
          -parameter_coefficient, expected)) { return false; }
    }
    if (!expression_exact_detail::same_polynomial(sum, expected)) { return false; }
  }
  for (std::uint8_t slot = 0; slot < 4; ++slot) {
    expression_parameter_polynomial expected = connection.reduction_p[basis][slot];
    if (slot < 4) {
      expression_parameter_polynomial scaled{};
      if (!expression_exact_detail::scale_polynomial(connection.reduction_q[basis][slot + 1U],
          static_cast<std::int64_t>(2U * (slot + 1U)), scaled)) { return false; }
      for (std::uint8_t degree = 0; degree < expression_parameter_capacity; ++degree) {
        if (!blind_integer_detail::add(expected.coefficients[degree],
                scaled.coefficients[degree], expected.coefficients[degree])) { return false; }
      }
      expression_exact_detail::normalize(expected);
    }
    if (!expression_exact_detail::same_polynomial(expected,
        connection.numerator[basis][slot])) { return false; }
  }
  return true;
}

HOLONICS_CALLABLE constexpr void derive(expression_presentation_receipt& out,
    std::int8_t discovery_min, std::int8_t discovery_max,
    std::int8_t holdout_first, std::int8_t holdout_second) noexcept {
  expression_x_polynomial f{}; bool exact = out.ideal.exact &&
      expression_sparse_detail::extract_f(out.mounted, f) &&
      discovery_min == -4 && discovery_max == 4;
  exact::small_rational p_values[4][4][9]{}; exact::small_rational q_values[4][5][9]{};
  std::uint8_t sample_slot = 0;
  for (std::int8_t parameter = discovery_min; parameter <= discovery_max && exact; ++parameter) {
    auto& sample = out.samples[sample_slot]; sample.parameter = {parameter, 1};
    bool determinant_exact = true; const auto discriminant = expression_ideal_detail::resultant_at(
        f, parameter, determinant_exact); sample.discriminant = {discriminant, 1};
    sample.identity = exact::word{194'500U + sample_slot};
    sample.lineage = exact::word{out.lineage.value() + sample_slot + 128U};
    sample.discovery = true; sample.regular = discriminant != 0; exact = exact && determinant_exact;
    for (std::uint8_t basis = 0; basis < 4 && exact; ++basis) {
      auto& reduction = sample.reductions[basis]; reduction.identity = exact::word{194'520U +
          static_cast<std::uint64_t>(sample_slot) * 4U + basis};
      reduction.lineage = exact::word{sample.lineage.value() + basis};
      exact = reduction_at(f, parameter, basis, reduction);
      for (std::uint8_t slot = 0; slot < 4 && exact; ++slot) {
        exact = scaled_value(reduction.p[slot], discriminant, p_values[basis][slot][sample_slot]);
      }
      for (std::uint8_t slot = 0; slot < 5 && exact; ++slot) {
        exact = scaled_value(reduction.q[slot], discriminant, q_values[basis][slot][sample_slot]);
      }
    }
    sample.exact = exact; ++sample_slot;
  }
  out.connection.identity = exact::word{194'600};
  out.connection.lineage = exact::word{out.lineage.value() + 256U};
  for (std::uint8_t basis = 0; basis < 4; ++basis) {
    for (std::uint8_t slot = 0; slot < 4; ++slot) {
      exact = exact && expression_exact_detail::interpolate(p_values[basis][slot], -4,
          out.connection.reduction_p[basis][slot]);
    }
    for (std::uint8_t slot = 0; slot < 5; ++slot) {
      exact = exact && expression_exact_detail::interpolate(q_values[basis][slot], -4,
          out.connection.reduction_q[basis][slot]);
    }
    for (std::uint8_t slot = 0; slot < 4; ++slot) {
      auto numerator = out.connection.reduction_p[basis][slot];
      expression_parameter_polynomial scaled{};
      exact = exact && expression_exact_detail::scale_polynomial(
          out.connection.reduction_q[basis][slot + 1U],
          static_cast<std::int64_t>(2U * (slot + 1U)), scaled);
      for (std::uint8_t degree = 0; degree < expression_parameter_capacity && exact; ++degree) {
        exact = blind_integer_detail::add(numerator.coefficients[degree],
            scaled.coefficients[degree], numerator.coefficients[degree]);
      }
      expression_exact_detail::normalize(numerator);
      out.connection.numerator[basis][slot] = numerator;
    }
    exact = exact && coefficientwise_reduction(f, out.ideal, out.connection, basis);
  }
  exact = exact && expression_exact_detail::scale_polynomial(
      out.ideal.resultant, 2, out.connection.denominator);
  const std::int8_t holdouts[2]{holdout_first, holdout_second};
  for (std::uint8_t held = 0; held < 2 && exact; ++held) {
    auto& sample = out.samples[sample_slot]; const auto parameter = holdouts[held];
    sample.parameter = {parameter, 1}; bool determinant_exact = true;
    const auto discriminant = expression_ideal_detail::resultant_at(f, parameter, determinant_exact);
    sample.discriminant = {discriminant, 1}; sample.identity = exact::word{194'570U + held};
    sample.lineage = exact::word{out.lineage.value() + 192U + held}; sample.holdout = true;
    sample.regular = discriminant != 0; exact = exact && determinant_exact;
    for (std::uint8_t basis = 0; basis < 4 && exact; ++basis) {
      auto& reduction = sample.reductions[basis]; reduction.identity = exact::word{194'580U +
          static_cast<std::uint64_t>(held) * 4U + basis}; reduction.lineage = sample.lineage;
      exact = reduction_at(f, parameter, basis, reduction);
      for (std::uint8_t slot = 0; slot < 4 && exact; ++slot) {
        exact::small_rational numerator{}; exact::small_rational denominator{};
        exact::small_rational quotient{};
        exact = expression_exact_detail::evaluate(out.connection.numerator[basis][slot],
            {parameter,1}, numerator) && expression_exact_detail::evaluate(
            out.connection.denominator, {parameter,1}, denominator) &&
            causal_linear_detail::rational_divide(numerator, denominator, quotient) &&
            expression_exact_detail::equal(quotient, reduction.reduced[slot]);
      }
    }
    sample.exact = exact; ++sample_slot;
  }
  out.sample_count = sample_slot; out.connection.rank = 4;
  out.connection.basis_derived = exact; out.connection.discovery_only = true;
  out.connection.coefficient_residual_zero = exact; out.connection.holdouts_exact = exact;
  out.connection.exact = exact;
}

}  // namespace holonics::organ::expression_connection_detail
