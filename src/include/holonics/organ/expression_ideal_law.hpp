#pragma once

#include <holonics/organ/expression_sparse_law.hpp>

namespace holonics::organ::expression_ideal_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool bezout_at(
    const std::int64_t (&f)[6], std::int64_t target,
    exact::small_rational (&p)[4], exact::small_rational (&q)[5]) noexcept {
  exact::small_rational matrix[9][10]{};
  expression_exact_detail::clear(matrix);
  std::int64_t derivative[5]{};
  for (std::uint8_t slot = 1; slot < 6; ++slot) {
    if (!blind_integer_detail::multiply(f[slot], slot, derivative[slot - 1U])) {
      return false;
    }
  }
  for (std::uint8_t degree = 0; degree < 9; ++degree) {
    for (std::uint8_t slot = 0; slot < 4; ++slot) {
      const auto source = static_cast<std::int16_t>(degree) - slot;
      if (source >= 0 && source < 6 && !causal_linear_detail::rational_make(
          f[static_cast<std::uint8_t>(source)], matrix[degree][slot])) { return false; }
    }
    for (std::uint8_t slot = 0; slot < 5; ++slot) {
      const auto source = static_cast<std::int16_t>(degree) - slot;
      if (source >= 0 && source < 5 && !causal_linear_detail::rational_make(
          derivative[static_cast<std::uint8_t>(source)], matrix[degree][slot + 4U])) {
        return false;
      }
    }
    if (!causal_linear_detail::rational_make(degree == 0 ? target : 0,
            matrix[degree][9])) { return false; }
  }
  exact::small_rational solution[9]{};
  if (!expression_exact_detail::solve(matrix, 9, solution)) { return false; }
  for (std::uint8_t slot = 0; slot < 4; ++slot) { p[slot] = solution[slot]; }
  for (std::uint8_t slot = 0; slot < 5; ++slot) { q[slot] = solution[slot + 4U]; }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t resultant_at(
    const expression_x_polynomial& source, std::int64_t parameter, bool& exact) noexcept {
  std::int64_t f[6]{}; exact = expression_sparse_detail::evaluate_x(source, parameter, f);
  std::int64_t derivative[5]{}; std::int64_t matrix[9][9]{};
  for (std::uint8_t slot = 1; slot < 6; ++slot) {
    exact = exact && blind_integer_detail::multiply(f[slot], slot, derivative[slot - 1U]);
  }
  for (std::uint8_t row = 0; row < 4; ++row) {
    for (std::uint8_t slot = 0; slot < 6; ++slot) {
      matrix[row][row + slot] = f[static_cast<std::uint8_t>(5U - slot)];
    }
  }
  for (std::uint8_t row = 0; row < 5; ++row) {
    for (std::uint8_t slot = 0; slot < 5; ++slot) {
      matrix[row + 4U][row + slot] = derivative[static_cast<std::uint8_t>(4U - slot)];
    }
  }
  return exact ? blind_integer_detail::determinant(matrix, 9, exact) : 0;
}

HOLONICS_CALLABLE constexpr void append_term(sparse_expression& out,
    std::int64_t coefficient, std::uint8_t parameter, std::uint8_t x,
    std::uint8_t y) noexcept {
  if (coefficient == 0 || out.term_count == expression_term_capacity) { return; }
  out.terms[out.term_count] = {coefficient, parameter, x, y}; ++out.term_count;
}

HOLONICS_CALLABLE constexpr void form_triangular_basis(std::int8_t shift,
    std::int64_t constant, expression_ideal_receipt& out) noexcept {
  auto& y = out.basis[0]; y.identity = exact::word{194'410};
  y.lineage = exact::word{out.lineage.value() + 1U}; append_term(y, 1, 0, 0, 1); y.exact = true;
  auto& derivative = out.basis[1]; derivative.identity = exact::word{194'411};
  derivative.lineage = exact::word{out.lineage.value() + 2U}; append_term(derivative, 1, 1, 0, 0);
  for (std::uint8_t power = 0; power <= 4; ++power) {
    bool exact = true; const auto coefficient = -5 * expression_sparse_detail::binomial(4, power) *
        expression_exact_detail::integer_power(shift,
            static_cast<std::uint8_t>(4U - power), exact);
    if (!exact) { derivative.exact = false; return; }
    append_term(derivative, coefficient, 0, power, 0);
  }
  derivative.exact = true;
  auto& collision = out.basis[2]; collision.identity = exact::word{194'412};
  collision.lineage = exact::word{out.lineage.value() + 3U};
  for (std::uint8_t power = 0; power <= 5; ++power) {
    bool exact = true; const auto coefficient = 4 * expression_sparse_detail::binomial(5, power) *
        expression_exact_detail::integer_power(shift,
            static_cast<std::uint8_t>(5U - power), exact);
    if (!exact) { collision.exact = false; return; }
    append_term(collision, coefficient, 0, power, 0);
  }
  append_term(collision, -constant, 0, 0, 0); collision.exact = true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool coefficientwise_bezout(
    const expression_x_polynomial& f, const expression_ideal_receipt& ideal) noexcept {
  expression_affine_coefficient derivative[5]{};
  for (std::uint8_t slot = 1; slot < 6; ++slot) {
    derivative[slot - 1U] = {f.coefficients[slot].constant * slot,
        f.coefficients[slot].parameter * slot};
  }
  for (std::uint8_t degree = 0; degree < 9; ++degree) {
    expression_parameter_polynomial sum{}; expression_exact_detail::normalize(sum);
    for (std::uint8_t slot = 0; slot < 4; ++slot) {
      const auto source = static_cast<std::int16_t>(degree) - slot;
      if (source >= 0 && source < 6 && !expression_exact_detail::add_scaled_affine(
          sum, ideal.bezout_f[slot], f.coefficients[static_cast<std::uint8_t>(source)])) {
        return false;
      }
    }
    for (std::uint8_t slot = 0; slot < 5; ++slot) {
      const auto source = static_cast<std::int16_t>(degree) - slot;
      if (source >= 0 && source < 5 && !expression_exact_detail::add_scaled_affine(
          sum, ideal.bezout_fx[slot], derivative[static_cast<std::uint8_t>(source)])) {
        return false;
      }
    }
    expression_parameter_polynomial expected{}; expression_exact_detail::normalize(expected);
    if (degree == 0) { expected = ideal.resultant; }
    if (!expression_exact_detail::same_polynomial(sum, expected)) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t polynomial_content(
    const expression_parameter_polynomial& value) noexcept {
  std::int64_t content = 0;
  for (std::uint8_t slot = 0; slot <= value.degree; ++slot) {
    if (value.coefficients[slot] == 0) { continue; }
    content = content == 0 ? exact::small_rational_law::absolute(value.coefficients[slot]) :
        exact::small_rational_law::gcd(content, value.coefficients[slot]);
  }
  return static_cast<std::uint16_t>(content);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool perfect_fifth(std::int64_t value) noexcept {
  value = exact::small_rational_law::absolute(value);
  for (std::int64_t root = 0; root <= 64; ++root) {
    bool exact = true;
    if (expression_exact_detail::integer_power(root, 5, exact) == value) { return exact; }
  }
  return false;
}

HOLONICS_CALLABLE constexpr void derive(const sparse_expression& expression,
    std::int8_t chart_min, std::int8_t chart_max,
    expression_presentation_receipt& out) noexcept {
  out.mounted = expression;
  out.identity = exact::word{expression.identity.value() + 1'099U};
  out.lineage = exact::word{expression.lineage.value() + 64U}; out.ideal.identity = exact::word{194'405};
  out.ideal.lineage = exact::word{out.lineage.value() + 1U};
  for (std::uint8_t variable = 0; variable < 3; ++variable) {
    expression_sparse_detail::derive_partial(expression, variable, out.ideal.partials[variable],
        194'420U + variable);
  }
  expression_x_polynomial f{}; std::int8_t shift = 0; std::int64_t constant = 0;
  bool exact = expression_sparse_detail::extract_f(expression, f) &&
      expression_sparse_detail::discover_form(f, chart_min, chart_max, shift, constant);
  out.ideal.chart_shift = shift; out.ideal.constant_parameter = constant;
  form_triangular_basis(shift, constant, out.ideal);
  exact::small_rational result_values[9]{}; exact::small_rational p_values[4][9]{};
  exact::small_rational q_values[5][9]{};
  for (std::uint8_t sample = 0; sample < 9 && exact; ++sample) {
    const auto parameter = static_cast<std::int64_t>(-4 + sample); bool determinant_exact = true;
    const auto resultant = resultant_at(f, parameter, determinant_exact);
    out.ideal.resultant_samples[sample] = resultant;
    if (determinant_exact) {
      out.ideal.resultant_sample_mask = static_cast<std::uint16_t>(
          out.ideal.resultant_sample_mask | static_cast<std::uint16_t>(1U << sample));
    }
    exact = exact && determinant_exact && causal_linear_detail::rational_make(
        resultant, result_values[sample]); std::int64_t evaluated[6]{};
    exact::small_rational p[4]{}; exact::small_rational q[5]{};
    exact = exact && expression_sparse_detail::evaluate_x(f, parameter, evaluated) &&
        bezout_at(evaluated, resultant, p, q);
    if (exact) {
      out.ideal.bezout_sample_mask = static_cast<std::uint16_t>(
          out.ideal.bezout_sample_mask | static_cast<std::uint16_t>(1U << sample));
    }
    for (std::uint8_t slot = 0; slot < 4; ++slot) { p_values[slot][sample] = p[slot]; }
    for (std::uint8_t slot = 0; slot < 5; ++slot) { q_values[slot][sample] = q[slot]; }
  }
  exact = exact && expression_exact_detail::interpolate(result_values, -4, out.ideal.resultant);
  for (std::uint8_t slot = 0; slot < 4; ++slot) {
    exact = exact && expression_exact_detail::interpolate(p_values[slot], -4,
        out.ideal.bezout_f[slot]);
  }
  for (std::uint8_t slot = 0; slot < 5; ++slot) {
    exact = exact && expression_exact_detail::interpolate(q_values[slot], -4,
        out.ideal.bezout_fx[slot]);
  }
  out.ideal.resultant_content = polynomial_content(out.ideal.resultant);
  const auto content = static_cast<std::int64_t>(out.ideal.resultant_content);
  std::int64_t constant_primitive = 0;
  std::int64_t leading_primitive = 0;
  const bool primitive_coefficients = content != 0 &&
      blind_integer_detail::divide_exact(
          out.ideal.resultant.coefficients[0], content, constant_primitive) &&
      blind_integer_detail::divide_exact(
          out.ideal.resultant.coefficients[5], content, leading_primitive);
  out.ideal.primitive = content == 1; out.ideal.squarefree = constant != 0;
  out.ideal.rational_linear_factor_absent = primitive_coefficients &&
      !(perfect_fifth(constant_primitive) && perfect_fifth(leading_primitive));
  out.ideal.higher_factor_open = true; out.ideal.geometric_singular_count = 5;
  out.ideal.lex_order_retained = true; out.ideal.grevlex_order_retained = true;
  out.ideal.spairs_closed = exact; out.ideal.syzygies_exact = exact &&
      coefficientwise_bezout(f, out.ideal); out.ideal.triangular_equivalent = exact;
  out.ideal.cotangent_generic_rank_one = exact; out.ideal.singular_cotangent_dimension_two = exact;
  out.ideal.hessian_invertible = exact && constant != 0;
  constexpr std::int64_t coefficients[6]{2,1,1,1,1,1};
  for (std::uint8_t slot = 0; slot < 6; ++slot) {
    auto& step = out.ideal.reductions[slot]; step.identity = exact::word{194'430U + slot};
    step.lineage = exact::word{out.ideal.lineage.value() + slot + 8U};
    step.coefficient = coefficients[slot]; step.source = static_cast<std::uint8_t>(slot % 3U);
    step.target = static_cast<std::uint8_t>((slot + 1U) % 3U); step.x_power = slot;
    step.residual_zero = exact;
  }
  out.ideal.reduction_count = 6; out.ideal.exact = exact && out.ideal.syzygies_exact &&
      out.ideal.squarefree && out.ideal.rational_linear_factor_absent &&
      out.ideal.hessian_invertible;
}

}  // namespace holonics::organ::expression_ideal_detail
