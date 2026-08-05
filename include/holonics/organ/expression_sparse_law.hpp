#pragma once

#include <holonics/organ/expression_exact_law.hpp>

namespace holonics::organ::expression_sparse_detail {

struct dense_expression final {
  std::int64_t coefficients[2][6][3]{};
  bool exact{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid(
    const sparse_expression& expression) noexcept {
  if (!expression.exact || expression.term_count == 0 ||
      expression.term_count > expression_term_capacity) { return false; }
  std::uint16_t y_square = 0;
  for (std::uint8_t slot = 0; slot < expression.term_count; ++slot) {
    const auto& term = expression.terms[slot];
    if (term.coefficient == 0 || term.parameter_power > 1 || term.x_power > 5 ||
        (term.y_power != 0 && term.y_power != 2)) { return false; }
    y_square = static_cast<std::uint16_t>(
        y_square + static_cast<std::uint16_t>(term.y_power == 2 ? 1U : 0U));
  }
  return y_square == 1;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool extract_f(
    const sparse_expression& expression, expression_x_polynomial& out) noexcept {
  if (!valid(expression)) { return false; }
  bool y_square = false;
  for (std::uint8_t slot = 0; slot < expression.term_count; ++slot) {
    const auto& term = expression.terms[slot];
    if (term.y_power == 2) {
      y_square = term.coefficient == 1 && term.x_power == 0 && term.parameter_power == 0;
      continue;
    }
    auto& coefficient = out.coefficients[term.x_power];
    if (term.parameter_power == 0) { coefficient.constant -= term.coefficient; }
    else { coefficient.parameter -= term.coefficient; }
  }
  out.degree = 5; out.exact = y_square && out.coefficients[5].constant == 1 &&
      out.coefficients[5].parameter == 0; return out.exact;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool evaluate_x(
    const expression_x_polynomial& source, std::int64_t parameter,
    std::int64_t (&out)[expression_x_capacity]) noexcept {
  if (!source.exact) { return false; }
  for (std::uint8_t slot = 0; slot < expression_x_capacity; ++slot) {
    std::int64_t product = 0;
    if (!blind_integer_detail::multiply(source.coefficients[slot].parameter,
            parameter, product) || !blind_integer_detail::add(
            source.coefficients[slot].constant, product, out[slot])) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t binomial(
    std::uint8_t degree, std::uint8_t slot) noexcept {
  constexpr std::int64_t values[6][6]{{1,0,0,0,0,0},{1,1,0,0,0,0},
      {1,2,1,0,0,0},{1,3,3,1,0,0},{1,4,6,4,1,0},{1,5,10,10,5,1}};
  return values[degree][slot];
}

[[nodiscard]] HOLONICS_CALLABLE constexpr dense_expression dense(
    const sparse_expression& source) noexcept {
  dense_expression out{}; out.exact = valid(source);
  for (std::uint8_t slot = 0; slot < source.term_count && out.exact; ++slot) {
    const auto& term = source.terms[slot]; std::int64_t next = 0;
    out.exact = blind_integer_detail::add(
        out.coefficients[term.parameter_power][term.x_power][term.y_power],
        term.coefficient, next); out.coefficients[term.parameter_power][term.x_power]
        [term.y_power] = next;
  }
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool rechart_identity(
    const sparse_expression& source, const sparse_expression& target,
    std::int8_t x_scale, std::int8_t x_shift, std::int8_t y_square,
    std::int8_t equation_scale) noexcept {
  const auto expected = dense(target); dense_expression transformed{};
  transformed.exact = valid(source) && expected.exact;
  for (std::uint8_t slot = 0; slot < source.term_count && transformed.exact; ++slot) {
    const auto& term = source.terms[slot];
    const auto y_factor = term.y_power == 2 ? y_square : 1;
    for (std::uint8_t power = 0; power <= term.x_power; ++power) {
      bool exact = true;
      const auto scale_power = expression_exact_detail::integer_power(x_scale, power, exact);
      const auto shift_power = expression_exact_detail::integer_power(
          x_shift, static_cast<std::uint8_t>(term.x_power - power), exact);
      std::int64_t coefficient = 0; std::int64_t held = 0; std::int64_t next = 0;
      transformed.exact = transformed.exact && exact &&
          blind_integer_detail::multiply(term.coefficient,
              binomial(term.x_power, power), held) &&
          blind_integer_detail::multiply(held, scale_power, coefficient) &&
          blind_integer_detail::multiply(coefficient, shift_power, held) &&
          blind_integer_detail::multiply(held, y_factor, coefficient) &&
          blind_integer_detail::add(transformed.coefficients[term.parameter_power][power]
              [term.y_power], coefficient, next);
      transformed.coefficients[term.parameter_power][power][term.y_power] = next;
    }
  }
  for (std::uint8_t t = 0; t < 2; ++t) {
    for (std::uint8_t x = 0; x < 6; ++x) {
      for (std::uint8_t y = 0; y < 3; ++y) {
        if (transformed.coefficients[t][x][y] !=
            equation_scale * expected.coefficients[t][x][y]) { return false; }
      }
    }
  }
  return transformed.exact;
}

HOLONICS_CALLABLE constexpr void derive_partial(const sparse_expression& source,
    std::uint8_t variable, sparse_expression& out, std::uint64_t identity) noexcept {
  out.identity = exact::word{identity}; out.lineage = exact::word{source.lineage.value() + variable};
  for (std::uint8_t slot = 0; slot < source.term_count; ++slot) {
    auto term = source.terms[slot]; const auto exponent = variable == 0 ?
        term.parameter_power : (variable == 1 ? term.x_power : term.y_power);
    if (exponent == 0) { continue; }
    term.coefficient *= exponent;
    if (variable == 0) { --term.parameter_power; }
    else if (variable == 1) { --term.x_power; }
    else { --term.y_power; }
    out.terms[out.term_count] = term; ++out.term_count;
  }
  out.exact = out.term_count != 0 && out.term_count <= expression_term_capacity;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool discover_form(
    const expression_x_polynomial& source, std::int8_t minimum, std::int8_t maximum,
    std::int8_t& shift, std::int64_t& constant) noexcept {
  for (std::int8_t candidate = minimum; candidate <= maximum; ++candidate) {
    bool exact = true; expression_x_polynomial expected{}; expected.degree = 5;
    for (std::uint8_t power = 0; power <= 5; ++power) {
      expected.coefficients[power].constant = binomial(5, power) *
          expression_exact_detail::integer_power(candidate,
              static_cast<std::uint8_t>(5U - power), exact);
    }
    expected.coefficients[1].parameter = -1;
    expected.coefficients[0].parameter = -candidate;
    const auto derived_constant = source.coefficients[0].constant -
        expected.coefficients[0].constant;
    expected.coefficients[0].constant += derived_constant;
    bool same = exact;
    for (std::uint8_t slot = 0; slot < 6; ++slot) {
      same = same && expected.coefficients[slot].constant ==
          source.coefficients[slot].constant && expected.coefficients[slot].parameter ==
          source.coefficients[slot].parameter;
    }
    if (same) { shift = candidate; constant = derived_constant; return true; }
  }
  return false;
}

}  // namespace holonics::organ::expression_sparse_detail
