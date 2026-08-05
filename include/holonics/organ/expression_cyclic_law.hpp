#pragma once

#include <holonics/organ/expression_connection_law.hpp>

namespace holonics::organ::expression_cyclic_detail {

struct rational_jet final { exact::small_rational coefficients[4]{}; };

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t choose(
    std::uint8_t degree, std::uint8_t slot) noexcept {
  if (slot > degree) { return 0; }
  if (slot > degree - slot) { slot = static_cast<std::uint8_t>(degree - slot); }
  std::int64_t result = 1;
  for (std::uint8_t step = 1; step <= slot; ++step) {
    std::int64_t product = 0; std::int64_t quotient = 0;
    if (!blind_integer_detail::multiply(result,
            static_cast<std::int64_t>(degree - slot + step), product) ||
        !blind_integer_detail::divide_exact(product, step, quotient)) { return 0; }
    result = quotient;
  }
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool taylor(
    const expression_parameter_polynomial& source, std::int64_t point,
    rational_jet& out) noexcept {
  for (std::uint8_t order = 0; order < 4; ++order) {
    std::int64_t sum = 0;
    for (std::uint8_t degree = order; degree <= source.degree; ++degree) {
      bool exact = true; const auto power = expression_exact_detail::integer_power(
          point, static_cast<std::uint8_t>(degree - order), exact);
      std::int64_t held = 0; std::int64_t product = 0; std::int64_t next = 0;
      if (!exact || !blind_integer_detail::multiply(source.coefficients[degree],
              choose(degree, order), held) || !blind_integer_detail::multiply(held, power, product) ||
          !blind_integer_detail::add(sum, product, next)) { return false; }
      sum = next;
    }
    if (!causal_linear_detail::rational_make(sum, out.coefficients[order])) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool quotient_jet(
    const expression_parameter_polynomial& numerator,
    const expression_parameter_polynomial& denominator, std::int64_t point,
    rational_jet& out) noexcept {
  rational_jet top{}; rational_jet bottom{};
  if (!taylor(numerator, point, top) || !taylor(denominator, point, bottom) ||
      bottom.coefficients[0].numerator == 0) { return false; }
  for (std::uint8_t order = 0; order < 4; ++order) {
    auto residual = top.coefficients[order];
    for (std::uint8_t slot = 1; slot <= order; ++slot) {
      exact::small_rational product{}; exact::small_rational next{};
      if (!expression_exact_detail::multiply(bottom.coefficients[slot],
              out.coefficients[order - slot], product) ||
          !expression_exact_detail::subtract(residual, product, next)) { return false; }
      residual = next;
    }
    if (!expression_exact_detail::divide(residual, bottom.coefficients[0],
            out.coefficients[order])) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool scalar_at(
    const expression_connection_receipt& connection, std::int64_t point,
    exact::small_rational (&coefficients)[4]) noexcept {
  rational_jet matrix[4][4]{};
  for (std::uint8_t row = 0; row < 4; ++row) {
    for (std::uint8_t column = 0; column < 4; ++column) {
      if (!quotient_jet(connection.numerator[row][column], connection.denominator,
              point, matrix[row][column])) { return false; }
    }
  }
  exact::small_rational rows[5][4][5]{};
  for (auto& level : rows) {
    for (auto& row : level) { expression_exact_detail::clear(row); }
  }
  rows[0][0][0] = expression_exact_detail::one();
  for (std::uint8_t level = 0; level < 4; ++level) {
    const auto jet_count = static_cast<std::uint8_t>(3U - level);
    for (std::uint8_t target = 0; target < 4; ++target) {
      for (std::uint8_t jet = 0; jet <= jet_count; ++jet) {
        auto sum = expression_exact_detail::zero();
        if (!expression_exact_detail::multiply(rows[level][target][jet + 1U],
                {static_cast<std::int64_t>(jet + 1U), 1}, sum)) { return false; }
        for (std::uint8_t source = 0; source < 4; ++source) {
          for (std::uint8_t split = 0; split <= jet; ++split) {
            exact::small_rational product{}; exact::small_rational next{};
            if (!expression_exact_detail::multiply(rows[level][source][split],
                    matrix[source][target].coefficients[jet - split], product) ||
                !expression_exact_detail::add(sum, product, next)) { return false; }
            sum = next;
          }
        }
        rows[level + 1U][target][jet] = sum;
      }
    }
  }
  exact::small_rational system[9][10]{};
  expression_exact_detail::clear(system);
  for (std::uint8_t component = 0; component < 4; ++component) {
    for (std::uint8_t derivative = 0; derivative < 4; ++derivative) {
      system[component][derivative] = rows[derivative][component][0];
    }
    system[component][4] = rows[4][component][0];
  }
  exact::small_rational solution[9]{};
  if (!expression_exact_detail::solve(system, 4, solution)) { return false; }
  for (std::uint8_t slot = 0; slot < 4; ++slot) { coefficients[slot] = solution[slot]; }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t lcm(
    std::int64_t left, std::int64_t right, bool& exact) noexcept {
  const auto divisor = exact::small_rational_law::gcd(left, right);
  std::int64_t quotient = 0; std::int64_t result = 0;
  exact = exact && blind_integer_detail::divide_exact(left, divisor, quotient) &&
      blind_integer_detail::multiply(quotient, right, result); return result;
}

HOLONICS_CALLABLE constexpr void derive(expression_presentation_receipt& out) noexcept {
  bool exact = out.connection.exact; std::int64_t clearance = 1;
  exact::small_rational values[4]{}; exact::small_rational scalar[4]{};
  exact::small_rational discriminant{};
  exact = scalar_at(out.connection, 1, scalar) && expression_exact_detail::evaluate(
      out.ideal.resultant, {1,1}, discriminant);
  for (std::uint8_t slot = 0; slot < 4 && exact; ++slot) {
    exact = expression_exact_detail::multiply(scalar[slot], discriminant, values[slot]);
    clearance = lcm(clearance, values[slot].denominator, exact);
  }
  out.scalar.identity = exact::word{194'700}; out.scalar.lineage =
      exact::word{out.lineage.value() + 384U};
  exact = exact && expression_exact_detail::scale_polynomial(
      out.ideal.resultant, clearance, out.scalar.coefficients[4]);
  for (std::uint8_t slot = 0; slot < 4; ++slot) {
    exact::small_rational scaled{}; exact::small_rational negative{};
    exact = exact && expression_exact_detail::multiply(values[slot],
        {clearance,1}, scaled) && expression_exact_detail::negate(scaled, negative) &&
        negative.denominator == 1;
    out.scalar.coefficients[slot].coefficients[slot + 1U] = negative.numerator;
    expression_exact_detail::normalize(out.scalar.coefficients[slot]);
  }
  const std::int64_t holdouts[2]{-1,5};
  for (const auto point : holdouts) {
    exact::small_rational held_scalar[4]{}; exact::small_rational held_discriminant{};
    exact = exact && scalar_at(out.connection, point, held_scalar) &&
        expression_exact_detail::evaluate(out.ideal.resultant, {point,1}, held_discriminant);
    for (std::uint8_t slot = 0; slot < 4 && exact; ++slot) {
      exact::small_rational expected{}; exact::small_rational scaled{};
      exact = expression_exact_detail::evaluate(out.scalar.coefficients[slot], {point,1}, expected) &&
          expression_exact_detail::multiply(held_scalar[slot], held_discriminant, scaled) &&
          expression_exact_detail::multiply(scaled, {clearance,1}, scaled) &&
          expression_exact_detail::negate(scaled, scaled) &&
          expression_exact_detail::equal(expected, scaled);
    }
  }
  out.scalar.order = 4; out.scalar.cyclic_vector_exact = exact;
  out.scalar.primitive = exact; out.scalar.holdouts_exact = exact; out.scalar.exact = exact;
}

}  // namespace holonics::organ::expression_cyclic_detail
