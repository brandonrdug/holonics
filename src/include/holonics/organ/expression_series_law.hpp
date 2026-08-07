#pragma once

#include <holonics/organ/expression_cyclic_law.hpp>

namespace holonics::organ::expression_series_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t falling(
    std::uint8_t value, std::uint8_t degree, bool& exact) noexcept {
  if (value < degree) { return 0; }
  std::int64_t result = 1;
  for (std::uint8_t slot = 0; slot < degree; ++slot) {
    std::int64_t next = 0; exact = exact && blind_integer_detail::multiply(
        result, static_cast<std::int64_t>(value - slot), next); result = next;
  }
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool derive_series(
    expression_scalar_receipt& scalar, std::uint8_t depth) noexcept {
  bool exact = scalar.exact && depth == expression_series_capacity;
  for (auto& front : scalar.series) { expression_exact_detail::clear(front); }
  for (std::uint8_t front = 0; front < 4; ++front) {
    scalar.series[front][front] = {1,1};
    for (std::uint8_t target = 0; target + 4U < depth && exact; ++target) {
      auto sum = expression_exact_detail::zero();
      for (std::uint8_t derivative = 0; derivative <= 4; ++derivative) {
        const auto& polynomial = scalar.coefficients[derivative];
        for (std::uint8_t power = 0; power <= polynomial.degree; ++power) {
          if (derivative == 4 && power == 0) { continue; }
          if (target + derivative < power) { continue; }
          const auto coefficient_index = static_cast<std::uint8_t>(
              target + derivative - power);
          if (coefficient_index >= depth) { continue; }
          bool falling_exact = true; const auto derivative_factor = falling(
              coefficient_index, derivative, falling_exact);
          std::int64_t integer_factor = 0;
          exact::small_rational product{}; exact::small_rational next{};
          exact = exact && falling_exact && blind_integer_detail::multiply(
              polynomial.coefficients[power], derivative_factor, integer_factor) &&
              causal_linear_detail::rational_multiply(
                  scalar.series[front][coefficient_index], {integer_factor,1}, product) &&
              causal_linear_detail::rational_add(sum, product, next);
          sum = next;
        }
      }
      bool falling_exact = true; std::int64_t divisor = 0;
      const auto factor = falling(static_cast<std::uint8_t>(target + 4U), 4, falling_exact);
      exact::small_rational denominator{}; exact::small_rational negative{};
      exact = exact && falling_exact && blind_integer_detail::multiply(
          scalar.coefficients[4].coefficients[0], factor, divisor) &&
          causal_linear_detail::rational_make(divisor, denominator) &&
          causal_linear_detail::rational_negate(sum, negative) &&
          causal_linear_detail::rational_divide(negative, denominator,
              scalar.series[front][target + 4U]);
    }
  }
  scalar.series_count = depth; scalar.recurrence_exact = exact; return exact;
}

HOLONICS_CALLABLE constexpr void add_falling(std::int64_t (&out)[5],
    std::uint8_t degree, std::int64_t scale, bool& exact) noexcept {
  std::int64_t polynomial[5]{1,0,0,0,0}; std::uint8_t current = 0;
  for (std::uint8_t root = 0; root < degree; ++root) {
    std::int64_t next[5]{};
    for (std::uint8_t slot = 0; slot <= current; ++slot) {
      std::int64_t held = 0;
      exact = exact && blind_integer_detail::multiply(polynomial[slot],
          -static_cast<std::int64_t>(root), held) && blind_integer_detail::add(
          next[slot], held, next[slot]) && blind_integer_detail::add(
          next[slot + 1U], polynomial[slot], next[slot + 1U]);
    }
    ++current;
    for (std::uint8_t slot = 0; slot < 5; ++slot) { polynomial[slot] = next[slot]; }
  }
  for (std::uint8_t slot = 0; slot < 5; ++slot) {
    std::int64_t held = 0; exact = exact && blind_integer_detail::multiply(
        polynomial[slot], scale, held) && blind_integer_detail::add(out[slot], held, out[slot]);
  }
}

HOLONICS_CALLABLE constexpr void normalize(std::int64_t (&value)[5]) noexcept {
  std::int64_t divisor = 0;
  for (const auto coefficient : value) {
    if (coefficient != 0) { divisor = divisor == 0 ?
        exact::small_rational_law::absolute(coefficient) :
        exact::small_rational_law::gcd(divisor, coefficient); }
  }
  if (divisor == 0) { return; }
  if (value[4] < 0) { divisor = -divisor; }
  for (auto& coefficient : value) {
    coefficient = exact::small_rational_law::quotient(coefficient, divisor);
  }
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool evaluate_rational(
    const exact::small_rational (&polynomial)[5], std::uint8_t degree,
    exact::small_rational point, exact::small_rational& out) noexcept {
  out = polynomial[degree];
  for (std::uint8_t offset = 0; offset < degree; ++offset) {
    const auto slot = static_cast<std::uint8_t>(degree - 1U - offset);
    exact::small_rational product{}; exact::small_rational next{};
    if (!causal_linear_detail::rational_multiply(out, point, product) ||
        !causal_linear_detail::rational_add(product, polynomial[slot], next)) { return false; }
    out = next;
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool factor_roots(
    const std::int64_t (&source)[5], exact::small_rational (&roots)[4]) noexcept {
  exact::small_rational work[5]{};
  for (std::uint8_t slot = 0; slot < 5; ++slot) {
    if (!causal_linear_detail::rational_make(source[slot], work[slot])) { return false; }
  }
  std::uint8_t degree = 4; std::uint8_t count = 0;
  while (degree != 0) {
    bool found = false;
    for (std::int8_t denominator = 1; denominator <= 8 && !found; ++denominator) {
      for (std::int8_t numerator = -40; numerator <= 40 && !found; ++numerator) {
        const auto candidate = exact::small_rational_law::make(numerator, denominator);
        if (candidate.numerator != numerator) { continue; }
        exact::small_rational value{};
        if (!evaluate_rational(work, degree, candidate, value)) { return false; }
        if (value.numerator != 0) { continue; }
        exact::small_rational quotient[5]{}; quotient[degree - 1U] = work[degree];
        for (std::uint8_t offset = 1; offset < degree; ++offset) {
          const auto slot = static_cast<std::uint8_t>(degree - 1U - offset);
          exact::small_rational product{};
          if (!causal_linear_detail::rational_multiply(candidate,
                  quotient[slot + 1U], product) ||
              !causal_linear_detail::rational_add(work[slot + 1U], product,
                  quotient[slot])) { return false; }
        }
        roots[count] = candidate; ++count; --degree;
        for (std::uint8_t slot = 0; slot < 5; ++slot) { work[slot] = quotient[slot]; }
        found = true;
      }
    }
    if (!found) { return false; }
  }
  return count == 4;
}

HOLONICS_CALLABLE constexpr void derive_indicial(expression_presentation_receipt& out) noexcept {
  auto& receipt = out.indicial; bool exact = out.scalar.exact;
  const auto leading = out.scalar.coefficients[4].coefficients[5];
  const auto third = out.scalar.coefficients[3].coefficients[4];
  std::int64_t derivative = 0; std::int64_t ratio = 0;
  exact = exact && blind_integer_detail::multiply(leading, 5, derivative) &&
      blind_integer_detail::divide_exact(third, derivative, ratio);
  add_falling(receipt.finite_coefficients, 4, 1, exact);
  add_falling(receipt.finite_coefficients, 3, ratio, exact);
  for (std::uint8_t order = 0; order <= 4; ++order) {
    const auto& polynomial = out.scalar.coefficients[order];
    if (polynomial.degree == order + 1U) {
      add_falling(receipt.infinity_coefficients, order,
          polynomial.coefficients[polynomial.degree], exact);
    }
  }
  normalize(receipt.finite_coefficients); normalize(receipt.infinity_coefficients);
  receipt.finite_factored = exact && factor_roots(
      receipt.finite_coefficients, receipt.finite_roots);
  receipt.infinity_factored = exact && factor_roots(
      receipt.infinity_coefficients, receipt.infinity_roots);
  receipt.repeated_finite_root = receipt.finite_roots[0].numerator == 0 &&
      receipt.finite_roots[1].numerator == 0;
  receipt.regular_singular = receipt.finite_factored && receipt.infinity_factored;
  receipt.identity = exact::word{194'720}; receipt.lineage = exact::word{out.lineage.value() + 448U};
  receipt.exact = exact && receipt.repeated_finite_root && receipt.regular_singular;
}

HOLONICS_CALLABLE constexpr void derive(expression_presentation_receipt& out,
    std::uint8_t depth) noexcept {
  const bool series = derive_series(out.scalar, depth); derive_indicial(out);
  out.scalar.exact = out.scalar.exact && series; out.exact = out.ideal.exact &&
      out.connection.exact && out.scalar.exact && out.indicial.exact;
}

}  // namespace holonics::organ::expression_series_detail
