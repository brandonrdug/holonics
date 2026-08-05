#pragma once

#include <holonics/organ/algebraic_variation_receipt.hpp>

namespace holonics::organ::variation_polynomial_detail {

namespace rational = exact::small_rational_law;

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_foundation(
    const algebraic_variation_foundation& foundation) noexcept {
  const auto& card = foundation.card;
  return card.parsed && card.schema == exact::word{240'024} && card.degree == 3 &&
      card.cover_degree == 2 && card.sample_count >= 5 &&
      card.sample_count <= variation_sample_capacity && card.discovery_count >= 3 &&
      card.discovery_count < card.sample_count && card.root_min <= card.root_max &&
      card.form_min <= card.form_max && card.series_depth > 0 &&
      card.series_depth < variation_series_capacity && foundation.ecology.value() != 0 &&
      foundation.family.value() != 0 && foundation.differential.value() != 0 &&
      foundation.connection.value() != 0 && foundation.invariant.value() != 0 &&
      foundation.loop.value() != 0 && foundation.theorem.value() != 0 &&
      foundation.provenance.value() != 0;
}

HOLONICS_CALLABLE constexpr void normalize(parameter_polynomial& value) noexcept {
  std::uint8_t degree = static_cast<std::uint8_t>(variation_polynomial_capacity - 1U);
  while (degree != 0 && value.coefficients[degree] == 0) { --degree; }
  value.degree = degree; value.exact = true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr parameter_polynomial affine(
    affine_integer_coefficient value) noexcept {
  parameter_polynomial result{};
  result.coefficients[0] = value.constant;
  result.coefficients[1] = value.parameter;
  normalize(result); return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr parameter_polynomial add(
    const parameter_polynomial& left, const parameter_polynomial& right) noexcept {
  parameter_polynomial result{};
  for (std::uint8_t slot = 0; slot < variation_polynomial_capacity; ++slot) {
    result.coefficients[slot] = left.coefficients[slot] + right.coefficients[slot];
  }
  normalize(result); return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr parameter_polynomial scale(
    const parameter_polynomial& source, std::int64_t factor) noexcept {
  parameter_polynomial result{};
  for (std::uint8_t slot = 0; slot < variation_polynomial_capacity; ++slot) {
    result.coefficients[slot] = source.coefficients[slot] * factor;
  }
  normalize(result); return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr parameter_polynomial subtract(
    const parameter_polynomial& left, const parameter_polynomial& right) noexcept {
  return add(left, scale(right, -1));
}

[[nodiscard]] HOLONICS_CALLABLE constexpr parameter_polynomial multiply(
    const parameter_polynomial& left, const parameter_polynomial& right) noexcept {
  parameter_polynomial result{};
  for (std::uint8_t row = 0; row <= left.degree; ++row) {
    for (std::uint8_t column = 0; column <= right.degree; ++column) {
      const auto target = static_cast<std::uint8_t>(row + column);
      if (target < variation_polynomial_capacity) {
        result.coefficients[target] += left.coefficients[row] * right.coefficients[column];
      }
    }
  }
  normalize(result); return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr parameter_polynomial power(
    parameter_polynomial base, std::uint8_t exponent) noexcept {
  parameter_polynomial result{}; result.coefficients[0] = 1; normalize(result);
  for (std::uint8_t count = 0; count < exponent; ++count) {
    result = multiply(result, base);
  }
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr exact::small_rational evaluate(
    const parameter_polynomial& polynomial, exact::small_rational point) noexcept {
  auto result = rational::make(0);
  for (std::uint8_t offset = 0; offset <= polynomial.degree; ++offset) {
    const auto slot = static_cast<std::uint8_t>(polynomial.degree - offset);
    result = rational::add(rational::multiply(result, point),
        rational::make(polynomial.coefficients[slot]));
  }
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal(
    const parameter_polynomial& left, const parameter_polynomial& right) noexcept {
  for (std::uint8_t slot = 0; slot < variation_polynomial_capacity; ++slot) {
    if (left.coefficients[slot] != right.coefficients[slot]) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool zero(
    const parameter_polynomial& value) noexcept {
  return value.degree == 0 && value.coefficients[0] == 0;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr parameter_polynomial discriminant(
    const algebraic_variation_card& card) noexcept {
  const auto d = affine(card.coefficients[0]);
  const auto c = affine(card.coefficients[1]);
  const auto b = affine(card.coefficients[2]);
  const auto a = affine(card.coefficients[3]);
  auto result = multiply(multiply(b, b), multiply(c, c));
  result = add(result, scale(multiply(a, multiply(multiply(c, c), c)), -4));
  result = add(result, scale(multiply(multiply(multiply(b, b), b), d), -4));
  result = add(result, scale(multiply(multiply(a, a), multiply(d, d)), -27));
  result = add(result, scale(multiply(multiply(multiply(a, b), c), d), 18));
  normalize(result); return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr parameter_polynomial substitute_root(
    const algebraic_variation_card& card, affine_integer_coefficient root) noexcept {
  const auto root_polynomial = affine(root);
  parameter_polynomial result{}; normalize(result);
  for (std::uint8_t coefficient = 0; coefficient <= card.degree; ++coefficient) {
    result = add(result, multiply(affine(card.coefficients[coefficient]),
        power(root_polynomial, coefficient)));
  }
  return result;
}

HOLONICS_CALLABLE constexpr void derive_roots(const algebraic_variation_card& card,
    algebraic_variation_receipt& out) noexcept {
  for (std::int8_t constant = card.root_min; constant <= card.root_max; ++constant) {
    for (std::int8_t parameter = card.root_min; parameter <= card.root_max; ++parameter) {
      const affine_integer_coefficient candidate{constant, parameter};
      if (zero(substitute_root(card, candidate)) && out.root_count < variation_root_capacity) {
        auto& root = out.roots[out.root_count]; root.root = candidate;
        root.identity = exact::word{191'400U + out.root_count};
        root.lineage = exact::word{card.lineage.value() + out.root_count + 1U};
        root.coefficientwise_zero = true; ++out.root_count;
      }
    }
  }
  out.roots_exact = out.root_count == card.degree;
}

HOLONICS_CALLABLE constexpr void derive_vandermonde(
    algebraic_variation_receipt& out) noexcept {
  parameter_polynomial result{}; result.coefficients[0] = 1; normalize(result);
  for (std::uint8_t left = 0; left < out.root_count; ++left) {
    for (std::uint8_t right = static_cast<std::uint8_t>(left + 1U);
        right < out.root_count; ++right) {
      const affine_integer_coefficient difference{
          out.roots[left].root.constant - out.roots[right].root.constant,
          out.roots[left].root.parameter - out.roots[right].root.parameter};
      result = multiply(result, power(affine(difference), 2));
    }
  }
  out.vandermonde_square = result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t root_multiplicity(
    const parameter_polynomial& polynomial, std::int64_t root) noexcept {
  std::int64_t coefficients[variation_polynomial_capacity]{};
  for (std::uint8_t slot = 0; slot <= polynomial.degree; ++slot) {
    coefficients[slot] = polynomial.coefficients[slot];
  }
  std::uint8_t degree = polynomial.degree; std::uint8_t multiplicity = 0;
  while (degree != 0) {
    std::int64_t quotient[variation_polynomial_capacity]{};
    quotient[degree - 1U] = coefficients[degree];
    for (std::uint8_t offset = 1; offset < degree; ++offset) {
      const auto slot = static_cast<std::uint8_t>(degree - 1U - offset);
      quotient[slot] = coefficients[slot + 1U] + root * quotient[slot + 1U];
    }
    if (coefficients[0] + root * quotient[0] != 0) { break; }
    for (std::uint8_t slot = 0; slot < degree; ++slot) { coefficients[slot] = quotient[slot]; }
    --degree; ++multiplicity;
  }
  return multiplicity;
}

HOLONICS_CALLABLE constexpr void derive_collisions(
    algebraic_variation_receipt& out) noexcept {
  for (std::uint8_t left = 0; left < out.root_count; ++left) {
    for (std::uint8_t right = static_cast<std::uint8_t>(left + 1U);
        right < out.root_count; ++right) {
      const auto denominator = out.roots[left].root.parameter -
          out.roots[right].root.parameter;
      if (denominator == 0 || out.collision_count == variation_collision_capacity) { continue; }
      const auto numerator = out.roots[right].root.constant -
          out.roots[left].root.constant;
      const auto parameter = rational::make(numerator, denominator);
      if (parameter.denominator != 1) { continue; }
      auto& collision = out.collisions[out.collision_count];
      collision.parameter = parameter; collision.left = left; collision.right = right;
      collision.multiplicity = root_multiplicity(out.discriminant, parameter.numerator);
      collision.identity = exact::word{191'420U + out.collision_count};
      collision.lineage = exact::word{out.mounted.lineage.value() + 32U + out.collision_count};
      collision.ordered = true; collision.exact = collision.multiplicity != 0;
      ++out.collision_count;
    }
  }
}

HOLONICS_CALLABLE constexpr void derive_family(
    const algebraic_variation_foundation& foundation,
    algebraic_variation_receipt& out) noexcept {
  out.mounted = foundation.card;
  if (!valid_foundation(foundation)) { return; }
  out.discriminant = discriminant(foundation.card);
  derive_roots(foundation.card, out); derive_vandermonde(out); derive_collisions(out);
  for (std::uint8_t collision = 0; collision < out.collision_count; ++collision) {
    out.foils.squarefree_multiplicity_rejected =
        out.foils.squarefree_multiplicity_rejected ||
        out.collisions[collision].multiplicity > 1;
  }
  out.discriminant_exact = equal(out.discriminant, out.vandermonde_square);
  out.obstruction = out.discriminant_exact && out.roots_exact ? variation_obstruction::none :
      variation_obstruction::root_section_refused;
}

}  // namespace holonics::organ::variation_polynomial_detail
