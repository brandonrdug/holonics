#pragma once

#include <cstdint>

#include <holonics/exact/integer_division.hpp>
#include <holonics/organ/arithmetic_field_receipt.hpp>

namespace holonics::organ::arithmetic_field_detail {

[[nodiscard]] HOLONICS_CALLABLE inline std::uint16_t reduced(
    std::int64_t value, std::uint16_t prime) noexcept {
  return static_cast<std::uint16_t>(exact::positive_remainder(value, prime));
}

[[nodiscard]] HOLONICS_CALLABLE inline std::uint32_t power_u32(
    std::uint32_t base, std::uint8_t exponent) noexcept {
  std::uint32_t result = 1;
  for (std::uint8_t slot = 0; slot < exponent; ++slot) { result *= base; }
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE inline bool polynomial_divides(
    const std::uint16_t* source, std::uint8_t source_degree,
    const std::uint16_t* divisor, std::uint8_t divisor_degree,
    std::uint16_t prime) noexcept {
  std::uint16_t remainder[arithmetic_degree_count + 1]{};
  for (std::uint8_t slot = 0; slot <= source_degree; ++slot) { remainder[slot] = source[slot]; }
  for (std::int8_t top = static_cast<std::int8_t>(source_degree);
       top >= static_cast<std::int8_t>(divisor_degree); --top) {
    const auto coefficient = remainder[static_cast<std::uint8_t>(top)];
    if (coefficient == 0) { continue; }
    const auto shift = static_cast<std::uint8_t>(top) - divisor_degree;
    for (std::uint8_t slot = 0; slot <= divisor_degree; ++slot) {
      const auto target = static_cast<std::uint8_t>(slot + shift);
      remainder[target] = reduced(static_cast<std::int64_t>(remainder[target]) -
          static_cast<std::int64_t>(coefficient) * divisor[slot], prime);
    }
  }
  for (std::uint8_t slot = 0; slot < divisor_degree; ++slot) {
    if (remainder[slot] != 0) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE inline bool irreducible(
    const std::uint16_t* polynomial, std::uint8_t degree, std::uint16_t prime,
    std::uint32_t& divisor_witness) noexcept {
  for (std::uint8_t divisor_degree = 1; divisor_degree <= (degree >> 1U); ++divisor_degree) {
    const auto count = power_u32(prime, divisor_degree);
    for (std::uint32_t code = 0; code < count; ++code) {
      std::uint32_t remaining = code;
      std::uint16_t divisor[arithmetic_degree_count + 1]{};
      for (std::uint8_t slot = 0; slot < divisor_degree; ++slot) {
        const auto part = exact::divide_unsigned(remaining, prime);
        divisor[slot] = static_cast<std::uint16_t>(part.remainder);
        remaining = static_cast<std::uint32_t>(part.quotient);
      }
      divisor[divisor_degree] = 1;
      if (polynomial_divides(polynomial, degree, divisor, divisor_degree, prime)) {
        divisor_witness = (static_cast<std::uint32_t>(divisor_degree) << 24U) | code;
        return false;
      }
    }
  }
  divisor_witness = 0;
  return true;
}

HOLONICS_CALLABLE inline void discover_tower(
    std::uint16_t prime, exact::word lineage, field_tower_receipt& out) noexcept {
  out.lineage = lineage;
  out.fields[0] = {prime, 1, prime, {0,1,0,0,0}, exact::word{lineage.value() + 1U}, true};
  for (std::uint16_t candidate = 1; candidate < prime; ++candidate) {
    if (reduced(static_cast<std::int64_t>(candidate) * candidate + 1, prime) == 0) {
      out.imaginary_unit = candidate; break;
    }
  }
  for (std::uint8_t degree = 2; degree <= arithmetic_degree_count; ++degree) {
    const auto limit = power_u32(prime, degree);
    bool selected = false;
    for (std::uint32_t code = 1; code < limit && !selected; ++code) {
      std::uint32_t remaining = code;
      std::uint16_t polynomial[arithmetic_degree_count + 1]{};
      for (std::uint8_t slot = 0; slot < degree; ++slot) {
        const auto part = exact::divide_unsigned(remaining, prime);
        polynomial[slot] = static_cast<std::uint16_t>(part.remainder);
        remaining = static_cast<std::uint32_t>(part.quotient);
      }
      polynomial[degree] = 1; std::uint32_t witness = 0;
      const bool exact = irreducible(polynomial, degree, prime, witness);
      if (out.candidate_count >= arithmetic_field_candidate_capacity) { return; }
      auto& receipt = out.candidates[out.candidate_count++];
      receipt.prime = prime; receipt.degree = degree; receipt.code = code;
      receipt.divisor_code = witness; receipt.irreducible = exact;
      receipt.lineage = exact::word{lineage.value() + 100U + out.candidate_count};
      for (std::uint8_t slot = 0; slot <= degree; ++slot) {
        receipt.coefficient[slot] = polynomial[slot];
      }
      if (exact) {
        auto& field = out.fields[degree - 1U]; field.prime = prime; field.degree = degree;
        field.order = power_u32(prime, degree); field.irreducible = true;
        field.lineage = exact::word{lineage.value() + degree};
        for (std::uint8_t slot = 0; slot <= degree; ++slot) {
          field.modulus[slot] = polynomial[slot];
        }
        selected = true;
      }
    }
    if (!selected) { return; }
  }
  out.exact = out.imaginary_unit != 0 && out.fields[1].irreducible &&
      out.fields[2].irreducible && out.fields[3].irreducible;
}

[[nodiscard]] HOLONICS_CALLABLE inline extension_field_element element(
    std::uint32_t encoding, const extension_field_spec& field) noexcept {
  extension_field_element result{};
  for (std::uint8_t slot = 0; slot < field.degree; ++slot) {
    const auto part = exact::divide_unsigned(encoding, field.prime);
    result.coefficient[slot] = static_cast<std::uint16_t>(part.remainder);
    encoding = static_cast<std::uint32_t>(part.quotient);
  }
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE inline std::uint32_t encoding(
    const extension_field_element& value, const extension_field_spec& field) noexcept {
  std::uint32_t result = 0; std::uint32_t place = 1;
  for (std::uint8_t slot = 0; slot < field.degree; ++slot) {
    result += static_cast<std::uint32_t>(value.coefficient[slot]) * place;
    place *= field.prime;
  }
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE inline bool equal(
    const extension_field_element& left, const extension_field_element& right,
    const extension_field_spec& field) noexcept {
  for (std::uint8_t slot = 0; slot < field.degree; ++slot) {
    if (left.coefficient[slot] != right.coefficient[slot]) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE inline bool zero(
    const extension_field_element& value, const extension_field_spec& field) noexcept {
  extension_field_element origin{}; return equal(value, origin, field);
}

[[nodiscard]] HOLONICS_CALLABLE inline extension_field_element add(
    const extension_field_element& left, const extension_field_element& right,
    const extension_field_spec& field) noexcept {
  extension_field_element result{};
  for (std::uint8_t slot = 0; slot < field.degree; ++slot) {
    result.coefficient[slot] = reduced(
        static_cast<std::int64_t>(left.coefficient[slot]) + right.coefficient[slot], field.prime);
  }
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE inline extension_field_element negate(
    const extension_field_element& value, const extension_field_spec& field) noexcept {
  extension_field_element result{};
  for (std::uint8_t slot = 0; slot < field.degree; ++slot) {
    result.coefficient[slot] = reduced(-static_cast<std::int64_t>(value.coefficient[slot]), field.prime);
  }
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE inline extension_field_element multiply(
    const extension_field_element& left, const extension_field_element& right,
    const extension_field_spec& field) noexcept {
  std::int64_t product[2 * arithmetic_degree_count - 1]{};
  for (std::uint8_t row = 0; row < field.degree; ++row) {
    for (std::uint8_t column = 0; column < field.degree; ++column) {
      product[row + column] += static_cast<std::int64_t>(left.coefficient[row]) *
          right.coefficient[column];
    }
  }
  for (std::int8_t top = static_cast<std::int8_t>(2U * field.degree - 2U);
       top >= static_cast<std::int8_t>(field.degree); --top) {
    const auto coefficient = reduced(product[static_cast<std::uint8_t>(top)], field.prime);
    const auto shift = static_cast<std::uint8_t>(top) - field.degree;
    for (std::uint8_t slot = 0; slot < field.degree; ++slot) {
      product[slot + shift] -= static_cast<std::int64_t>(coefficient) * field.modulus[slot];
    }
  }
  extension_field_element result{};
  for (std::uint8_t slot = 0; slot < field.degree; ++slot) {
    result.coefficient[slot] = reduced(product[slot], field.prime);
  }
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE inline extension_field_element power(
    extension_field_element base, std::uint32_t exponent,
    const extension_field_spec& field) noexcept {
  auto result = element(1, field);
  while (exponent != 0) {
    if ((exponent & 1U) != 0) { result = multiply(result, base, field); }
    exponent >>= 1U;
    if (exponent != 0) { base = multiply(base, base, field); }
  }
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE inline extension_field_element inverse(
    const extension_field_element& value, const extension_field_spec& field) noexcept {
  return power(value, field.order - 2U, field);
}

[[nodiscard]] HOLONICS_CALLABLE inline extension_field_element divide(
    const extension_field_element& left, const extension_field_element& right,
    const extension_field_spec& field) noexcept {
  return multiply(left, inverse(right, field), field);
}

[[nodiscard]] HOLONICS_CALLABLE inline std::int8_t character(
    const extension_field_element& value, const extension_field_spec& field) noexcept {
  if (zero(value, field)) { return 0; }
  return equal(power(value, (field.order - 1U) >> 1U, field), element(1, field), field) ? 1 : -1;
}

}  // namespace holonics::organ::arithmetic_field_detail
