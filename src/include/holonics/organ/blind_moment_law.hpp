#pragma once

#include <holonics/organ/blind_polynomial_exact.hpp>

namespace holonics::organ::blind_moment_detail {
[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_case(
    const moment_problem_case& value) noexcept {
  return value.occurrence.value() != 0 && value.degree >= 2 &&
      value.degree <= blind_moment_degree_capacity &&
      value.moment_count <= blind_moment_capacity &&
      value.aperture_min <= value.aperture_max &&
      value.aperture_min >= -32 && value.aperture_max <= 32;
}

HOLONICS_CALLABLE constexpr bool newton_polynomial(
    const moment_problem_case& source,
    std::int64_t (&coefficients)[blind_polynomial_capacity]) noexcept {
  std::int64_t elementary[blind_polynomial_capacity]{};
  elementary[0] = 1;
  for (std::uint8_t degree = 1; degree <= source.degree; ++degree) {
    std::int64_t sum = 0;
    for (std::uint8_t index = 1; index <= degree; ++index) {
      std::int64_t term = 0;
      std::int64_t next = 0;
      if (!blind_integer_detail::multiply(elementary[degree - index],
              source.moments[index], term)) { return false; }
      if ((index & 1U) == 0) { term = -term; }
      if (!blind_integer_detail::add(sum, term, next)) { return false; }
      sum = next;
    }
    if (!blind_integer_detail::divide_exact(sum, static_cast<std::int64_t>(degree),
            elementary[degree])) { return false; }
  }
  coefficients[source.degree] = 1;
  for (std::uint8_t index = 1; index <= source.degree; ++index) {
    coefficients[source.degree - index] = (index & 1U) == 0 ?
        elementary[index] : -elementary[index];
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t discriminant(
    const std::int64_t (&polynomial)[blind_polynomial_capacity],
    std::uint8_t degree, bool& exact) noexcept {
  std::int64_t sylvester[7][7]{};
  const auto derivative_degree = static_cast<std::uint8_t>(degree - 1U);
  const auto size = static_cast<std::uint8_t>(2U * degree - 1U);
  for (std::uint8_t row = 0; row < derivative_degree; ++row) {
    for (std::uint8_t column = 0; column <= degree; ++column) {
      sylvester[row][row + column] = polynomial[degree - column];
    }
  }
  for (std::uint8_t row = 0; row < degree; ++row) {
    for (std::uint8_t column = 0; column <= derivative_degree; ++column) {
      const auto power = static_cast<std::uint8_t>(degree - column);
      sylvester[derivative_degree + row][row + column] =
          static_cast<std::int64_t>(power) * polynomial[power];
    }
  }
  auto value = blind_integer_detail::determinant(sylvester, size, exact);
  if ((degree & std::uint8_t{2}) != 0) { value = -value; }
  return value;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool evaluate(
    const std::int64_t (&polynomial)[blind_polynomial_capacity],
    std::uint8_t degree, std::int64_t point, std::int64_t& value) noexcept {
  value = polynomial[degree];
  for (std::uint8_t offset = degree; offset > 0; --offset) {
    std::int64_t product = 0;
    std::int64_t next = 0;
    if (!blind_integer_detail::multiply(value, point, product) ||
        !blind_integer_detail::add(product, polynomial[offset - 1U], next)) { return false; }
    value = next;
  }
  return true;
}

HOLONICS_CALLABLE constexpr bool remove_root(
    std::int64_t (&polynomial)[blind_polynomial_capacity],
    std::uint8_t& degree, std::int64_t root) noexcept {
  if (degree == 0) { return false; }
  std::int64_t quotient[blind_polynomial_capacity]{};
  quotient[degree - 1U] = polynomial[degree];
  for (std::uint8_t index = static_cast<std::uint8_t>(degree - 1U); index > 0; --index) {
    std::int64_t product = 0;
    if (!blind_integer_detail::multiply(quotient[index], root, product) ||
        !blind_integer_detail::add(polynomial[index], product,
            quotient[index - 1U])) { return false; }
  }
  std::int64_t remainder = 0;
  if (!blind_integer_detail::multiply(quotient[0], root, remainder) ||
      !blind_integer_detail::add(remainder, polynomial[0], remainder) || remainder != 0) {
    return false;
  }
  --degree;
  for (std::uint8_t slot = 0; slot <= degree; ++slot) { polynomial[slot] = quotient[slot]; }
  polynomial[degree + 1U] = 0;
  return true;
}

HOLONICS_CALLABLE constexpr blind_candidate_receipt candidate(
    blind_candidate_kind kind, const moment_problem_case& source,
    const std::int64_t (&newton)[blind_polynomial_capacity],
    std::int64_t discriminant_value, std::uint8_t slot) noexcept {
  blind_candidate_receipt out{};
  out.kind = kind;
  out.identity = exact::word{189'600U + static_cast<std::uint64_t>(slot) * 10U +
      static_cast<std::uint8_t>(kind)};
  out.lineage = source.occurrence.value() + out.identity.value();
  out.access_complete = source.moment_count >= 2U * source.degree;
  if (!out.access_complete) { return out; }
  std::int64_t base[blind_moment_degree_capacity][blind_moment_degree_capacity]{};
  std::int64_t shifted[blind_moment_degree_capacity][blind_moment_degree_capacity]{};
  std::uint8_t size = source.degree;
  if (kind == blind_candidate_kind::collapsed_degree) { --size; }
  for (std::uint8_t row = 0; row < size; ++row) {
    for (std::uint8_t column = 0; column < size; ++column) {
      std::uint8_t index = static_cast<std::uint8_t>(row + column);
      if (kind == blind_candidate_kind::toeplitz) {
        index = row > column ? static_cast<std::uint8_t>(row - column) :
            static_cast<std::uint8_t>(column - row);
      } else if (kind == blind_candidate_kind::reversed_hankel) {
        index = static_cast<std::uint8_t>(2U * source.degree - 2U - row - column);
      }
      base[row][column] = source.moments[index];
      shifted[row][column] = source.moments[index + 1U];
    }
  }
  const auto pencil = blind_polynomial_detail::determinant_pencil(base, shifted, size);
  bool determinant_exact = false;
  const auto determinant = blind_integer_detail::determinant(base, size, determinant_exact);
  out.recurrence_exact = pencil.exact && determinant_exact && determinant != 0 &&
      pencil.degree == source.degree;
  if (out.recurrence_exact) {
    for (std::uint8_t coefficient = 0; coefficient <= source.degree; ++coefficient) {
      std::int64_t quotient = 0;
      out.recurrence_exact = out.recurrence_exact && blind_integer_detail::divide_exact(
          pencil.coefficients[coefficient], determinant, quotient) &&
          quotient == newton[coefficient];
    }
  }
  out.contact_exact = out.recurrence_exact;
  out.source_order_exact = kind == blind_candidate_kind::hankel;
  out.separable = discriminant_value != 0;
  out.admitted = out.access_complete && out.recurrence_exact && out.contact_exact &&
      out.source_order_exact && out.separable;
  return out;
}

HOLONICS_CALLABLE constexpr void form_moment_root(const moment_problem_case& source,
    std::uint8_t slot, moment_root_receipt& out) noexcept {
  out.identity = exact::word{189'450U + slot};
  out.lineage = source.occurrence.value() + out.identity.value();
  out.degree = source.degree;
  if (!valid_case(source)) { return; }
  out.access_complete = source.moment_count >= 2U * source.degree;
  if (!out.access_complete) {
    out.obstruction = blind_obstruction::moment_access_refused;
    out.exact = true;
    return;
  }
  for (std::uint8_t row = 0; row < source.degree; ++row) {
    for (std::uint8_t column = 0; column < source.degree; ++column) {
      out.hankel[row][column] = source.moments[row + column];
      out.shifted[row][column] = source.moments[row + column + 1U];
    }
  }
  bool determinant_exact = false;
  out.hankel_determinant = blind_integer_detail::determinant(
      out.hankel, source.degree, determinant_exact);
  const bool newton_exact = newton_polynomial(source, out.newton);
  const auto pencil = blind_polynomial_detail::determinant_pencil(
      out.hankel, out.shifted, source.degree);
  for (std::uint8_t index = 0; index <= source.degree; ++index) {
    out.pencil[index] = pencil.coefficients[index];
  }
  bool discriminant_exact = false;
  out.discriminant = discriminant(out.newton, source.degree, discriminant_exact);
  out.pencil_newton_agree = determinant_exact && newton_exact && pencil.exact &&
      out.hankel_determinant != 0 && pencil.degree == source.degree;
  if (out.pencil_newton_agree) {
    for (std::uint8_t coefficient = 0; coefficient <= source.degree; ++coefficient) {
      std::int64_t quotient = 0;
      out.pencil_newton_agree = out.pencil_newton_agree &&
          blind_integer_detail::divide_exact(out.pencil[coefficient],
              out.hankel_determinant, quotient) &&
          quotient == out.newton[coefficient];
    }
  }
  out.separable = discriminant_exact && out.discriminant != 0;
  for (std::uint8_t candidate_slot = 0; candidate_slot < blind_candidate_capacity;
      ++candidate_slot) {
    const blind_candidate_kind kinds[blind_candidate_capacity]{blind_candidate_kind::hankel,
        blind_candidate_kind::toeplitz, blind_candidate_kind::reversed_hankel,
        blind_candidate_kind::collapsed_degree};
    out.candidates[candidate_slot] = candidate(kinds[candidate_slot], source,
        out.newton, out.discriminant, slot);
  }
  if (!out.separable) {
    out.obstruction = blind_obstruction::singular_root_fiber;
    out.exact = newton_exact && discriminant_exact && out.hankel_determinant == 0 &&
        out.discriminant == 0 && !out.candidates[0].admitted;
    return;
  }
  std::int64_t remaining[blind_polynomial_capacity]{};
  for (std::uint8_t index = 0; index <= source.degree; ++index) {
    remaining[index] = out.newton[index];
  }
  std::uint8_t remaining_degree = source.degree;
  for (std::int16_t root = source.aperture_min; root <= source.aperture_max; ++root) {
    std::int64_t value = 0;
    if (!evaluate(remaining, remaining_degree, root, value)) { return; }
    if (value == 0 && out.root_count < source.degree) {
      out.roots[out.root_count++] = root;
      if (!remove_root(remaining, remaining_degree, root)) { return; }
    }
  }
  out.roots_remove_exactly = out.root_count == source.degree && remaining_degree == 0 &&
      remaining[0] == 1;
  std::int64_t square = 1;
  bool square_exact = true;
  for (std::uint8_t left = 0; left < out.root_count; ++left) {
    for (std::uint8_t right = static_cast<std::uint8_t>(left + 1U);
        right < out.root_count; ++right) {
      std::int64_t difference = 0;
      std::int64_t term = 0;
      square_exact = square_exact && blind_integer_detail::subtract(
          out.roots[left], out.roots[right], difference) &&
          blind_integer_detail::multiply(difference, difference, term) &&
          blind_integer_detail::multiply(square, term, square);
    }
  }
  out.vandermonde_square = square_exact && square == out.hankel_determinant &&
      square == out.discriminant;
  out.obstruction = blind_obstruction::none;
  out.exact = out.pencil_newton_agree && out.roots_remove_exactly &&
      out.vandermonde_square && out.candidates[0].admitted;
}
}  // namespace holonics::organ::blind_moment_detail
