#pragma once

#include <cstdint>

#include <holonics/organ/arithmetic_field_law.hpp>
#include <holonics/organ/arithmetic_spectral_receipt.hpp>

namespace holonics::organ::arithmetic_curve_detail {

[[nodiscard]] HOLONICS_CALLABLE inline const extension_field_spec& field_for(
    const arithmetic_spectral_receipt& inquiry, std::uint16_t prime, std::uint8_t degree) noexcept {
  const std::uint8_t tower = prime == 5 ? 0 : 1;
  return inquiry.towers[tower].fields[degree - 1U];
}

[[nodiscard]] HOLONICS_CALLABLE inline extension_field_element curve_rhs(
    const extension_field_element& x, std::uint16_t coefficient,
    const extension_field_spec& field) noexcept {
  const auto square = arithmetic_field_detail::multiply(x, x, field);
  const auto cube = arithmetic_field_detail::multiply(square, x, field);
  auto scalar = extension_field_element{}; scalar.coefficient[0] = coefficient;
  return arithmetic_field_detail::add(cube,
      arithmetic_field_detail::multiply(scalar, x, field), field);
}

[[nodiscard]] HOLONICS_CALLABLE inline bool on_curve(
    const elliptic_point& point, std::uint16_t coefficient,
    const extension_field_spec& field) noexcept {
  return point.infinite || arithmetic_field_detail::equal(
      arithmetic_field_detail::multiply(point.y, point.y, field),
      curve_rhs(point.x, coefficient, field), field);
}

[[nodiscard]] HOLONICS_CALLABLE inline bool point_equal(
    const elliptic_point& left, const elliptic_point& right,
    const extension_field_spec& field) noexcept {
  if (left.infinite || right.infinite) { return left.infinite == right.infinite; }
  return arithmetic_field_detail::equal(left.x, right.x, field) &&
      arithmetic_field_detail::equal(left.y, right.y, field);
}

[[nodiscard]] HOLONICS_CALLABLE inline elliptic_point point_negate(
    elliptic_point value, const extension_field_spec& field) noexcept {
  if (!value.infinite) { value.y = arithmetic_field_detail::negate(value.y, field); }
  return value;
}

[[nodiscard]] HOLONICS_CALLABLE inline elliptic_point point_add(
    const elliptic_point& left, const elliptic_point& right, std::uint16_t coefficient,
    const extension_field_spec& field) noexcept {
  if (left.infinite) { return right; }
  if (right.infinite) { return left; }
  const auto y_sum = arithmetic_field_detail::add(left.y, right.y, field);
  if (arithmetic_field_detail::equal(left.x, right.x, field) &&
      arithmetic_field_detail::zero(y_sum, field)) { return {{},{},true}; }
  extension_field_element slope{};
  if (arithmetic_field_detail::equal(left.x, right.x, field)) {
    if (arithmetic_field_detail::zero(left.y, field)) { return {{},{},true}; }
    auto three = extension_field_element{}; three.coefficient[0] = 3;
    auto two = extension_field_element{}; two.coefficient[0] = 2;
    auto c = extension_field_element{}; c.coefficient[0] = coefficient;
    const auto numerator = arithmetic_field_detail::add(
        arithmetic_field_detail::multiply(three,
          arithmetic_field_detail::multiply(left.x, left.x, field), field), c, field);
    slope = arithmetic_field_detail::divide(numerator,
        arithmetic_field_detail::multiply(two, left.y, field), field);
  } else {
    slope = arithmetic_field_detail::divide(
        arithmetic_field_detail::add(right.y,
          arithmetic_field_detail::negate(left.y, field), field),
        arithmetic_field_detail::add(right.x,
          arithmetic_field_detail::negate(left.x, field), field), field);
  }
  const auto x3 = arithmetic_field_detail::add(
      arithmetic_field_detail::add(arithmetic_field_detail::multiply(slope, slope, field),
        arithmetic_field_detail::negate(left.x, field), field),
      arithmetic_field_detail::negate(right.x, field), field);
  const auto y3 = arithmetic_field_detail::add(
      arithmetic_field_detail::multiply(slope,
        arithmetic_field_detail::add(left.x,
          arithmetic_field_detail::negate(x3, field), field), field),
      arithmetic_field_detail::negate(left.y, field), field);
  return {x3,y3,false};
}

[[nodiscard]] HOLONICS_CALLABLE inline elliptic_point scalar_multiply(
    std::int8_t scalar, elliptic_point point, std::uint16_t coefficient,
    const extension_field_spec& field) noexcept {
  std::int16_t magnitude = scalar;
  if (magnitude < 0) { magnitude = static_cast<std::int16_t>(-magnitude); point = point_negate(point, field); }
  elliptic_point result{{},{},true};
  while (magnitude != 0) {
    if ((magnitude & 1) != 0) { result = point_add(result, point, coefficient, field); }
    magnitude >>= 1;
    if (magnitude != 0) { point = point_add(point, point, coefficient, field); }
  }
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE inline elliptic_point frobenius(
    elliptic_point point, const extension_field_spec& field) noexcept {
  if (!point.infinite) {
    point.x = arithmetic_field_detail::power(point.x, field.prime, field);
    point.y = arithmetic_field_detail::power(point.y, field.prime, field);
  }
  return point;
}

[[nodiscard]] HOLONICS_CALLABLE inline elliptic_point cm_image(
    elliptic_point point, std::uint16_t imaginary_unit,
    const extension_field_spec& field) noexcept {
  if (point.infinite) { return point; }
  point.x = arithmetic_field_detail::negate(point.x, field);
  auto scalar = extension_field_element{}; scalar.coefficient[0] = imaginary_unit;
  point.y = arithmetic_field_detail::multiply(scalar, point.y, field); return point;
}

[[nodiscard]] HOLONICS_CALLABLE inline elliptic_point gaussian_image(
    elliptic_point point, std::int8_t real, std::int8_t imaginary,
    std::uint16_t coefficient, std::uint16_t imaginary_unit,
    const extension_field_spec& field) noexcept {
  return point_add(scalar_multiply(real, point, coefficient, field),
      scalar_multiply(imaginary, cm_image(point, imaginary_unit, field), coefficient, field),
      coefficient, field);
}

HOLONICS_CALLABLE inline void evaluate_candidate(const arithmetic_spectral_receipt& inquiry,
    std::uint8_t curve, std::uint8_t candidate, correspondence_candidate_receipt& out) noexcept {
  const auto& source = inquiry.curves[curve].source;
  const auto& field = field_for(inquiry, source.prime, 2);
  const auto minimum = inquiry.mounted.candidate_min;
  const auto coordinate = exact::divide_unsigned(candidate, arithmetic_candidate_side);
  const auto real = static_cast<std::int8_t>(minimum +
      static_cast<std::int8_t>(coordinate.quotient));
  const auto imaginary = static_cast<std::int8_t>(minimum +
      static_cast<std::int8_t>(coordinate.remainder));
  out.curve = curve; out.real = real; out.imaginary = imaginary;
  out.norm = static_cast<std::uint32_t>(real * real + imaginary * imaginary);
  out.norm_matches = out.norm == source.prime; out.points_tested = 1;
  const auto q = field.order;
  for (std::uint32_t x = 0; x < q; ++x) {
    for (std::uint32_t y = 0; y < q; ++y) {
      elliptic_point point{arithmetic_field_detail::element(x, field),
          arithmetic_field_detail::element(y, field), false};
      if (!on_curve(point, source.coefficient, field)) { continue; }
      ++out.points_tested;
      const auto expected = frobenius(point, field);
      const auto actual = gaussian_image(point, real, imaginary, source.coefficient,
          inquiry.towers[source.prime == 5 ? 0 : 1].imaginary_unit, field);
      if (!point_equal(expected, actual, field)) { ++out.mismatches; }
    }
  }
  out.lineage = exact::word{source.lineage.value() + 10'000U + candidate};
}

HOLONICS_CALLABLE inline void fixed_contribution(const arithmetic_spectral_receipt& inquiry,
    std::uint8_t curve, std::uint8_t degree, std::uint32_t x_encoding,
    fixed_locus_contribution& out) noexcept {
  const auto& source = inquiry.curves[curve].source;
  const auto& field = field_for(inquiry, source.prime, degree);
  const auto x = arithmetic_field_detail::element(x_encoding, field);
  const auto rhs = curve_rhs(x, source.coefficient, field);
  const auto character = arithmetic_field_detail::character(rhs, field);
  out.curve = curve; out.degree = degree; out.x_encoding = x_encoding;
  out.rhs_encoding = arithmetic_field_detail::encoding(rhs, field);
  out.character = character; out.point_count = static_cast<std::uint8_t>(character + 1);
  out.lineage = exact::word{source.lineage.value() +
      static_cast<std::uint64_t>(degree) * 100'000U + x_encoding};
}

}  // namespace holonics::organ::arithmetic_curve_detail
