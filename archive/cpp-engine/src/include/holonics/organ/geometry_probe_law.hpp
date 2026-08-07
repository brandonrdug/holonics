#pragma once

#include <holonics/organ/geometry_inquiry_exact.hpp>
#include <holonics/organ/geometry_inquiry_receipt.hpp>

namespace holonics::organ {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_geometry_inquiry_foundation(
    const geometry_inquiry_foundation& value) noexcept {
  return value.ecology.value() != 0 && value.swing_construction.value() != 0 &&
      value.fractional_chart.value() != 0 &&
      value.commutative_ring_operations.value() != 0 && value.field_quotient.value() != 0 &&
      value.provenance.value() != 0 && value.probe_seed.value() != 0 &&
      value.probe_count == geometry_inquiry_probe_capacity;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool swing_pair(
    const std::uint64_t* points, inquiry_ratio_pair& pair) noexcept {
  using namespace geometry_inquiry_detail;
  std::uint64_t ca = 0;
  std::uint64_t db = 0;
  std::uint64_t cb = 0;
  std::uint64_t da = 0;
  std::uint64_t first = 0;
  std::uint64_t second = 0;
  return difference(points[2], points[0], ca) && difference(points[3], points[1], db) &&
      difference(points[2], points[1], cb) && difference(points[3], points[0], da) &&
      multiply(ca, db, first) && multiply(cb, da, second) &&
      ((pair = {exact::word{first}, exact::word{second}}), true);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr geometry_probe_receipt form_geometry_probe(
    const geometry_inquiry_foundation& foundation, std::uint16_t slot) noexcept {
  using namespace geometry_inquiry_detail;
  geometry_probe_receipt result{};
  result.identity = exact::word{foundation.probe_seed.value() + slot};
  if (!valid_geometry_inquiry_foundation(foundation) || slot >= foundation.probe_count) {
    return result;
  }
  if (slot + 1U == foundation.probe_count) {
    result.points[0] = exact::word{0};
    result.points[1] = exact::word{1};
    result.points[2] = exact::word{2};
    result.points[3] = exact::word{4};
    result.frame[0] = exact::word{3};
    result.frame[1] = exact::word{1};
    result.frame[2] = exact::word{1};
    result.frame[3] = exact::word{0};
    result.quotient_singular = true;
    result.returned = true;
    return result;
  }
  const std::uint64_t a = 1U + slot;
  const std::uint64_t alpha = 3U + slot % 3U;
  const std::uint64_t beta = 1U + slot % 2U;
  const std::uint64_t gamma = 1U;
  const std::uint64_t delta = 20U + slot;
  const std::uint64_t points[4]{a, a + 1U, a + 3U, a + 7U};
  const std::uint64_t frame[4]{alpha, beta, gamma, delta};
  for (std::size_t index = 0; index < 4; ++index) {
    result.points[index] = exact::word{points[index]};
    result.frame[index] = exact::word{frame[index]};
  }
  std::uint64_t positive = 0;
  std::uint64_t negative = 0;
  std::uint64_t determinant = 0;
  if (!multiply(alpha, delta, positive) || !multiply(beta, gamma, negative) ||
      !difference(positive, negative, determinant) || !swing_pair(points, result.original)) {
    return result;
  }
  std::uint64_t numerators[4]{};
  std::uint64_t denominators[4]{};
  for (std::size_t index = 0; index < 4; ++index) {
    if (!multiply(alpha, points[index], numerators[index]) ||
        !add(numerators[index], beta, numerators[index]) ||
        !multiply(gamma, points[index], denominators[index]) ||
        !add(denominators[index], delta, denominators[index])) {
      return result;
    }
  }
  constexpr std::size_t left[4]{2, 3, 2, 3};
  constexpr std::size_t right[4]{0, 1, 1, 0};
  std::uint64_t image_differences[4]{};
  for (std::size_t pair = 0; pair < 4; ++pair) {
    std::uint64_t positive_image = 0;
    std::uint64_t negative_image = 0;
    if (!multiply(numerators[left[pair]], denominators[right[pair]], positive_image) ||
        !multiply(numerators[right[pair]], denominators[left[pair]], negative_image) ||
        !difference(positive_image, negative_image, image_differences[pair])) {
      return result;
    }
  }
  std::uint64_t first = 0;
  std::uint64_t second = 0;
  std::uint64_t square = 0;
  if (!multiply(image_differences[0], image_differences[1], first) ||
      !multiply(image_differences[2], image_differences[3], second) ||
      !multiply(determinant, determinant, square)) {
    return result;
  }
  result.transformed = {exact::word{first}, exact::word{second}};
  result.determinant = exact::word{determinant};
  result.common_square = exact::word{square};
  std::uint64_t projective_left = 0;
  std::uint64_t projective_right = 0;
  if (!multiply(result.original.first.value(), second, projective_left) ||
      !multiply(result.original.second.value(), first, projective_right)) {
    return result;
  }
  result.projectively_equal = projective_left == projective_right;
  result.coordinates_equal = result.original.first == result.transformed.first &&
      result.original.second == result.transformed.second;
  result.returned = first != 0 && second != 0;
  return result;
}

}  // namespace holonics::organ
