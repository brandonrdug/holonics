#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/receiver/geometry_exact.hpp>

namespace holonics::receiver {
namespace swing_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool distinct_four(
    const exact::word* points) noexcept {
  for (std::size_t left = 0; left < geometry_point_count; ++left) {
    for (std::size_t right = left + 1; right < geometry_point_count; ++right) {
      if (points[left] == points[right]) { return false; }
    }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool ordered_pair(
    std::uint64_t left,
    std::uint64_t right,
    std::uint64_t& difference) noexcept {
  if (left < right) { return false; }
  difference = left - right;
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool affine_pair(
    const exact::word* points,
    word_pair& result) noexcept {
  std::uint64_t ca = 0;
  std::uint64_t db = 0;
  std::uint64_t cb = 0;
  std::uint64_t da = 0;
  std::uint64_t first = 0;
  std::uint64_t second = 0;
  return ordered_pair(points[2].value(), points[0].value(), ca) &&
      ordered_pair(points[3].value(), points[1].value(), db) &&
      ordered_pair(points[2].value(), points[1].value(), cb) &&
      ordered_pair(points[3].value(), points[0].value(), da) &&
      geometry_multiply(ca, db, first) && geometry_multiply(cb, da, second) &&
      ((result = {exact::word{first}, exact::word{second}}), true);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool transform_points(
    const projective_swing_program& program,
    std::uint64_t* numerator,
    std::uint64_t* denominator) noexcept {
  for (std::size_t slot = 0; slot < geometry_point_count; ++slot) {
    std::uint64_t ax = 0;
    std::uint64_t cx = 0;
    if (!geometry_multiply(program.frame[0].value(), program.points[slot].value(), ax) ||
        !geometry_multiply(program.frame[2].value(), program.points[slot].value(), cx) ||
        !geometry_add(ax, program.frame[1].value(), numerator[slot]) ||
        !geometry_add(cx, program.frame[3].value(), denominator[slot])) {
      return false;
    }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool determinant(
    std::uint64_t left_numerator,
    std::uint64_t left_denominator,
    std::uint64_t right_numerator,
    std::uint64_t right_denominator,
    std::uint64_t& result) noexcept {
  std::uint64_t positive = 0;
  std::uint64_t negative = 0;
  return geometry_multiply(left_numerator, right_denominator, positive) &&
      geometry_multiply(left_denominator, right_numerator, negative) &&
      ordered_pair(positive, negative, result);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool transformed_pair(
    const projective_swing_program& program,
    word_pair& result) noexcept {
  std::uint64_t numerator[geometry_point_count]{};
  std::uint64_t denominator[geometry_point_count]{};
  std::uint64_t ca = 0;
  std::uint64_t db = 0;
  std::uint64_t cb = 0;
  std::uint64_t da = 0;
  std::uint64_t first = 0;
  std::uint64_t second = 0;
  return transform_points(program, numerator, denominator) &&
      determinant(numerator[2], denominator[2], numerator[0], denominator[0], ca) &&
      determinant(numerator[3], denominator[3], numerator[1], denominator[1], db) &&
      determinant(numerator[2], denominator[2], numerator[1], denominator[1], cb) &&
      determinant(numerator[3], denominator[3], numerator[0], denominator[0], da) &&
      geometry_multiply(ca, db, first) && geometry_multiply(cb, da, second) &&
      ((result = {exact::word{first}, exact::word{second}}), true);
}

}  // namespace swing_detail

[[nodiscard]] HOLONICS_CALLABLE constexpr projective_swing_receipt projective_swing(
    const projective_swing_program& program) noexcept {
  projective_swing_receipt result{};
  result.path = program.path;
  word_pair degenerate{};
  result.degenerate_open = !swing_detail::distinct_four(program.degenerate_points) ||
      !swing_detail::affine_pair(program.degenerate_points, degenerate) ||
      degenerate.first.value() == 0 || degenerate.second.value() == 0;
  result.non_field_open = !program.counterexample_field_carrier;
  if (!program.field_carrier) {
    result.obstruction = geometry_obstruction::non_field_carrier;
    return result;
  }
  if (!swing_detail::distinct_four(program.points) ||
      !swing_detail::affine_pair(program.points, result.original) ||
      !swing_detail::transformed_pair(program, result.transformed) ||
      result.original.first.value() == 0 || result.original.second.value() == 0) {
    result.obstruction = geometry_obstruction::degenerate_swing;
    return result;
  }
  std::uint64_t left = 0;
  std::uint64_t right = 0;
  if (!geometry_multiply(result.original.first.value(), result.transformed.second.value(), left) ||
      !geometry_multiply(result.original.second.value(), result.transformed.first.value(), right)) {
    result.obstruction = geometry_obstruction::invalid_program;
    return result;
  }
  result.projectively_equal = left == right;
  result.frame_changed = result.original.first != result.transformed.first ||
      result.original.second != result.transformed.second;
  return result;
}

}  // namespace holonics::receiver
