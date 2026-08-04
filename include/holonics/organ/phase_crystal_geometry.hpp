#pragma once

#include <holonics/exact/signed_magnitude.hpp>
#include <holonics/organ/phase_crystal_exact.hpp>

namespace holonics::organ::phase_crystal_detail {

struct phase_point final {
  phase_ratio x{};
  phase_ratio y{};
  std::uint16_t first{};
  std::uint16_t second{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr bool conic_phase(
    std::uint16_t residue, std::uint16_t modulus,
    phase_ratio& horizontal, phase_ratio& vertical) noexcept {
  if (modulus < 2 || residue >= modulus) { return false; }
  const std::uint64_t four_residue = 4U * residue;
  std::uint64_t quadrant = 0;
  std::uint64_t local = 0;
  if (!divide_unsigned(four_residue, modulus, quadrant, local)) { return false; }
  const std::uint64_t square_modulus = static_cast<std::uint64_t>(modulus) * modulus;
  const std::uint64_t square_local = local * local;
  const auto first = normalize(static_cast<std::int64_t>(square_modulus - square_local),
      square_modulus + square_local);
  const auto second = normalize(static_cast<std::int64_t>(2U * local * modulus),
      square_modulus + square_local);
  if (quadrant == 0) { horizontal = first; vertical = second; }
  else if (quadrant == 1) { horizontal = {-second.numerator, second.denominator}; vertical = first; }
  else if (quadrant == 2) {
    horizontal = {-first.numerator, first.denominator};
    vertical = {-second.numerator, second.denominator};
  } else if (quadrant == 3) {
    horizontal = second;
    vertical = {-first.numerator, first.denominator};
  } else { return false; }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool rational_turn(
    phase_ratio x, phase_ratio y, phase_ratio& turned_x, phase_ratio& turned_y) noexcept {
  phase_ratio three_x{};
  phase_ratio four_y{};
  phase_ratio four_x{};
  phase_ratio three_y{};
  phase_ratio horizontal{};
  phase_ratio vertical{};
  if (!scale(x, 3, 1, three_x) || !scale(y, 4, 1, four_y) ||
      !scale(x, 4, 1, four_x) || !scale(y, 3, 1, three_y) ||
      !subtract(three_x, four_y, horizontal) || !add(four_x, three_y, vertical) ||
      !scale(horizontal, 1, 5, turned_x) || !scale(vertical, 1, 5, turned_y)) {
    return false;
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool project_point(
    const phase_case_definition& definition, std::uint16_t first, std::uint16_t second,
    phase_point& point) noexcept {
  phase_ratio first_x{};
  phase_ratio first_y{};
  phase_ratio second_x{};
  phase_ratio second_y{};
  if (!conic_phase(first, definition.first_modulus, first_x, first_y) ||
      !conic_phase(second, definition.second_modulus, second_x, second_y)) { return false; }
  if (definition.rational_turn) {
    phase_ratio turned_first_x{};
    phase_ratio turned_first_y{};
    phase_ratio turned_second_x{};
    phase_ratio turned_second_y{};
    if (!rational_turn(first_x, first_y, turned_first_x, turned_first_y) ||
        !rational_turn(second_x, second_y, turned_second_x, turned_second_y)) { return false; }
    first_x = turned_first_x;
    first_y = turned_first_y;
    second_x = turned_second_x;
    second_y = turned_second_y;
  }
  const std::int64_t first_weight = definition.second_dominant ? 1 : 3;
  const std::int64_t second_weight = definition.second_dominant ? 3 : 1;
  phase_ratio weighted_first_x{};
  phase_ratio weighted_first_y{};
  phase_ratio weighted_second_x{};
  phase_ratio weighted_second_y{};
  phase_ratio x{};
  phase_ratio y{};
  if (!scale(first_x, first_weight, 3, weighted_first_x) ||
      !scale(first_y, first_weight, 3, weighted_first_y) ||
      !scale(second_x, second_weight, 3, weighted_second_x) ||
      !scale(second_y, second_weight, 3, weighted_second_y) ||
      !add(weighted_first_x, weighted_second_x, x) ||
      !add(weighted_first_y, weighted_second_y, y) ||
      !scale(x, definition.scale_numerator, definition.scale_denominator, point.x) ||
      !scale(y, definition.scale_numerator, definition.scale_denominator, point.y)) {
    return false;
  }
  point.first = first;
  point.second = second;
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool squared_distance(
    const phase_point& left, const phase_point& right, phase_ratio& result) noexcept {
  phase_ratio dx{};
  phase_ratio dy{};
  phase_ratio dx2{};
  phase_ratio dy2{};
  return subtract(right.x, left.x, dx) && subtract(right.y, left.y, dy) &&
      multiply(dx, dx, dx2) && multiply(dy, dy, dy2) && add(dx2, dy2, result);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr int orientation(
    const phase_point& a, const phase_point& b, const phase_point& c, bool& exact) noexcept {
  phase_ratio abx{};
  phase_ratio aby{};
  phase_ratio acx{};
  phase_ratio acy{};
  if (!subtract(b.x, a.x, abx) || !subtract(b.y, a.y, aby) ||
      !subtract(c.x, a.x, acx) || !subtract(c.y, a.y, acy)) {
    exact = false;
    return 0;
  }
  using wide = exact::signed_magnitude<6>;
  const auto value = [](std::int64_t number) {
    return wide{number < 0, exact::unsigned_384::from_word(magnitude(number))};
  };
  const auto product = [&](wide left, std::uint64_t right, wide& output) {
    const auto result = exact::multiply(left,
        wide{false, exact::unsigned_384::from_word(right)});
    if (!result.accepted()) { return false; }
    output = result.value;
    return true;
  };
  wide left = value(abx.numerator);
  wide right = value(aby.numerator);
  if (!product(left, magnitude(acy.numerator), left) ||
      !product(left, aby.denominator, left) ||
      !product(left, acx.denominator, left) ||
      !product(right, magnitude(acx.numerator), right) ||
      !product(right, abx.denominator, right) ||
      !product(right, acy.denominator, right)) {
    exact = false;
    return 0;
  }
  left = wide{(abx.numerator < 0) != (acy.numerator < 0), left.magnitude()};
  right = wide{(aby.numerator < 0) != (acx.numerator < 0), right.magnitude()};
  const wide negative_right{!right.negative(), right.magnitude()};
  const auto area = exact::add(left, negative_right);
  if (!area.accepted()) { exact = false; return 0; }
  if (area.value.magnitude().is_zero()) { return 0; }
  return area.value.negative() ? -1 : 1;
}

}  // namespace holonics::organ::phase_crystal_detail
