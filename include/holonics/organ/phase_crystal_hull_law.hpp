#pragma once

#include <holonics/organ/phase_crystal_geometry.hpp>

namespace holonics::organ::phase_crystal_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr int point_compare(
    const phase_point& left, const phase_point& right, bool& exact) noexcept {
  const int horizontal = compare(left.x, right.x, exact);
  if (!exact || horizontal != 0) { return horizontal; }
  const int vertical = compare(left.y, right.y, exact);
  if (!exact || vertical != 0) { return vertical; }
  if (left.first != right.first) { return left.first < right.first ? -1 : 1; }
  if (left.second != right.second) { return left.second < right.second ? -1 : 1; }
  return 0;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool same_position(
    const phase_point& left, const phase_point& right) noexcept {
  return left.x.numerator == right.x.numerator && left.x.denominator == right.x.denominator &&
      left.y.numerator == right.y.numerator && left.y.denominator == right.y.denominator;
}

HOLONICS_CALLABLE constexpr void sort_points(
    phase_point* points, std::uint16_t count, bool& exact) noexcept {
  for (std::uint16_t index = 1; index < count && exact; ++index) {
    const phase_point value = points[index];
    std::uint16_t position = index;
    while (position != 0 && point_compare(value, points[position - 1U], exact) < 0) {
      points[position] = points[position - 1U];
      --position;
    }
    points[position] = value;
  }
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t unique_points(
    phase_point* points, std::uint16_t count) noexcept {
  if (count == 0) { return 0; }
  std::uint16_t used = 1;
  for (std::uint16_t slot = 1; slot < count; ++slot) {
    if (!same_position(points[slot], points[used - 1U])) { points[used++] = points[slot]; }
  }
  return used;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t convex_hull(
    phase_point* points, std::uint16_t count,
    phase_point* hull, bool& exact) noexcept {
  sort_points(points, count, exact);
  count = unique_points(points, count);
  if (!exact || count < 3) { return 0; }
  std::uint16_t used = 0;
  for (std::uint16_t slot = 0; slot < count; ++slot) {
    while (used >= 2 && orientation(hull[used - 2U], hull[used - 1U], points[slot], exact) <= 0) {
      --used;
    }
    hull[used++] = points[slot];
  }
  const std::uint16_t lower = used;
  for (std::uint16_t slot = static_cast<std::uint16_t>(count - 1U); slot != 0; --slot) {
    while (used > lower && orientation(hull[used - 2U], hull[used - 1U],
        points[slot - 1U], exact) <= 0) { --used; }
    hull[used++] = points[slot - 1U];
  }
  return exact && used > 1 ? static_cast<std::uint16_t>(used - 1U) : 0;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool hull_receipt(
    const phase_case_definition& definition, phase_case_receipt& receipt) noexcept {
  phase_point points[phase_crystal_point_capacity]{};
  phase_point hull[phase_crystal_point_capacity * 2U]{};
  std::uint16_t count = 0;
  for (std::uint16_t first = 0; first < definition.first_modulus; ++first) {
    for (std::uint16_t second = 0; second < definition.second_modulus; ++second) {
      if (!project_point(definition, first, second, points[count++])) { return false; }
    }
  }
  bool exact = true;
  const std::uint16_t corners = convex_hull(points, count, hull, exact);
  if (!exact || corners < 3) { return false; }
  phase_ratio side_types[phase_crystal_point_capacity * 2U]{};
  std::uint16_t type_count = 0;
  std::uint16_t transitions = 0;
  for (std::uint16_t slot = 0; slot < corners; ++slot) {
    const auto next = static_cast<std::uint16_t>(slot + 1U == corners ? 0U : slot + 1U);
    phase_ratio side{};
    if (!squared_distance(hull[slot], hull[next], side)) { return false; }
    if (slot == 0 || compare(side, receipt.receiver_shortest_hull_side, exact) < 0) {
      receipt.receiver_shortest_hull_side = side;
    }
    if (slot == 0 || compare(side, receipt.receiver_longest_hull_side, exact) > 0) {
      receipt.receiver_longest_hull_side = side;
    }
    bool seen = false;
    for (std::uint16_t prior = 0; prior < type_count; ++prior) {
      seen = seen || (side.numerator == side_types[prior].numerator &&
          side.denominator == side_types[prior].denominator);
    }
    if (!seen) { side_types[type_count++] = side; }
    const auto current_residue = definition.second_dominant ?
        hull[slot].second : hull[slot].first;
    const auto next_residue = definition.second_dominant ?
        hull[next].second : hull[next].first;
    transitions = static_cast<std::uint16_t>(transitions +
        (current_residue == next_residue ? 0U : 1U));
  }
  receipt.hull_corners = corners;
  receipt.contracted_sides = transitions;
  receipt.hull_edge_types = type_count;
  receipt.hull_exact = exact;
  return exact;
}

}  // namespace holonics::organ::phase_crystal_detail
