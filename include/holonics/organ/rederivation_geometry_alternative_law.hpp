#pragma once

#include <holonics/organ/rederivation_receipt.hpp>

namespace holonics::organ::rederivation_geometry_alternative_detail {

[[nodiscard]] HOLONICS_CALLABLE inline std::int32_t
orientation(rederivation_point a, rederivation_point b,
            rederivation_point c) noexcept {
  return (static_cast<std::int32_t>(b.x) - a.x) *
             (static_cast<std::int32_t>(c.y) - a.y) -
         (static_cast<std::int32_t>(b.y) - a.y) *
             (static_cast<std::int32_t>(c.x) - a.x);
}

[[nodiscard]] HOLONICS_CALLABLE inline bool
self_crossing_foil(const lattice_problem_card &card) noexcept {
  const auto &polygon = card.polygons[1];
  if (polygon.vertex_count != 4)
    return false;
  const auto a = polygon.vertices[0];
  const auto b = polygon.vertices[2];
  const auto c = polygon.vertices[1];
  const auto d = polygon.vertices[3];
  const auto first_a = orientation(a, b, c);
  const auto first_b = orientation(a, b, d);
  const auto second_a = orientation(c, d, a);
  const auto second_b = orientation(c, d, b);
  return ((first_a < 0 && first_b > 0) || (first_a > 0 && first_b < 0)) &&
         ((second_a < 0 && second_b > 0) || (second_a > 0 && second_b < 0));
}

} // namespace holonics::organ::rederivation_geometry_alternative_detail
