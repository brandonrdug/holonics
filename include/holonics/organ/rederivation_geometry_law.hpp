#pragma once

#include <holonics/exact/integer_division.hpp>
#include <holonics/organ/rederivation_receipt.hpp>

namespace holonics::organ::rederivation_geometry_detail {

[[nodiscard]] HOLONICS_CALLABLE inline std::int32_t
absolute(std::int32_t value) noexcept {
  return value < 0 ? -value : value;
}
[[nodiscard]] HOLONICS_CALLABLE inline std::int32_t
gcd(std::int32_t a, std::int32_t b) noexcept {
  a = absolute(a);
  b = absolute(b);
  while (b != 0) {
    const auto r = exact::positive_remainder(static_cast<std::uint64_t>(a),
                                             static_cast<std::uint64_t>(b));
    a = b;
    b = static_cast<std::int32_t>(r);
  }
  return a;
}
[[nodiscard]] HOLONICS_CALLABLE inline std::int32_t
cross(rederivation_point a, rederivation_point b, std::int32_t x,
      std::int32_t y, std::uint8_t dilation) noexcept {
  const auto ax = static_cast<std::int32_t>(a.x) * dilation;
  const auto ay = static_cast<std::int32_t>(a.y) * dilation;
  const auto bx = static_cast<std::int32_t>(b.x) * dilation;
  const auto by = static_cast<std::int32_t>(b.y) * dilation;
  return (bx - ax) * (y - ay) - (by - ay) * (x - ax);
}
[[nodiscard]] HOLONICS_CALLABLE inline bool
on_segment(rederivation_point a, rederivation_point b, std::int32_t x,
           std::int32_t y, std::uint8_t dilation) noexcept {
  if (cross(a, b, x, y, dilation) != 0)
    return false;
  const auto ax = static_cast<std::int32_t>(a.x) * dilation;
  const auto ay = static_cast<std::int32_t>(a.y) * dilation;
  const auto bx = static_cast<std::int32_t>(b.x) * dilation;
  const auto by = static_cast<std::int32_t>(b.y) * dilation;
  return x >= (ax < bx ? ax : bx) && x <= (ax > bx ? ax : bx) &&
         y >= (ay < by ? ay : by) && y <= (ay > by ? ay : by);
}
[[nodiscard]] HOLONICS_CALLABLE inline bool
contains(const rederivation_polygon_source &polygon, std::int32_t x,
         std::int32_t y, std::uint8_t dilation, bool &boundary) noexcept {
  boundary = false;
  std::int32_t winding = 0;
  for (std::uint8_t i = 0; i < polygon.vertex_count; ++i) {
    const auto a = polygon.vertices[i];
    const auto next = static_cast<std::uint8_t>(i + 1U);
    const auto b = polygon.vertices[next == polygon.vertex_count ? 0U : next];
    if (on_segment(a, b, x, y, dilation)) {
      boundary = true;
      return true;
    }
    const auto ay = static_cast<std::int32_t>(a.y) * dilation;
    const auto by = static_cast<std::int32_t>(b.y) * dilation;
    const auto c = cross(a, b, x, y, dilation);
    if (ay <= y && by > y && c > 0)
      ++winding;
    else if (ay > y && by <= y && c < 0)
      --winding;
  }
  return winding != 0;
}
[[nodiscard]] HOLONICS_CALLABLE inline std::int32_t
double_area(const rederivation_polygon_source &polygon) noexcept {
  std::int32_t sum = 0;
  for (std::uint8_t i = 0; i < polygon.vertex_count; ++i) {
    const auto a = polygon.vertices[i];
    const auto next = static_cast<std::uint8_t>(i + 1U);
    const auto b = polygon.vertices[next == polygon.vertex_count ? 0U : next];
    sum += a.x * b.y - a.y * b.x;
  }
  return absolute(sum);
}
[[nodiscard]] HOLONICS_CALLABLE inline std::int32_t
boundary_count(const rederivation_polygon_source &polygon) noexcept {
  std::int32_t sum = 0;
  for (std::uint8_t i = 0; i < polygon.vertex_count; ++i) {
    const auto a = polygon.vertices[i];
    const auto next = static_cast<std::uint8_t>(i + 1U);
    const auto b = polygon.vertices[next == polygon.vertex_count ? 0U : next];
    sum += gcd(b.x - a.x, b.y - a.y);
  }
  return sum;
}

HOLONICS_CALLABLE inline void
derive_polygon(std::uint8_t slot, const lattice_problem_card &card,
               rederivation_workspace &workspace,
               polygon_rederivation_receipt &out) noexcept {
  const auto &polygon = card.polygons[slot];
  out.double_area = double_area(polygon);
  out.boundary = boundary_count(polygon);
  out.simple = true;
  for (std::uint8_t dilation = 0; dilation < 5; ++dilation) {
    std::int32_t count = 0;
    std::int32_t interior = 0;
    std::int32_t max_x = 0, max_y = 0;
    for (std::uint8_t v = 0; v < polygon.vertex_count; ++v) {
      const auto x =
          static_cast<std::int32_t>(polygon.vertices[v].x) * dilation;
      const auto y =
          static_cast<std::int32_t>(polygon.vertices[v].y) * dilation;
      if (x > max_x)
        max_x = x;
      if (y > max_y)
        max_y = y;
    }
    for (std::int32_t x = 0; x <= max_x; ++x)
      for (std::int32_t y = 0; y <= max_y; ++y) {
        bool edge = false;
        const bool included = contains(polygon, x, y, dilation, edge);
        if (included) {
          ++count;
          if (!edge)
            ++interior;
        }
        auto &point = workspace.lattice[slot][dilation][x][y];
        point = {slot,
                 dilation,
                 static_cast<std::int16_t>(x),
                 static_cast<std::int16_t>(y),
                 true,
                 included,
                 edge,
                 exact::word{card.metadata.lineage.value() + 50'000U +
                             static_cast<std::uint64_t>(slot) * 10'000U +
                             static_cast<std::uint64_t>(dilation) * 1'000U +
                             static_cast<std::uint64_t>(x) * 32U +
                             static_cast<std::uint64_t>(y)}};
      }
    out.lattice_count[dilation] = count;
    out.reciprocal_interior[dilation] = interior;
  }
  out.interior = out.reciprocal_interior[1];
  out.pick_exact = out.double_area == 2 * out.interior + out.boundary - 2;
  out.ehrhart_exact = true;
  out.reciprocity_exact = true;
  for (std::uint8_t n = 0; n < 5; ++n) {
    out.ehrhart_exact =
        out.ehrhart_exact && 2 * out.lattice_count[n] ==
                                 out.double_area * n * n + out.boundary * n + 2;
    if (n > 0)
      out.reciprocity_exact =
          out.reciprocity_exact &&
          2 * out.reciprocal_interior[n] ==
              out.double_area * n * n - out.boundary * n + 2;
  }
  out.identity = exact::word{197'301U + slot};
  out.lineage = exact::word{card.metadata.lineage.value() + 49'000U + slot};
}

} // namespace holonics::organ::rederivation_geometry_detail
