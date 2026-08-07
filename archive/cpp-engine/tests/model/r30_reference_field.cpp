#include "r30_reference_field.hpp"

namespace holonics::tests {
namespace {
std::int64_t power(std::int64_t base, std::uint8_t exponent) {
  std::int64_t out = 1;
  while (exponent-- != 0)
    out *= base;
  return out;
}
std::int64_t factorial(std::uint8_t value) {
  std::int64_t out = 1;
  for (std::uint8_t i = 2; i <= value; ++i)
    out *= i;
  return out;
}
std::int64_t falling(std::uint8_t value, std::uint8_t count) {
  std::int64_t out = 1;
  for (std::uint8_t i = 0; i < count; ++i)
    out *= value - i;
  return out;
}
std::uint8_t population(std::uint8_t value) {
  std::uint8_t out = 0;
  while (value != 0) {
    out = static_cast<std::uint8_t>(out + (value & 1U));
    value >>= 1U;
  }
  return out;
}
bool emit(std::uint8_t side, std::uint8_t subset, std::uint8_t forbidden,
          const std::uint8_t (&image)[3], std::uint8_t size,
          std::int64_t weight, std::uint16_t wanted, std::uint16_t &used,
          r30_reference_injection &out) {
  if (used++ != wanted)
    return false;
  out = {side, subset, forbidden, {image[0], image[1], image[2]}, size, weight};
  return true;
}
struct point final {
  std::int32_t x;
  std::int32_t y;
};
constexpr std::uint8_t vertex_counts[4]{3, 4, 6, 3};
constexpr point vertices[4][6]{{{0, 0}, {4, 0}, {0, 3}},
                               {{0, 0}, {3, 0}, {3, 2}, {0, 2}},
                               {{0, 0}, {3, 0}, {3, 1}, {1, 1}, {1, 3}, {0, 3}},
                               {{0, 0}, {5, 0}, {0, 3}}};
std::int32_t cross(point a, point b, std::int32_t x, std::int32_t y,
                   std::uint8_t dilation) {
  a.x *= dilation;
  a.y *= dilation;
  b.x *= dilation;
  b.y *= dilation;
  return (b.x - a.x) * (y - a.y) - (b.y - a.y) * (x - a.x);
}
bool on_segment(point a, point b, std::int32_t x, std::int32_t y,
                std::uint8_t dilation) {
  if (cross(a, b, x, y, dilation) != 0)
    return false;
  a.x *= dilation;
  a.y *= dilation;
  b.x *= dilation;
  b.y *= dilation;
  return x >= (a.x < b.x ? a.x : b.x) && x <= (a.x > b.x ? a.x : b.x) &&
         y >= (a.y < b.y ? a.y : b.y) && y <= (a.y > b.y ? a.y : b.y);
}
std::uint8_t bit(std::uint8_t value, std::uint8_t row) {
  return static_cast<std::uint8_t>((value >> row) & 1U);
}
} // namespace

bool r30_reference_injection_at(std::uint8_t side, std::uint16_t wanted,
                                r30_reference_injection &out) noexcept {
  const std::int16_t values[2][7]{{1, 2, 3, 4, 5, 6, 7},
                                  {8, 9, 10, 11, 12, 13, 14}};
  std::uint16_t used = 0;
  for (std::uint8_t subset = 0; subset < 7; ++subset) {
    std::uint8_t indices[3]{}, count = 0;
    for (std::uint8_t bit_slot = 0; bit_slot < 3; ++bit_slot)
      if ((subset & (1U << bit_slot)) != 0)
        indices[count++] = bit_slot;
    for (std::uint8_t forbidden = 0; forbidden < 7; ++forbidden) {
      const std::uint8_t empty[3]{};
      if (count == 0) {
        if (emit(side, subset, forbidden, empty, 0, 1, wanted, used, out))
          return true;
        continue;
      }
      for (std::uint8_t a = 0; a < 7; ++a) {
        if (a == forbidden)
          continue;
        const std::uint8_t one[3]{a, 0, 0};
        const auto wa =
            power(values[side][a], static_cast<std::uint8_t>(1U << indices[0]));
        if (count == 1) {
          if (emit(side, subset, forbidden, one, 1, wa, wanted, used, out))
            return true;
          continue;
        }
        for (std::uint8_t b = 0; b < 7; ++b) {
          if (b == forbidden || b == a)
            continue;
          const std::uint8_t two[3]{a, b, 0};
          const auto wb = power(values[side][b],
                                static_cast<std::uint8_t>(1U << indices[1]));
          if (count == 2) {
            if (emit(side, subset, forbidden, two, 2, wa * wb, wanted, used,
                     out))
              return true;
            continue;
          }
          for (std::uint8_t c = 0; c < 7; ++c) {
            if (c == forbidden || c == a || c == b)
              continue;
            const std::uint8_t three[3]{a, b, c};
            if (emit(side, subset, forbidden, three, 3,
                     wa * wb *
                         power(values[side][c],
                               static_cast<std::uint8_t>(1U << indices[2])),
                     wanted, used, out))
              return true;
          }
        }
      }
    }
  }
  return false;
}

std::int64_t r30_reference_evaluation(std::uint8_t side, std::uint8_t subset,
                                      std::uint8_t forbidden) noexcept {
  std::int64_t sum = 0;
  for (std::uint16_t slot = 0;; ++slot) {
    r30_reference_injection injection{};
    if (!r30_reference_injection_at(side, slot, injection))
      break;
    if (injection.subset == subset && injection.forbidden == forbidden)
      sum += injection.weight;
  }
  return sum;
}

r30_reference_factor r30_reference_factor_at(std::uint8_t alpha,
                                             std::uint8_t beta) noexcept {
  const auto p = population(alpha), q = population(beta);
  const auto pl =
      static_cast<std::int16_t>((p & 1U) == 0 ? factorial(p) : -factorial(p));
  const auto ql =
      static_cast<std::int16_t>((q & 1U) == 0 ? factorial(q) : -factorial(q));
  return {p, q, pl, ql,
          factorial(static_cast<std::uint8_t>(6U - p - q)) *
              falling(static_cast<std::uint8_t>(6U - p), q) *
              falling(static_cast<std::uint8_t>(6U - q), p)};
}

r30_reference_point r30_reference_lattice_point(std::uint8_t polygon,
                                                std::uint8_t dilation,
                                                std::int32_t x,
                                                std::int32_t y) noexcept {
  std::int32_t maximum_x = 0, maximum_y = 0;
  for (std::uint8_t i = 0; i < vertex_counts[polygon]; ++i) {
    const auto vx = vertices[polygon][i].x * dilation;
    const auto vy = vertices[polygon][i].y * dilation;
    maximum_x = vx > maximum_x ? vx : maximum_x;
    maximum_y = vy > maximum_y ? vy : maximum_y;
  }
  r30_reference_point out{x >= 0 && y >= 0 && x <= maximum_x && y <= maximum_y,
                          false, false};
  if (!out.in_box)
    return out;
  std::int32_t winding = 0;
  for (std::uint8_t i = 0; i < vertex_counts[polygon]; ++i) {
    const auto next = static_cast<std::uint8_t>(i + 1U);
    const auto a = vertices[polygon][i];
    const auto b = vertices[polygon][next == vertex_counts[polygon] ? 0 : next];
    if (on_segment(a, b, x, y, dilation)) {
      out.boundary = true;
      out.included = true;
      return out;
    }
    const auto ay = a.y * dilation, by = b.y * dilation;
    const auto orientation = cross(a, b, x, y, dilation);
    if (ay <= y && by > y && orientation > 0)
      ++winding;
    else if (ay > y && by <= y && orientation < 0)
      --winding;
  }
  out.included = winding != 0;
  return out;
}

r30_reference_subset r30_reference_subset_at(std::uint8_t wanted) noexcept {
  std::uint8_t used = 0;
  for (std::uint8_t a = 0; a < 5; ++a)
    for (std::uint8_t b = a + 1; b < 6; ++b)
      for (std::uint8_t c = b + 1; c < 7; ++c)
        for (std::uint8_t d = c + 1; d < 8; ++d) {
          if (used++ != wanted)
            continue;
          r30_reference_subset out{{a, b, c, d}, 0, false};
          for (std::uint8_t row = 0; row < 3 && !out.saturated; ++row)
            if (bit(a, row) != bit(b, row) || bit(a, row) != bit(c, row) ||
                bit(a, row) != bit(d, row)) {
              out.witness = row;
              out.saturated = true;
            }
          return out;
        }
  return {};
}

r30_reference_pair r30_reference_pair_at(std::uint8_t index) noexcept {
  r30_reference_pair out{static_cast<std::uint8_t>(index / 8U),
                         static_cast<std::uint8_t>(index % 8U)};
  const auto exceptional = static_cast<std::uint8_t>(7U - out.y);
  if (out.x == exceptional) {
    out.left = bit(out.x, 0) == bit(exceptional, 0);
    return out;
  }
  for (std::uint8_t row = 0; row < 3; ++row)
    if (bit(out.x, row) == bit(out.y, row)) {
      out.witness = row;
      out.right = true;
      break;
    }
  return out;
}

} // namespace holonics::tests
