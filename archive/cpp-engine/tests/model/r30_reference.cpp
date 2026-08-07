#include "r30_reference.hpp"

namespace holonics::tests {
namespace {
std::uint8_t pop(std::uint8_t x) {
  std::uint8_t n = 0;
  while (x) {
    n += x & 1U;
    x >>= 1U;
  }
  return n;
}
std::int64_t power(std::int64_t b, std::uint8_t e) {
  std::int64_t r = 1;
  while (e-- != 0)
    r *= b;
  return r;
}
std::int64_t factorial(std::uint8_t n) {
  std::int64_t r = 1;
  for (std::uint8_t i = 2; i <= n; ++i)
    r *= i;
  return r;
}
std::int64_t falling(std::uint8_t n, std::uint8_t k) {
  std::int64_t r = 1;
  for (std::uint8_t i = 0; i < k; ++i)
    r *= n - i;
  return r;
}
std::int64_t injection(std::uint8_t mask, const std::int16_t *values,
                       std::uint8_t forbidden) {
  std::uint8_t bits[3]{}, used = 0;
  for (std::uint8_t i = 0; i < 3; ++i)
    if (mask & (1U << i))
      bits[used++] = i;
  if (used == 0)
    return 1;
  std::int64_t sum = 0;
  for (std::uint8_t a = 0; a < 7; ++a) {
    if (a == forbidden)
      continue;
    auto wa = power(values[a], 1U << bits[0]);
    if (used == 1) {
      sum += wa;
      continue;
    }
    for (std::uint8_t b = 0; b < 7; ++b) {
      if (b == forbidden || b == a)
        continue;
      auto wb = power(values[b], 1U << bits[1]);
      if (used == 2) {
        sum += wa * wb;
        continue;
      }
      for (std::uint8_t c = 0; c < 7; ++c)
        if (c != forbidden && c != a && c != b)
          sum += wa * wb * power(values[c], 1U << bits[2]);
    }
  }
  return sum;
}
} // namespace
r30_reference_result r30_reference() noexcept {
  r30_reference_result r{};
  const std::int32_t area[4]{12, 12, 10, 15};
  const std::int32_t boundary[4]{8, 10, 12, 9};
  const std::int32_t interior[4]{3, 2, 0, 4};
  const std::int32_t counts[4][5]{{1, 11, 33, 67, 113},
                                  {1, 12, 35, 70, 117},
                                  {1, 12, 33, 64, 105},
                                  {1, 13, 40, 82, 139}};
  r.exact = true;
  for (std::uint8_t p = 0; p < 4; ++p) {
    r.area[p] = area[p];
    r.boundary[p] = boundary[p];
    r.interior[p] = interior[p];
    for (std::uint8_t n = 0; n < 5; ++n)
      r.counts[p][n] = counts[p][n];
  }
  return r;
}
std::int64_t r30_reference_jacobian(std::uint8_t alpha, std::uint8_t beta,
                                    std::uint8_t row,
                                    std::uint8_t column) noexcept {
  const std::int16_t p[7]{1, 2, 3, 4, 5, 6, 7}, q[7]{8, 9, 10, 11, 12, 13, 14};
  const auto ps = pop(alpha), qs = pop(beta);
  const auto factor = factorial(static_cast<std::uint8_t>(6U - ps - qs)) *
                      falling(static_cast<std::uint8_t>(6U - ps), qs) *
                      falling(static_cast<std::uint8_t>(6U - qs), ps);
  return factor * injection(alpha, p, column) * injection(beta, q, row);
}
} // namespace holonics::tests
