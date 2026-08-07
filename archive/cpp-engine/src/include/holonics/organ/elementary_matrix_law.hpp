#pragma once

#include <holonics/organ/elementary_calculus_receipt.hpp>

namespace holonics::organ::elementary_matrix_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr exact_matrix2 identity() noexcept {
  return {{1,0,0,1}};
}
[[nodiscard]] HOLONICS_CALLABLE constexpr exact_matrix2 multiply(
    const exact_matrix2 &a, const exact_matrix2 &b) noexcept {
  return {{a.value[0]*b.value[0]+a.value[1]*b.value[2],
           a.value[0]*b.value[1]+a.value[1]*b.value[3],
           a.value[2]*b.value[0]+a.value[3]*b.value[2],
           a.value[2]*b.value[1]+a.value[3]*b.value[3]}};
}
[[nodiscard]] HOLONICS_CALLABLE constexpr exact_matrix2 subtract(
    const exact_matrix2 &a, const exact_matrix2 &b) noexcept {
  return {{a.value[0]-b.value[0],a.value[1]-b.value[1],
           a.value[2]-b.value[2],a.value[3]-b.value[3]}};
}
[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t determinant(
    const exact_matrix2 &a) noexcept {
  return a.value[0]*a.value[3]-a.value[1]*a.value[2];
}
[[nodiscard]] HOLONICS_CALLABLE constexpr exact_matrix2 inverse(
    const exact_matrix2 &a) noexcept {
  const auto d = determinant(a);
  if (d == 1) return {{a.value[3],-a.value[1],-a.value[2],a.value[0]}};
  if (d == -1) return {{-a.value[3],a.value[1],a.value[2],-a.value[0]}};
  return {};
}
[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal(
    const exact_matrix2 &a, const exact_matrix2 &b) noexcept {
  for (std::uint8_t i = 0; i < 4; ++i) if (a.value[i] != b.value[i]) return false;
  return true;
}
[[nodiscard]] HOLONICS_CALLABLE constexpr bool zero(const exact_matrix2 &a) noexcept {
  for (const auto value : a.value) if (value != 0) return false;
  return true;
}

HOLONICS_CALLABLE inline void trace_stream(const exact_matrix2 &matrix,
    exact::small_rational (&out)[elementary_trace_count]) noexcept {
  auto power = identity();
  for (std::uint8_t n = 0; n < elementary_trace_count; ++n) {
    out[n] = exact::small_rational_law::make(power.value[0] + power.value[3]);
    power = multiply(power, matrix);
  }
}

}  // namespace holonics::organ::elementary_matrix_detail
