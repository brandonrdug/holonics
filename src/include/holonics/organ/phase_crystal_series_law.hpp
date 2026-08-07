#pragma once

#include <holonics/organ/phase_crystal_exact.hpp>

namespace holonics::organ::phase_crystal_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool carry_gauss_112(
    std::uint16_t requested, phase_case_receipt& receipt) noexcept {
  const std::uint16_t terms = requested < phase_crystal_series_capacity ?
      requested : static_cast<std::uint16_t>(phase_crystal_series_capacity);
  phase_ratio coefficient{1, 1};
  receipt.series_recurrence_exact = terms != 0;
  receipt.series_closed_form_detected = terms != 0;
  for (std::uint16_t index = 0; index < terms; ++index) {
    const phase_ratio expected = normalize(1, static_cast<std::uint64_t>(index) + 1U);
    receipt.series_closed_form_detected = receipt.series_closed_form_detected &&
        coefficient.numerator == expected.numerator &&
        coefficient.denominator == expected.denominator;
    if (index + 1U == terms) { continue; }
    const std::uint64_t successor = static_cast<std::uint64_t>(index) + 1U;
    phase_ratio first{};
    phase_ratio second{};
    phase_ratio ratio{};
    phase_ratio next{};
    if (!scale({1, 1}, static_cast<std::int64_t>(successor), 1, first) ||
        !multiply(first, first, first) ||
        !scale({1, 1}, static_cast<std::int64_t>(successor + 1U), 1, second) ||
        !scale(second, static_cast<std::int64_t>(successor), 1, second) ||
        !multiply(first, normalize(1, second.numerator < 0 ? 0U :
            static_cast<std::uint64_t>(second.numerator)), ratio) ||
        !multiply(coefficient, ratio, next)) {
      receipt.series_recurrence_exact = false;
      return false;
    }
    coefficient = next;
  }
  receipt.series_terms = terms;
  return receipt.series_recurrence_exact && receipt.series_closed_form_detected;
}

}  // namespace holonics::organ::phase_crystal_detail
