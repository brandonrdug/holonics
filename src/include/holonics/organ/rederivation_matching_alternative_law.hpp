#pragma once

#include <holonics/organ/rederivation_receipt.hpp>

namespace holonics::organ::rederivation_matching_alternative_detail {

[[nodiscard]] HOLONICS_CALLABLE inline std::int64_t
vandermonde(const std::int16_t (&values)[rederivation_external_count],
            bool duplicate_last) noexcept {
  std::int64_t product = 1;
  for (std::uint8_t left = 0; left < rederivation_external_count; ++left)
    for (std::uint8_t right = static_cast<std::uint8_t>(left + 1U);
         right < rederivation_external_count; ++right) {
      const auto right_value =
          duplicate_last && right + 1U == rederivation_external_count
              ? values[rederivation_external_count - 2U]
              : values[right];
      product *= static_cast<std::int64_t>(right_value - values[left]);
    }
  return product;
}

HOLONICS_CALLABLE inline void
derive(const matching_problem_card &card,
       matching_rederivation_receipt &out) noexcept {
  out.p_vandermonde = vandermonde(card.p, false);
  out.q_vandermonde = vandermonde(card.q, false);
  out.duplicate_q_vandermonde = vandermonde(card.q, true);
  out.duplicate_q_obstructed = out.duplicate_q_vandermonde == 0;
  out.changed_independence_undetermined = out.duplicate_q_obstructed;
}

} // namespace holonics::organ::rederivation_matching_alternative_detail
