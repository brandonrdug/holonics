#include "r29_cases.hpp"

namespace holonics::tests {

apparatus::arithmetic_spectral_mount r29_case(
    const event::hodge_realization_rest_record& inherited,
    const organ::arithmetic_spectral_card& card) noexcept {
  const organ::arithmetic_spectral_foundation foundation{card, exact::word{141'200},
      exact::word{141'201}, exact::word{141'202}, exact::word{141'203}};
  return {foundation, {exact::word{151'200}, exact::word{151'201}, exact::word{151'202}}, inherited};
}

organ::arithmetic_spectral_card r29_host_card() noexcept {
  organ::arithmetic_spectral_card card{}; card.schema = exact::word{290'029};
  card.occurrence = exact::word{196'300}; card.lineage = exact::word{250'509};
  card.byte_fold = 260'509; card.path_fold = 270'509; card.byte_count = 91;
  const std::uint16_t values[organ::arithmetic_baseline_count][2]{
      {5,1},{5,4},{13,1},{13,4},{13,2},{13,3}};
  for (std::uint8_t slot = 0; slot < organ::arithmetic_baseline_count; ++slot) {
    card.baseline[slot] = {values[slot][0],values[slot][1],exact::word{196'301U + slot},
        exact::word{250'510U + slot}};
  }
  card.changed_prime = 13; card.changed_from = 2; card.changed_to = 7;
  card.degree_min = 1; card.degree_max = 4; card.candidate_min = -4; card.candidate_max = 4;
  card.test_degree = 4; card.test_min = -1; card.test_max = 1;
  card.rechart_left = 2; card.rechart_right = 5; card.parsed = true; return card;
}

}  // namespace holonics::tests
