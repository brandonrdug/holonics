#include "r26_cases.hpp"

namespace holonics::tests {
namespace {

[[nodiscard]] organ::intrinsic_hypergeometry_foundation foundation(
    const organ::intrinsic_hypergeometry_card& card,
    const organ::cm_problem_card& cm,
    const organ::algebraic_variation_card& variation) noexcept {
  return {exact::word{139'900}, exact::word{139'901}, exact::word{139'902},
      exact::word{139'903}, exact::word{139'904}, exact::word{139'905},
      exact::word{139'906}, exact::word{139'907}, card, cm, variation};
}

[[nodiscard]] organ::intrinsic_hypergeometry_question question() noexcept {
  return {exact::word{149'900}, exact::word{149'901}, exact::word{149'902}};
}

}  // namespace

apparatus::intrinsic_hypergeometry_mount r26_case(
    const event::causal_linear_rest_record& inherited,
    const organ::intrinsic_hypergeometry_card& card,
    const organ::cm_problem_card& cm,
    const organ::algebraic_variation_card& variation) noexcept {
  auto changed = card; changed.cases[2].second = 8;
  return {foundation(card, cm, variation), foundation(changed, cm, variation),
      question(), inherited};
}

organ::intrinsic_hypergeometry_card r26_host_card() noexcept {
  organ::intrinsic_hypergeometry_card card{};
  card.schema = exact::word{260'026}; card.occurrence = exact::word{193'300};
  card.lineage = exact::word{250'306}; card.byte_fold = 260'306;
  card.path_fold = 270'306; card.byte_count = 104;
  constexpr organ::intrinsic_presentation cases[organ::intrinsic_case_capacity]{
      {2,3,0},{3,5,0},{5,7,0},{7,11,0},{11,13,0},
      {13,17,0},{17,19,0},{6,9,0},{8,12,0},{7,5,1}};
  for (std::uint8_t slot = 0; slot < organ::intrinsic_case_capacity; ++slot) {
    card.cases[slot] = cases[slot];
  }
  card.section_modulus = 65'521; card.receiver_first_weight = 3;
  card.receiver_second_weight = 1; card.receiver_denominator = 3;
  card.series_depth = 20; card.case_count = organ::intrinsic_case_capacity;
  card.parsed = true; return card;
}

}  // namespace holonics::tests
