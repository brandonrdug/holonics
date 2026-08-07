#include "r25_cases.hpp"

namespace holonics::tests {
namespace {

[[nodiscard]] organ::causal_linear_foundation foundation(
    const organ::causal_linear_card& card, const organ::cm_problem_card& cm,
    const organ::toric_cycle_card& toric,
    const organ::algebraic_variation_card& variation) noexcept {
  return {exact::word{139'800}, exact::word{139'801}, exact::word{139'802},
      exact::word{139'803}, exact::word{139'804}, exact::word{139'805},
      exact::word{139'806}, exact::word{139'807}, card, cm, toric, variation};
}

[[nodiscard]] organ::causal_linear_question question() noexcept {
  return {exact::word{149'800}, exact::word{149'801}, exact::word{149'802}};
}

}  // namespace

apparatus::causal_linear_mount r25_case(
    const event::algebraic_variation_rest_record& inherited,
    const organ::causal_linear_card& card, const organ::cm_problem_card& cm,
    const organ::toric_cycle_card& toric,
    const organ::algebraic_variation_card& variation) noexcept {
  return {foundation(card, cm, toric, variation), question(), inherited};
}

organ::causal_linear_card r25_host_card() noexcept {
  organ::causal_linear_card card{}; card.schema = exact::word{250'025};
  card.occurrence = exact::word{192'300}; card.lineage = exact::word{250'305};
  card.byte_fold = 260'305; card.path_fold = 270'305; card.byte_count = 27;
  card.eigen_min = -2; card.eigen_max = 2; card.phase_first = 2;
  card.phase_second = 3; card.parsed = true; return card;
}

}  // namespace holonics::tests
