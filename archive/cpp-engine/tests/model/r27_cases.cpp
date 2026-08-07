#include "r27_cases.hpp"

namespace holonics::tests {
namespace {

[[nodiscard]] organ::expression_geometry_foundation foundation(
    const organ::expression_geometry_card& card) noexcept {
  return {exact::word{140'100}, exact::word{140'101}, exact::word{140'102},
      exact::word{140'103}, exact::word{140'104}, exact::word{140'105},
      exact::word{140'106}, exact::word{140'107}, card};
}

[[nodiscard]] organ::expression_geometry_question question() noexcept {
  return {exact::word{150'100}, exact::word{150'101}, exact::word{150'102}};
}

void add(organ::sparse_expression& expression, std::int64_t coefficient,
    std::uint8_t parameter, std::uint8_t x, std::uint8_t y) noexcept {
  expression.terms[expression.term_count] = {coefficient, parameter, x, y};
  ++expression.term_count;
}

void changed_constant(organ::sparse_expression& expression,
    std::int64_t from, std::int64_t to) noexcept {
  for (std::uint8_t slot = 0; slot < expression.term_count; ++slot) {
    auto& term = expression.terms[slot];
    if (term.parameter_power == 0 && term.x_power == 0 && term.y_power == 0 &&
        term.coefficient == from) { term.coefficient = to; return; }
  }
}

}  // namespace

apparatus::expression_geometry_mount r27_case(
    const event::intrinsic_hypergeometry_rest_record& inherited,
    const organ::expression_geometry_card& card) noexcept {
  auto changed = card; changed_constant(changed.presentations[0], -1, -2);
  changed_constant(changed.presentations[1], -2, -3);
  return {foundation(card), foundation(changed), question(), inherited};
}

organ::expression_geometry_card r27_host_card() noexcept {
  organ::expression_geometry_card card{}; card.schema = exact::word{270'027};
  card.occurrence = exact::word{194'300}; card.lineage = exact::word{250'307};
  card.byte_fold = 260'307; card.path_fold = 270'307; card.byte_count = 212;
  auto& canonical = card.presentations[0]; canonical.identity = exact::word{194'301};
  canonical.lineage = exact::word{250'308}; add(canonical,1,0,0,2); add(canonical,-1,0,5,0);
  add(canonical,1,1,1,0); add(canonical,-1,0,0,0); canonical.exact = true;
  auto& translated = card.presentations[1]; translated.identity = exact::word{194'302};
  translated.lineage = exact::word{250'309}; add(translated,1,0,0,2);
  add(translated,-1,0,5,0); add(translated,-5,0,4,0); add(translated,-10,0,3,0);
  add(translated,-10,0,2,0); add(translated,1,1,1,0); add(translated,-5,0,1,0);
  add(translated,1,1,0,0); add(translated,-2,0,0,0); translated.exact = true;
  auto& twist = card.presentations[2]; twist.identity = exact::word{194'303};
  twist.lineage = exact::word{250'310}; add(twist,1,0,0,2); add(twist,-1,0,5,0);
  add(twist,1,1,1,0); add(twist,1,0,0,0); twist.exact = true;
  card.discovery_min = -4; card.discovery_max = 4; card.holdout_first = 5;
  card.holdout_second = 6; card.chart_min = -2; card.chart_max = 2;
  card.series_depth = 11; card.presentation_count = 3; card.parsed = true; return card;
}

}  // namespace holonics::tests
