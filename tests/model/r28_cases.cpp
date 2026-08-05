#include "r28_cases.hpp"

namespace holonics::tests {
namespace {

[[nodiscard]] organ::hodge_realization_foundation foundation(
    const organ::hodge_realization_card& card) noexcept {
  return {exact::word{140'200}, exact::word{140'201}, exact::word{140'202},
      exact::word{140'203}, exact::word{140'204}, exact::word{140'205},
      exact::word{140'206}, exact::word{140'207}, exact::word{140'208}, card};
}

void add(organ::hodge_family_source& source, std::int64_t coefficient,
    std::uint8_t parameter, std::uint8_t x, std::uint8_t y) noexcept {
  source.terms[source.term_count] = {coefficient,parameter,x,y}; ++source.term_count;
}

}  // namespace

apparatus::hodge_realization_mount r28_case(
    const event::expression_geometry_rest_record& inherited,
    const organ::hodge_realization_card& card) noexcept {
  return {foundation(card), {exact::word{150'200}, exact::word{150'201}, exact::word{150'202}}, inherited};
}

organ::hodge_realization_card r28_host_card() noexcept {
  organ::hodge_realization_card card{}; card.schema = exact::word{280'028};
  card.occurrence = exact::word{195'300}; card.lineage = exact::word{250'408};
  card.byte_fold = 260'408; card.path_fold = 270'408; card.byte_count = 182;
  for (std::uint8_t factor = 0; factor < 2; ++factor) {
    auto& source = card.factors[factor]; source.identity = exact::word{195'301U + factor};
    source.lineage = exact::word{250'409U + factor}; add(source,1,0,0,2);
    add(source,-1,0,3,0); add(source,1,0,2,0); add(source,1,1,2,0);
    add(source,-1,1,1,0); source.exact = true;
  }
  const std::int64_t targets[3][6]{{1,1,0,1,-1,0},{1,1,0,1,-1,0},{0,0,1,0,0,1}};
  for (std::uint8_t question = 0; question < 3; ++question) {
    for (std::uint8_t slot = 0; slot < 6; ++slot) {
      card.questions[question].numerator[slot] = targets[question][slot];
    }
    card.questions[question].denominator = question == 1 ? 2 : 1;
  }
  card.coefficient_min = -1; card.coefficient_max = 1; card.base_t = 2; card.base_u = 2;
  card.off_diagonal_u = 3; card.denominator_aperture = 2; card.center_selector = 0;
  card.changed_center_selector = 1; card.factor_count = 2; card.rank = 6;
  card.question_count = 3; card.parsed = true; return card;
}

}  // namespace holonics::tests
