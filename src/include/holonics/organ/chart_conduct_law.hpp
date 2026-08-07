#pragma once

#include <holonics/organ/elementary_matrix_law.hpp>

namespace holonics::organ::chart_conduct_detail {

HOLONICS_CALLABLE inline void derive_chart(const local_chart_card &card,
    chart_receipt &out) noexcept {
  using namespace elementary_matrix_detail;
  out.first_inverse = inverse(card.first); out.second_inverse = inverse(card.second);
  out.first_path = multiply(card.first, card.second);
  out.second_path = multiply(card.second, card.first);
  out.residual = subtract(out.first_path, out.second_path);
  out.closed_word = multiply(multiply(multiply(card.first, card.second),
                                      out.first_inverse), out.second_inverse);
  out.flat_word = multiply(card.first, out.first_inverse);
  out.determinant = determinant(out.closed_word);
  out.trace = out.closed_word.value[0] + out.closed_word.value[3];
  out.curved = !zero(out.residual) && !equal(out.closed_word, identity());
  out.flat_control = equal(out.flat_word, identity());
  out.theory_formed = determinant(card.first) == 1 && determinant(card.second) == 1 &&
      out.determinant == 1 && out.trace == 3 && out.curved && out.flat_control;
}

[[nodiscard]] HOLONICS_CALLABLE inline bool matches(const conduct_case_card &row,
    std::uint16_t code, std::uint8_t &conditions) noexcept {
  bool accepted = true; conditions = 0;
  for (std::uint8_t field = 0; field < elementary_conduct_field_count; ++field) {
    const auto division = exact::small_rational_law::divide_unsigned(code, 3U);
    const auto condition = static_cast<std::uint8_t>(division.remainder);
    code = static_cast<std::uint16_t>(division.quotient);
    if (condition != 0) ++conditions;
    if (condition == 1) accepted = accepted && row.fields[field] == 0;
    if (condition == 2) accepted = accepted && row.fields[field] == 1;
  }
  return accepted;
}

HOLONICS_CALLABLE inline void derive_conduct(const return_conduct_card &card,
    conduct_receipt &out) noexcept {
  std::uint8_t best = elementary_conduct_field_count + 1U;
  std::uint16_t least_count = 0;
  for (std::uint16_t code = 0; code < elementary_conduct_candidate_count; ++code) {
    auto &candidate = out.candidates[code]; candidate.code = code;
    for (std::uint8_t row = 0; row < card.case_count; ++row) {
      std::uint8_t conditions = 0; const bool predicted = matches(card.cases[row], code, conditions);
      candidate.conditions = conditions;
      if (predicted != card.cases[row].changed_conduct) ++candidate.errors;
    }
    if (candidate.errors == 0) {
      if (candidate.conditions < best) { best = candidate.conditions; least_count = 1; out.selected_code = code; }
      else if (candidate.conditions == best) ++least_count;
    }
  }
  out.selected_population = best; out.unique_least = least_count == 1;
  out.candidates[out.selected_code].selected = out.unique_least;
  auto selected = out.selected_code;
  for (std::uint8_t field = 0; field < elementary_conduct_field_count; ++field) {
    const auto division = exact::small_rational_law::divide_unsigned(selected, 3U);
    out.selected_conditions[field] = static_cast<std::uint8_t>(division.remainder);
    selected = static_cast<std::uint16_t>(division.quotient);
  }
  constexpr std::uint8_t expected[elementary_conduct_field_count]{2,2,2,1,1,1,2};
  bool exact = out.unique_least && out.selected_population == elementary_conduct_field_count;
  for (std::uint8_t field = 0; field < elementary_conduct_field_count; ++field)
    exact = exact && out.selected_conditions[field] == expected[field];
  out.theory_formed = exact;
}

}  // namespace holonics::organ::chart_conduct_detail
