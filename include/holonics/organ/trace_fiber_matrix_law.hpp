#pragma once

#include <holonics/organ/characteristic_matrix_law.hpp>
#include <holonics/organ/trace_fiber_receipt.hpp>

namespace holonics::organ::trace_fiber_matrix_detail {

HOLONICS_CALLABLE inline void form_words(const three_face_source_card &card,
                                         transition_word_population &out) noexcept {
  characteristic_matrix_detail::form_words(card.transitions, out);
  if (out.count < card.admitted_words ||
      card.admitted_words != trace_fiber_word_count) {
    out.complete = false;
    return;
  }
  out.count = card.admitted_words;
}
HOLONICS_CALLABLE inline void form_triple(
    const reduced_transition_word &wa, const reduced_transition_word &wb,
    const reduced_transition_word &wc, std::uint8_t source,
    transition_triple_receipt &out) noexcept {
  using namespace elementary_matrix_detail;
  out = {};
  out.matrices[0] = wa.matrix;
  out.matrices[1] = wb.matrix;
  out.matrices[2] = wc.matrix;
  out.matrices[3] = multiply(wa.matrix, wb.matrix);
  out.matrices[4] = multiply(wa.matrix, wc.matrix);
  out.matrices[5] = multiply(wb.matrix, wc.matrix);
  out.matrices[6] = multiply(out.matrices[3], wc.matrix);
  out.matrices[7] = multiply(out.matrices[4], wb.matrix);
  for (std::uint8_t i = 0; i < trace_fiber_lower_count; ++i)
    out.lower[i] = characteristic_matrix_detail::trace(out.matrices[i]);
  out.ordered[0] = characteristic_matrix_detail::trace(out.matrices[6]);
  out.ordered[1] = characteristic_matrix_detail::trace(out.matrices[7]);
  out.symmetric[0] = out.ordered[0] + out.ordered[1];
  out.symmetric[1] = out.ordered[0] * out.ordered[1];
  out.discriminant = out.symmetric[0] * out.symmetric[0] -
                     4 * out.symmetric[1];
  const auto gap = out.ordered[0] - out.ordered[1];
  out.root_gap = gap < 0 ? -gap : gap;
  out.words[0] = wa.ordinal;
  out.words[1] = wb.ordinal;
  out.words[2] = wc.ordinal;
  out.source = source;
  out.branch = out.ordered[0] == out.ordered[1];
  out.valid = out.discriminant == out.root_gap * out.root_gap;
}
struct heldout_trace_source_secret final {
  exact_matrix2 matrices[8]{};
  std::int64_t lower[trace_fiber_lower_count]{};
  std::int64_t ordered[2]{};
  std::int64_t determinants[3]{};
  exact::word lineage{};
  bool valid{};
};
HOLONICS_CALLABLE inline void
form_heldout(const heldout_oriented_system_card &card,
             heldout_trace_source_secret &out) noexcept {
  using namespace elementary_matrix_detail;
  out = {};
  out.matrices[0] = multiply(card.edges[0], card.edges[1]);
  out.matrices[1] = multiply(card.edges[2], card.edges[3]);
  out.matrices[2] = multiply(card.edges[4], card.edges[5]);
  out.matrices[3] = multiply(out.matrices[0], out.matrices[1]);
  out.matrices[4] = multiply(out.matrices[0], out.matrices[2]);
  out.matrices[5] = multiply(out.matrices[1], out.matrices[2]);
  out.matrices[6] = multiply(out.matrices[3], out.matrices[2]);
  out.matrices[7] = multiply(out.matrices[4], out.matrices[1]);
  for (std::uint8_t i = 0; i < trace_fiber_lower_count; ++i)
    out.lower[i] = characteristic_matrix_detail::trace(out.matrices[i]);
  out.ordered[0] = characteristic_matrix_detail::trace(out.matrices[6]);
  out.ordered[1] = characteristic_matrix_detail::trace(out.matrices[7]);
  for (std::uint8_t i = 0; i < 3; ++i)
    out.determinants[i] = determinant(out.matrices[i]);
  out.lineage = card.metadata.lineage;
  out.valid = true;
}

} // namespace holonics::organ::trace_fiber_matrix_detail
