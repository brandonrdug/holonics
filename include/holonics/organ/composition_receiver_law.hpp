#pragma once

#include <holonics/organ/elementary_calculus_receipt.hpp>

namespace holonics::organ::composition_receiver_detail {

HOLONICS_CALLABLE inline void derive_composition(const composition_card &card,
    composition_receipt &out) noexcept {
  for (std::uint8_t index = 0; index < card.case_count; ++index) {
    const auto &source = card.cases[index]; auto &result = out.signatures[index];
    result.visible = source.visible; result.contact = source.contact;
    result.predecessor_link = source.predecessor_link;
    result.forward_complete = source.forward_available && source.forward[1] == 0;
    result.reverse_complete = source.reverse_available && source.reverse[1] == 0;
    result.obstruction_present = source.forward[1] != 0 || source.reverse[1] != 0;
    result.complete_equal = result.forward_complete && result.reverse_complete;
    for (std::uint8_t field = 0; field < 4; ++field) {
      result.residual[field] = source.forward[field] - source.reverse[field];
      result.complete_equal = result.complete_equal && result.residual[field] == 0;
    }
    if (source.predecessor_link && result.forward_complete && !source.reverse_available)
      result.code = successor_signature_code::ordered;
    else if (result.complete_equal && !result.obstruction_present)
      result.code = successor_signature_code::equal_complete;
    else if (source.contact && result.forward_complete && result.reverse_complete)
      result.code = successor_signature_code::residual_complete;
    else if (result.obstruction_present && !result.forward_complete)
      result.code = successor_signature_code::blocked;
    else result.code = successor_signature_code::unresolved;
  }
  out.pairwise_distinct = true;
  for (std::uint8_t i = 0; i < card.case_count; ++i)
    for (std::uint8_t j = i + 1U; j < card.case_count; ++j)
      out.pairwise_distinct = out.pairwise_distinct &&
          out.signatures[i].code != out.signatures[j].code;
  const auto &counter = card.cases[2];
  out.scalar_only_refuted = counter.forward[0] == counter.reverse[0] &&
      (counter.forward[2] != counter.reverse[2] || counter.forward[3] != counter.reverse[3]);
  out.theory_formed = card.case_count == elementary_composition_count &&
      out.pairwise_distinct && out.scalar_only_refuted;
}

[[nodiscard]] HOLONICS_CALLABLE inline bool factors(const std::int64_t *question,
    const std::int64_t *consequence, std::uint8_t count) noexcept {
  for (std::uint8_t left = 0; left < count; ++left)
    for (std::uint8_t right = left + 1U; right < count; ++right)
      if (question[left] == question[right] && consequence[left] != consequence[right]) return false;
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE inline std::uint8_t fiber_count(
    const std::int64_t *question, std::uint8_t count) noexcept {
  std::uint8_t result = 0;
  for (std::uint8_t i = 0; i < count; ++i) {
    bool first = true;
    for (std::uint8_t j = 0; j < i; ++j) first = first && question[j] != question[i];
    if (first) ++result;
  }
  return result;
}

HOLONICS_CALLABLE inline void derive_receiver(const receiver_card &card,
    receiver_receipt &out) noexcept {
  for (std::uint8_t left = 0; left < card.source_count; ++left)
    for (std::uint8_t right = left + 1U; right < card.source_count; ++right) {
      auto &pair = out.pairs[out.pair_count++]; pair.left = left; pair.right = right;
      pair.same_coarse = card.coarse[left] == card.coarse[right];
      pair.same_fine = card.fine[left] == card.fine[right];
      pair.same_first = card.first_consequence[left] == card.first_consequence[right];
      pair.same_strict = card.strict_consequence[left] == card.strict_consequence[right];
      if (pair.same_coarse && !pair.same_strict) ++out.coarse_strict_witnesses;
    }
  out.coarse_fibers = fiber_count(card.coarse, card.source_count);
  out.fine_fibers = fiber_count(card.fine, card.source_count);
  out.first_factors_coarse = factors(card.coarse, card.first_consequence, card.source_count);
  out.strict_factors_coarse = factors(card.coarse, card.strict_consequence, card.source_count);
  out.strict_factors_fine = factors(card.fine, card.strict_consequence, card.source_count);
  out.refinement_exact = true;
  for (const auto &pair : out.pairs) out.refinement_exact = out.refinement_exact &&
      (!pair.same_fine || pair.same_coarse);
  out.unequal_sources_retained = out.pairs[0].same_coarse && out.pairs[0].left != out.pairs[0].right;
  out.theory_formed = out.pair_count == 15 && out.coarse_fibers == 2 && out.fine_fibers == 4 &&
      out.first_factors_coarse && !out.strict_factors_coarse && out.strict_factors_fine &&
      out.coarse_strict_witnesses == 4 && out.refinement_exact && out.unequal_sources_retained;
}

}  // namespace holonics::organ::composition_receiver_detail
