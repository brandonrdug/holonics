#pragma once

#include <holonics/organ/hodge_cycle_locus_law.hpp>

namespace holonics::organ::hodge_cycle_detail {

HOLONICS_CALLABLE constexpr void close(const hodge_realization_card& card,
    const hodge_product_receipt& product, hodge_cycle_receipt& out) noexcept {
  out.translations_distinct = true;
  for (std::uint8_t left = 0; left < 4; ++left) {
    for (std::uint8_t right = static_cast<std::uint8_t>(left + 1U); right < 4; ++right) {
      out.translations_distinct = out.translations_distinct &&
          out.translations[left].support != out.translations[right].support;
    }
  }
  derive_locus(product, card.lineage.value(), out.locus); derive_generators(out);
  for (std::uint8_t target = 0; target < 3; ++target) {
    derive_fiber(card, out.generators, target, out.fibers[target]);
  }
  out.identity = exact::word{195'580}; out.lineage = exact::word{card.lineage.value() + 256U};
  out.image_rank = 3;
  bool translations_exact = true;
  for (const auto& translation : out.translations) {
    translations_exact = translations_exact && translation.exact;
  }
  out.graph_relation_exact = true;
  for (std::uint8_t slot = 0; slot < 6; ++slot) {
    out.graph_relation_exact = out.graph_relation_exact &&
        out.locus.graph_class[slot] + out.locus.negation_class[slot] ==
        2 * product.polarization[slot];
  }
  out.rational_integral_separated = out.fibers[0].integral_member &&
      !out.fibers[1].integral_member && out.fibers[2].outside_image;
  out.alternatives_retained = out.fibers[0].realizer_count == 16 &&
      out.fibers[1].realizer_count == 16;
  out.exact = translations_exact && out.translations_distinct && out.locus.exact &&
      out.graph_relation_exact && out.rational_integral_separated &&
      out.alternatives_retained && out.fibers[0].exact && out.fibers[1].exact &&
      out.fibers[2].exact;
}

}  // namespace holonics::organ::hodge_cycle_detail
