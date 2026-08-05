#pragma once

#include <holonics/organ/shift_organ_cultivation_law.hpp>

namespace holonics::organ::cultivation_realization_detail {

HOLONICS_CALLABLE inline void close(cultivation_receipt &out,
                                    cultivation_workspace &workspace) noexcept {
  out.development_ports_distinct = true;
  out.all_candidates_exact = true;
  for (std::uint8_t i = 0; i < cultivation_family_count; ++i) {
    out.all_candidates_exact = out.all_candidates_exact &&
        out.families[i].source_current_independent && out.families[i].selected_exact;
    for (std::uint8_t j = i + 1U; j < cultivation_family_count; ++j)
      out.development_ports_distinct = out.development_ports_distinct &&
          out.families[i].candidate.lineage != out.families[j].candidate.lineage;
  }
  developmental_stream_card constant{};
  constant.series_count = 1; constant.sample_count[0] = 4;
  for (std::uint8_t i = 0; i < 4; ++i) constant.samples[0][i] = exact::small_rational_law::make(1);
  feature_geometry_receipt nonunique{};
  shift_cultivation_detail::derive_candidate(constant, 2, 0, workspace.matrices[0], nonunique);
  out.controls.constant_stream = nonunique.obstruction;
  developmental_stream_card short_card{};
  short_card.series_count = 1; short_card.sample_count[0] = 1;
  short_card.samples[0][0] = exact::small_rational_law::make(1);
  feature_geometry_receipt short_receipt{};
  shift_cultivation_detail::derive_candidate(short_card, 1, 0,
      workspace.matrices[0], short_receipt);
  out.controls.short_stream = short_receipt.obstruction;
  out.passage = exact::word{198'400}; out.lineage = exact::word{510'131};
  out.atlas_rows = 38;
  out.theory_formed = out.development_ports_distinct && out.all_candidates_exact &&
      out.controls.constant_stream == cultivation_obstruction::nonunique_kernel &&
      out.controls.short_stream == cultivation_obstruction::insufficient_rows;
}

}  // namespace holonics::organ::cultivation_realization_detail
