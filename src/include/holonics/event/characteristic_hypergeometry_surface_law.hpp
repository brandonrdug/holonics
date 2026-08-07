#pragma once

#include <holonics/codec/characteristic_hypergeometry_face.hpp>

namespace holonics::event {

[[nodiscard]] HOLONICS_CALLABLE inline codec::
    characteristic_hypergeometry_surface
    characteristic_surface(
        const organ::characteristic_hypergeometry_receipt &r) noexcept {
  codec::characteristic_hypergeometry_surface out{};
  for (std::uint8_t i = 0; i < organ::characteristic_feature_count; ++i)
    out.coefficients[i] = r.organ.coefficients[i];
  for (std::uint8_t i = 0; i < organ::characteristic_source_count; ++i)
    out.pair_count[i] = r.pair_count[i];
  out.group_count = r.group_count;
  for (std::uint8_t i = 0; i < 3; ++i)
    out.closed_strata[i] = r.closed_strata[i];
  for (std::uint8_t i = 0; i < organ::characteristic_witness_count; ++i)
    for (std::uint8_t j = 0; j < 2; ++j) {
      const auto &p = r.pairs[j == 0 ? r.witnesses[i].first_pair
                                     : r.witnesses[i].second_pair];
      auto &target = out.witnesses[i][j];
      for (std::uint8_t k = 0; k < 4; ++k) {
        target.first.value[k] = p.first.value[k];
        target.second.value[k] = p.second.value[k];
        target.product.value[k] = p.product.value[k];
        target.closed.value[k] = p.closed.value[k];
      }
      target.trace_first = p.trace_first;
      target.trace_second = p.trace_second;
      target.trace_product = p.trace_product;
      target.trace_closed = p.trace_closed;
      target.left_word = p.left_word;
      target.right_word = p.right_word;
      target.source = p.source;
    }
  out.passage = r.passage;
  out.exact = r.theory_formed;
  return out;
}
[[nodiscard]] HOLONICS_CALLABLE inline codec::heldout_characteristic_surface
heldout_characteristic_surface(
    const organ::heldout_characteristic_receipt &r) noexcept {
  codec::heldout_characteristic_surface out{};
  for (std::uint8_t i = 0; i < 3; ++i) {
    out.visible[i] = r.visible[i];
    out.characteristic[i] = r.characteristic[i];
  }
  out.predicted_trace = r.predicted_trace;
  out.source_trace = r.source_trace;
  out.predicted_discriminant = r.predicted_discriminant;
  out.fixed_rank = r.predicted_fixed_rank;
  out.passage = r.passage;
  out.prediction_before_comparison = r.prediction_before_comparison;
  out.source_detached = r.development_sources_absent;
  out.exact = r.theory_formed;
  return out;
}
[[nodiscard]] HOLONICS_CALLABLE inline codec::
    characteristic_hypergeometry_surface
    rested_characteristic_surface(
        const characteristic_law_bundle &law) noexcept {
  codec::characteristic_hypergeometry_surface out{};
  for (std::uint8_t i = 0; i < organ::characteristic_feature_count; ++i)
    out.coefficients[i] = law.organ.coefficients[i];
  out.group_count = law.group_count;
  for (std::uint8_t i = 0; i < 3; ++i) {
    out.pair_count[i] = law.pair_count[i];
    out.closed_strata[i] = law.closed_strata[i];
  }
  out.passage = law.discovery.passage;
  out.exact = law.checker_founded;
  return out;
}

} // namespace holonics::event
