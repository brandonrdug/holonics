#pragma once

#include <holonics/codec/cultivated_organ_face.hpp>
#include <holonics/organ/cultivated_organ_receipt.hpp>

namespace holonics::event {

HOLONICS_CALLABLE inline void project_kernel(
    const organ::cultivated_shift_organ &source,
    codec::cultivated_kernel_surface &out) noexcept {
  out.order = source.order; out.degree = source.degree; out.features = source.features;
  for (std::uint8_t i = 0; i < source.features; ++i) out.coefficients[i] = source.coefficients[i];
}

[[nodiscard]] HOLONICS_CALLABLE inline codec::cultivation_surface cultivation_surface(
    const organ::developmental_stream_card (&cards)[organ::cultivation_family_count],
    const organ::cultivation_receipt &receipt) noexcept {
  codec::cultivation_surface out{}; out.passage = receipt.passage; out.exact = receipt.theory_formed;
  for (std::uint8_t family = 0; family < organ::cultivation_family_count; ++family) {
    auto &kernel = out.kernels[family]; project_kernel(receipt.families[family].candidate, kernel);
    kernel.series_count = cards[family].series_count;
    for (std::uint8_t series = 0; series < kernel.series_count; ++series) {
      kernel.sample_count[series] = cards[family].sample_count[series];
      for (std::uint8_t i = 0; i < kernel.sample_count[series]; ++i)
        kernel.samples[series][i] = cards[family].samples[series][i];
    }
  }
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE inline codec::cultivated_application_surface
cultivated_application_surface(const organ::heldout_application_receipt &receipt,
    const organ::cultivated_shift_organ (&organs)[organ::cultivation_family_count]) noexcept {
  codec::cultivated_application_surface out{}; out.passage = receipt.passage;
  out.source_detached = receipt.development_sources_absent; out.exact = receipt.theory_formed;
  for (std::uint8_t family = 0; family < organ::cultivation_family_count; ++family) {
    project_kernel(organs[family], out.kernels[family]);
    const auto &source = receipt.tails[family]; auto &tail = out.tails[family];
    tail.sample_count = source.sample_count; tail.prefix_count = source.prefix_count;
    tail.changed_source = static_cast<std::uint8_t>(source.changed_source);
    tail.short_prefix = static_cast<std::uint8_t>(source.short_prefix);
    tail.exclusion = static_cast<std::uint8_t>(source.exclusion); tail.exact = source.exact;
    for (std::uint8_t i = 0; i < source.sample_count; ++i) {
      tail.source[i] = source.source[i]; tail.predicted[i] = source.predicted[i];
    }
  }
  return out;
}

}  // namespace holonics::event
