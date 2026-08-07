#pragma once

#include <holonics/codec/trace_fiber_face.hpp>
#include <holonics/event/trace_fiber_rest.hpp>

namespace holonics::event {

[[nodiscard]] HOLONICS_CALLABLE inline codec::trace_fiber_triple_surface
trace_fiber_triple_surface(const organ::transition_triple_receipt &t) noexcept {
  codec::trace_fiber_triple_surface out{};
  for (std::uint8_t i = 0; i < 8; ++i)
    for (std::uint8_t j = 0; j < 4; ++j)
      out.matrices[i].value[j] = t.matrices[i].value[j];
  for (std::uint8_t i = 0; i < 6; ++i)
    out.lower[i] = t.lower[i];
  for (std::uint8_t i = 0; i < 2; ++i)
    out.ordered[i] = t.ordered[i];
  for (std::uint8_t i = 0; i < 3; ++i)
    out.words[i] = t.words[i];
  out.source = t.source;
  return out;
}
[[nodiscard]] HOLONICS_CALLABLE inline codec::trace_fiber_discovery_surface
trace_fiber_surface(const organ::trace_fiber_discovery_receipt &r) noexcept {
  codec::trace_fiber_discovery_surface out{};
  for (std::uint8_t target = 0; target < 2; ++target)
    for (std::uint8_t i = 0; i < organ::trace_fiber_feature_count; ++i)
      out.coefficients[target][i] = r.organs[target].coefficients[i];
  for (std::uint8_t i = 0; i < organ::trace_fiber_witness_count; ++i) {
    out.witnesses[i][0] = trace_fiber_triple_surface(r.triples[r.witnesses[i].first]);
    out.witnesses[i][1] = trace_fiber_triple_surface(r.triples[r.witnesses[i].second]);
  }
  for (std::uint8_t i = 0; i < 3; ++i)
    out.triple_count[i] = r.triple_count[i];
  out.group_count = r.group_count;
  out.branch_count = r.branch_count;
  out.two_sheet_count = r.two_sheet_count;
  out.passage = r.passage;
  out.exact = r.theory_formed;
  return out;
}
[[nodiscard]] HOLONICS_CALLABLE inline codec::heldout_trace_fiber_surface
heldout_trace_fiber_surface(const organ::heldout_trace_fiber_receipt &r) noexcept {
  codec::heldout_trace_fiber_surface out{};
  for (std::uint8_t i = 0; i < 8; ++i)
    for (std::uint8_t j = 0; j < 4; ++j)
      out.matrices[i].value[j] = r.matrices[i].value[j];
  for (std::uint8_t i = 0; i < 6; ++i)
    out.lower[i] = r.lower[i];
  for (std::uint8_t i = 0; i < 2; ++i) {
    out.symmetric[i] = r.symmetric[i];
    out.roots[i] = r.roots[i];
  }
  for (std::uint8_t i = 0; i < 3; ++i)
    out.quadratic[i] = r.quadratic[i];
  out.anchor = r.anchor;
  out.companion = r.predicted_companion;
  out.source_companion = r.source_companion;
  out.discriminant = r.discriminant;
  out.passage = r.passage;
  out.prediction_before_comparison = r.prediction_before_comparison;
  out.source_detached = r.development_sources_absent;
  out.exact = r.theory_formed;
  return out;
}
[[nodiscard]] HOLONICS_CALLABLE inline codec::trace_fiber_discovery_surface
rested_trace_fiber_surface(const trace_fiber_law_bundle &law) noexcept {
  codec::trace_fiber_discovery_surface out{};
  for (std::uint8_t target = 0; target < 2; ++target)
    for (std::uint8_t i = 0; i < organ::trace_fiber_feature_count; ++i)
      out.coefficients[target][i] = law.organs[target].coefficients[i];
  for (std::uint8_t i = 0; i < 3; ++i)
    out.triple_count[i] = law.triple_count[i];
  out.group_count = law.group_count;
  out.branch_count = law.branch_count;
  out.two_sheet_count = law.two_sheet_count;
  out.passage = law.discovery.passage;
  out.exact = law.checker_founded;
  return out;
}

} // namespace holonics::event
