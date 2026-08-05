#pragma once

#include <holonics/organ/trace_fiber_witness_law.hpp>

namespace holonics::organ::trace_fiber_close_detail {

[[nodiscard]] HOLONICS_CALLABLE inline bool selected_controls(
    const trace_fiber_discovery_receipt &out) noexcept {
  bool exact = out.candidates[3].obstruction == trace_fiber_obstruction::none &&
               out.candidates[7].obstruction == trace_fiber_obstruction::none;
  for (std::uint8_t i = 0; i < 3; ++i) {
    exact = exact && out.candidates[i].obstruction == trace_fiber_obstruction::none &&
            out.candidates[4U + i].obstruction == trace_fiber_obstruction::none &&
            trace_fiber_discovery_detail::same_coefficients(out.candidates[0],
                                                             out.candidates[i]) &&
            trace_fiber_discovery_detail::same_coefficients(out.candidates[4],
                                                             out.candidates[4U + i]);
  }
  for (std::uint8_t i = 8; i < 12; ++i)
    exact = exact &&
            out.candidates[i].obstruction == trace_fiber_obstruction::full_rank;
  return exact &&
         out.candidates[12].obstruction ==
             trace_fiber_obstruction::insufficient_rows &&
         out.candidates[13].obstruction == trace_fiber_obstruction::full_rank;
}
HOLONICS_CALLABLE inline void close(trace_fiber_discovery_receipt &out,
                                    trace_fiber_workspace &workspace) noexcept {
  std::uint16_t population = 0;
  for (std::uint8_t s = 0; s < trace_fiber_source_count; ++s) {
    out.triple_count[s] = trace_fiber_triple_stride;
    const auto base = trace_fiber_census_detail::offset(s);
    for (std::uint16_t i = 0; i < trace_fiber_triple_stride; ++i) {
      const auto &t = out.triples[base + i];
      out.census_complete = out.census_complete || t.valid;
      if (t.branch)
        ++out.branch_count;
      else
        ++out.two_sheet_count;
      trace_fiber_census_detail::add_group(out, t);
      ++population;
    }
  }
  trace_fiber_census_detail::discover(out, workspace);
  for (std::uint8_t target = 0; target < 2; ++target) {
    const auto selected = static_cast<std::uint8_t>(target == 0 ? 3 : 7);
    for (std::uint8_t i = 0; i < trace_fiber_feature_count; ++i)
      out.organs[target].coefficients[i] =
          out.candidates[selected].coefficients[i];
    out.organs[target].target = static_cast<trace_fiber_target>(target);
    out.organs[target].lineage = out.lineage;
    out.organs[target].primitive = out.candidates[selected].primitive;
  }
  for (std::uint16_t i = 0; i < trace_fiber_triple_capacity; ++i)
    for (std::uint8_t target = 0; target < 2; ++target)
      out.residuals = static_cast<std::uint16_t>(
          out.residuals +
          (trace_fiber_discovery_detail::residual(
               out.organs[target].coefficients, out.triples[i],
               static_cast<trace_fiber_target>(target)) != 0));
  std::uint16_t grouped = 0;
  for (std::uint16_t i = 0; i < out.group_count; ++i)
    grouped = static_cast<std::uint16_t>(grouped + out.groups[i].population);
  trace_fiber_witness_detail::retain(out);
  out.census_complete =
      population == trace_fiber_triple_capacity && grouped == population &&
      out.branch_count + out.two_sheet_count == population;
  out.theory_formed = out.development_ports_distinct && out.census_complete &&
                      out.witnesses_complete && selected_controls(out) &&
                      out.residuals == 0;
}

} // namespace holonics::organ::trace_fiber_close_detail
