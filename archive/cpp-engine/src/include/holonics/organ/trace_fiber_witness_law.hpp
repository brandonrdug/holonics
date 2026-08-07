#pragma once

#include <holonics/organ/trace_fiber_census_law.hpp>

namespace holonics::organ::trace_fiber_witness_detail {

HOLONICS_CALLABLE inline void retain(trace_fiber_discovery_receipt &out) noexcept {
  for (std::uint8_t s = 0; s < trace_fiber_source_count &&
                           !out.witnesses[0].found;
       ++s) {
    const auto base = trace_fiber_census_detail::offset(s);
    for (std::uint8_t a = 0; a < trace_fiber_word_count &&
                             !out.witnesses[0].found;
         ++a)
      for (std::uint8_t b = 0; b < trace_fiber_word_count; ++b)
        for (std::uint8_t c = static_cast<std::uint8_t>(b + 1U);
             c < trace_fiber_word_count; ++c) {
          const auto first = static_cast<std::uint16_t>(
              base + a * 144U + b * 12U + c);
          const auto second = static_cast<std::uint16_t>(
              base + a * 144U + c * 12U + b);
          const auto &x = out.triples[first];
          const auto &y = out.triples[second];
          if (trace_fiber_census_detail::same_lower(x, y) && !x.branch &&
              x.ordered[0] == y.ordered[1] &&
              x.ordered[1] == y.ordered[0]) {
            out.witnesses[0] = {first, second, 0, true};
            break;
          }
        }
  }
  const auto zero = trace_fiber_census_detail::offset(0);
  const auto one = trace_fiber_census_detail::offset(1);
  for (std::uint16_t i = 0; i < trace_fiber_triple_stride &&
                            !out.witnesses[1].found;
       ++i)
    for (std::uint16_t j = 0; j < trace_fiber_triple_stride; ++j) {
      const auto &a = out.triples[zero + i];
      const auto &b = out.triples[one + j];
      if (trace_fiber_census_detail::same_fiber(a, b) &&
          (!trace_fiber_census_detail::same_matrix(a.matrices[0], b.matrices[0]) ||
           !trace_fiber_census_detail::same_matrix(a.matrices[1], b.matrices[1]) ||
           !trace_fiber_census_detail::same_matrix(a.matrices[2], b.matrices[2]))) {
        out.witnesses[1] = {static_cast<std::uint16_t>(zero + i),
                            static_cast<std::uint16_t>(one + j), 1, true};
        break;
      }
    }
  const auto two = trace_fiber_census_detail::offset(2);
  for (std::uint16_t i = 0; i < trace_fiber_triple_stride &&
                            !out.witnesses[2].found;
       ++i) {
    const auto &a = out.triples[one + i];
    const auto &b = out.triples[two + i];
    if (trace_fiber_census_detail::same_fiber(a, b) &&
        (!trace_fiber_census_detail::same_matrix(a.matrices[0], b.matrices[0]) ||
         !trace_fiber_census_detail::same_matrix(a.matrices[1], b.matrices[1]) ||
         !trace_fiber_census_detail::same_matrix(a.matrices[2], b.matrices[2])))
      out.witnesses[2] = {static_cast<std::uint16_t>(one + i),
                          static_cast<std::uint16_t>(two + i), 2, true};
  }
  for (std::uint16_t i = 0; i < trace_fiber_triple_capacity; ++i) {
    if (!out.witnesses[3].found && out.triples[i].branch)
      out.witnesses[3] = {i, i, 3, true};
    if (!out.witnesses[4].found && !out.triples[i].branch)
      out.witnesses[4] = {i, i, 4, true};
  }
  out.witnesses_complete = true;
  for (const auto &w : out.witnesses)
    out.witnesses_complete = out.witnesses_complete && w.found;
}

} // namespace holonics::organ::trace_fiber_witness_detail
