#pragma once

#include <holonics/organ/characteristic_matrix_law.hpp>
#include <holonics/organ/trace_law_discovery.hpp>

namespace holonics::organ::characteristic_census_detail {

[[nodiscard]] HOLONICS_CALLABLE inline std::uint16_t
offset(std::uint8_t source) noexcept {
  return static_cast<std::uint16_t>(source * characteristic_pair_stride);
}
[[nodiscard]] HOLONICS_CALLABLE inline bool
same_matrix(const exact_matrix2 &a, const exact_matrix2 &b) noexcept {
  return elementary_matrix_detail::equal(a, b);
}
[[nodiscard]] HOLONICS_CALLABLE inline bool
same_characteristic(const characteristic_pair_receipt &a,
                    const characteristic_pair_receipt &b) noexcept {
  return a.trace_first == b.trace_first && a.trace_second == b.trace_second &&
         a.trace_product == b.trace_product && a.trace_closed == b.trace_closed;
}
[[nodiscard]] HOLONICS_CALLABLE inline bool
same_group(const characteristic_group_receipt &g,
           const characteristic_pair_receipt &p) noexcept {
  const std::int64_t coordinates[4]{p.trace_first, p.trace_second,
                                    p.trace_product, p.trace_closed};
  for (std::uint8_t i = 0; i < 4; ++i)
    if (g.coordinates[i] != coordinates[i] || g.strata[i] != p.strata[i])
      return false;
  return g.closed_fixed_rank == p.fixed_ranks[3];
}
HOLONICS_CALLABLE inline void
add_group(characteristic_hypergeometry_receipt &out,
          const characteristic_pair_receipt &p) noexcept {
  std::uint16_t at = 0;
  while (at < out.group_count && !same_group(out.groups[at], p))
    ++at;
  if (at < out.group_count) {
    ++out.groups[at].population;
    return;
  }
  if (at >= characteristic_group_capacity)
    return;
  auto &g = out.groups[out.group_count++];
  const std::int64_t coordinates[4]{p.trace_first, p.trace_second,
                                    p.trace_product, p.trace_closed};
  for (std::uint8_t i = 0; i < 4; ++i) {
    g.coordinates[i] = coordinates[i];
    g.strata[i] = p.strata[i];
  }
  g.closed_fixed_rank = p.fixed_ranks[3];
  g.population = 1;
  g.valid = true;
}
HOLONICS_CALLABLE inline void
retain_witnesses(characteristic_hypergeometry_receipt &out) noexcept {
  for (std::uint8_t s = 0; s < characteristic_source_count; ++s) {
    const auto base = offset(s), count = out.pair_count[s];
    for (std::uint16_t i = 0; i < count && !out.witnesses[0].found; ++i)
      for (std::uint16_t j = i + 1; j < count; ++j) {
        const auto &a = out.pairs[base + i];
        const auto &b = out.pairs[base + j];
        if (a.trace_first == b.trace_first &&
            a.trace_second == b.trace_second &&
            a.trace_product != b.trace_product &&
            a.trace_closed != b.trace_closed) {
          out.witnesses[0] = {static_cast<std::uint16_t>(base + i),
                              static_cast<std::uint16_t>(base + j), 0, true};
          break;
        }
      }
  }
  const auto one = offset(1), two = offset(2);
  const auto common = out.pair_count[1] < out.pair_count[2] ? out.pair_count[1]
                                                            : out.pair_count[2];
  for (std::uint16_t i = 0; i < common && !out.witnesses[1].found; ++i)
    if (same_characteristic(out.pairs[one + i], out.pairs[two + i]))
      out.witnesses[1] = {static_cast<std::uint16_t>(one + i),
                          static_cast<std::uint16_t>(two + i), 1, true};
  for (std::uint16_t i = 0; i < common && !out.witnesses[3].found; ++i) {
    const auto &a = out.pairs[one + i];
    const auto &b = out.pairs[two + i];
    if (same_characteristic(a, b) &&
        (!same_matrix(a.first, b.first) || !same_matrix(a.second, b.second)))
      out.witnesses[3] = {static_cast<std::uint16_t>(one + i),
                          static_cast<std::uint16_t>(two + i), 3, true};
  }
  for (std::uint8_t s = 0;
       s < characteristic_source_count && !out.witnesses[2].found; ++s) {
    const auto base = offset(s);
    const auto words = out.words[s].count;
    for (std::uint16_t left = 0; left < words && !out.witnesses[2].found;
         ++left)
      for (std::uint16_t right = left + 1; right < words; ++right) {
        const auto forward =
            static_cast<std::uint16_t>(base + left * words + right);
        const auto reverse =
            static_cast<std::uint16_t>(base + right * words + left);
        const auto &a = out.pairs[forward];
        const auto &b = out.pairs[reverse];
        if (a.trace_closed == b.trace_closed &&
            !same_matrix(a.closed, b.closed)) {
          out.witnesses[2] = {forward, reverse, 2, true};
          break;
        }
      }
  }
  for (std::uint8_t s = 0;
       s < characteristic_source_count && !out.witnesses[4].found; ++s) {
    const auto base = offset(s), count = out.pair_count[s];
    for (std::uint16_t i = 0; i < count; ++i) {
      const auto &p = out.pairs[base + i];
      if (p.trace_first == 2 && p.trace_second == 2 && p.trace_closed != 2) {
        out.witnesses[4] = {static_cast<std::uint16_t>(base + i),
                            static_cast<std::uint16_t>(base + i), 4, true};
        break;
      }
    }
  }
  out.witnesses_complete = true;
  for (const auto &w : out.witnesses)
    out.witnesses_complete = out.witnesses_complete && w.found;
}
HOLONICS_CALLABLE inline void
close(characteristic_hypergeometry_receipt &out,
      characteristic_workspace &workspace) noexcept {
  std::uint16_t total = 0;
  for (std::uint8_t s = 0; s < characteristic_source_count; ++s) {
    const auto count = out.words[s].count;
    out.pair_count[s] = static_cast<std::uint16_t>(count * count);
    total = static_cast<std::uint16_t>(total + out.pair_count[s]);
    const auto base = offset(s);
    for (std::uint16_t i = 0; i < out.pair_count[s]; ++i) {
      const auto &p = out.pairs[base + i];
      trace_law_detail::insert(workspace.bases[s], p, 0);
      trace_law_detail::insert(workspace.bases[3], p, 0);
      ++out.closed_strata[static_cast<std::uint8_t>(p.strata[3] + 1)];
      add_group(out, p);
    }
  }
  for (std::uint8_t s = 0; s < characteristic_source_count; ++s)
    trace_law_detail::candidate(workspace.bases[s], out.pair_count[s], 0,
                                out.candidates[s]);
  trace_law_detail::candidate(workspace.bases[3], total, 0, out.candidates[3]);
  out.candidates[3].selected = true;
  workspace.bases[0] = {};
  for (std::uint8_t s = 0; s < characteristic_source_count; ++s) {
    const auto base = offset(s);
    for (std::uint16_t i = 0; i < out.pair_count[s]; ++i)
      trace_law_detail::insert(workspace.bases[0], out.pairs[base + i], 1);
  }
  trace_law_detail::candidate(workspace.bases[0], total, 1, out.candidates[4]);
  workspace.bases[0] = {};
  for (std::uint8_t s = 0; s < characteristic_source_count; ++s) {
    const auto base = offset(s);
    for (std::uint16_t i = 0; i < out.pair_count[s]; ++i)
      trace_law_detail::insert(workspace.bases[0], out.pairs[base + i], 2);
  }
  trace_law_detail::candidate(workspace.bases[0], total, 2, out.candidates[5]);
  workspace.bases[0] = {};
  for (std::uint16_t i = 0; i < 8; ++i)
    trace_law_detail::insert(workspace.bases[0], out.pairs[i], 0);
  trace_law_detail::candidate(workspace.bases[0], 8, 0, out.candidates[6]);
  for (std::uint8_t i = 0; i < characteristic_feature_count; ++i)
    out.organ.coefficients[i] = out.candidates[3].coefficients[i];
  out.organ.features = characteristic_feature_count;
  out.organ.primitive = out.candidates[3].primitive;
  out.organ.lineage = out.lineage;
  for (std::uint8_t s = 0; s < characteristic_source_count; ++s) {
    const auto base = offset(s);
    for (std::uint16_t i = 0; i < out.pair_count[s]; ++i)
      out.law_residuals += trace_law_detail::residual(out.organ.coefficients,
                                                      out.pairs[base + i]) != 0;
  }
  std::uint16_t grouped = 0;
  for (std::uint16_t i = 0; i < out.group_count; ++i)
    grouped = static_cast<std::uint16_t>(grouped + out.groups[i].population);
  const auto stratified = static_cast<std::uint16_t>(
      out.closed_strata[0] + out.closed_strata[1] + out.closed_strata[2]);
  retain_witnesses(out);
  out.census_complete =
      out.group_count != 0 && grouped == total && stratified == total;
  out.theory_formed =
      out.development_ports_distinct && out.census_complete &&
      out.witnesses_complete &&
      out.candidates[3].obstruction == hypergeometry_trace_obstruction::none &&
      out.candidates[4].obstruction ==
          hypergeometry_trace_obstruction::full_rank &&
      out.candidates[5].obstruction ==
          hypergeometry_trace_obstruction::full_rank &&
      out.candidates[6].obstruction ==
          hypergeometry_trace_obstruction::insufficient_rows &&
      out.law_residuals == 0;
}

} // namespace holonics::organ::characteristic_census_detail
