#pragma once

#include <holonics/organ/trace_fiber_discovery_law.hpp>
#include <holonics/organ/trace_fiber_matrix_law.hpp>

namespace holonics::organ::trace_fiber_census_detail {

[[nodiscard]] HOLONICS_CALLABLE inline std::uint16_t
offset(std::uint8_t source) noexcept {
  return static_cast<std::uint16_t>(source * trace_fiber_triple_stride);
}
[[nodiscard]] HOLONICS_CALLABLE inline bool same_matrix(
    const exact_matrix2 &a, const exact_matrix2 &b) noexcept {
  return elementary_matrix_detail::equal(a, b);
}
[[nodiscard]] HOLONICS_CALLABLE inline bool same_lower(
    const transition_triple_receipt &a,
    const transition_triple_receipt &b) noexcept {
  for (std::uint8_t i = 0; i < trace_fiber_lower_count; ++i)
    if (a.lower[i] != b.lower[i])
      return false;
  return true;
}
HOLONICS_CALLABLE inline void sorted_roots(
    const transition_triple_receipt &t, std::int64_t (&roots)[2]) noexcept {
  roots[0] = t.ordered[0] < t.ordered[1] ? t.ordered[0] : t.ordered[1];
  roots[1] = t.ordered[0] < t.ordered[1] ? t.ordered[1] : t.ordered[0];
}
[[nodiscard]] HOLONICS_CALLABLE inline bool same_fiber(
    const transition_triple_receipt &a,
    const transition_triple_receipt &b) noexcept {
  std::int64_t ar[2]{}, br[2]{};
  sorted_roots(a, ar);
  sorted_roots(b, br);
  return same_lower(a, b) && ar[0] == br[0] && ar[1] == br[1];
}
/// Assemble one triple into the census, given the first index carrying its key.
///
/// This replaces a linear scan over every group already inserted. The scan cost
/// 5,184 insertions against up to 2,304 groups — about ten million comparisons
/// on a single device thread — and the answer it computed is exactly `first_of`,
/// which a kernel can compute for every triple at once.
HOLONICS_CALLABLE inline void place_group(trace_fiber_discovery_receipt &out,
                                          trace_fiber_workspace &workspace,
                                          std::uint16_t index) noexcept {
  const auto &t = out.triples[index];
  const std::uint16_t first = workspace.first_of[index];
  if (first != index) {
    const std::uint16_t at = workspace.ordinal_of[first];
    workspace.ordinal_of[index] = at;
    if (at < trace_fiber_group_capacity) {
      ++out.groups[at].population;
    }
    return;
  }
  if (out.group_count >= trace_fiber_group_capacity) {
    workspace.ordinal_of[index] = trace_fiber_group_capacity;
    return;
  }
  std::int64_t roots[2]{};
  sorted_roots(t, roots);
  auto &g = out.groups[out.group_count];
  for (std::uint8_t i = 0; i < trace_fiber_lower_count; ++i)
    g.lower[i] = t.lower[i];
  g.roots[0] = roots[0];
  g.roots[1] = roots[1];
  g.population = 1;
  g.branch = t.branch;
  g.valid = true;
  workspace.ordinal_of[index] = out.group_count;
  ++out.group_count;
}

HOLONICS_CALLABLE inline void add_group(trace_fiber_discovery_receipt &out,
                                        const transition_triple_receipt &t) noexcept {
  std::int64_t roots[2]{};
  sorted_roots(t, roots);
  std::uint16_t at = 0;
  for (; at < out.group_count; ++at) {
    bool same = out.groups[at].roots[0] == roots[0] &&
                out.groups[at].roots[1] == roots[1];
    for (std::uint8_t i = 0; i < trace_fiber_lower_count; ++i)
      same = same && out.groups[at].lower[i] == t.lower[i];
    if (same)
      break;
  }
  if (at < out.group_count) {
    ++out.groups[at].population;
    return;
  }
  if (out.group_count >= trace_fiber_group_capacity)
    return;
  auto &g = out.groups[out.group_count++];
  for (std::uint8_t i = 0; i < trace_fiber_lower_count; ++i)
    g.lower[i] = t.lower[i];
  g.roots[0] = roots[0];
  g.roots[1] = roots[1];
  g.population = 1;
  g.branch = t.branch;
  g.valid = true;
}
HOLONICS_CALLABLE inline void build_candidate(
    trace_fiber_discovery_receipt &out, trace_fiber_workspace &workspace,
    std::uint8_t source, trace_fiber_target target,
    trace_fiber_feature_mode mode, std::uint16_t row_limit,
    trace_fiber_candidate_receipt &candidate) noexcept {
  for (std::uint8_t row = 0; row < trace_fiber_feature_count; ++row) {
    workspace.basis.pivots[row] = 0;
    for (std::uint8_t column = 0; column < trace_fiber_feature_count; ++column) {
      workspace.basis.rows[row][column].numerator = 0;
      workspace.basis.rows[row][column].denominator = 1;
    }
  }
  workspace.basis.rank = 0;
  workspace.basis.exact = true;
  const auto count = row_limit < out.triple_count[source]
                         ? row_limit
                         : out.triple_count[source];
  const auto features = trace_fiber_feature_detail::feature_count(mode);
  const auto wanted = mode == trace_fiber_feature_mode::complete
                          ? static_cast<std::uint8_t>(features - 1U)
                          : features;
  const auto base = offset(source);
  for (std::uint16_t i = 0; i < count && workspace.basis.rank < wanted; ++i)
    trace_fiber_feature_detail::insert(workspace.basis, out.triples[base + i],
                                       target, mode);
  trace_fiber_discovery_detail::candidate(workspace.basis, count, target, mode,
                                          candidate);
}
HOLONICS_CALLABLE inline void discover(trace_fiber_discovery_receipt &out,
                                       trace_fiber_workspace &workspace) noexcept {
  for (std::uint8_t s = 0; s < trace_fiber_source_count; ++s)
    build_candidate(out, workspace, s, trace_fiber_target::sum,
                    trace_fiber_feature_mode::complete,
                    out.triple_count[s], out.candidates[s]);
  out.candidates[3] = out.candidates[0];
  out.candidates[3].rows = trace_fiber_triple_capacity;
  out.candidates[3].selected = true;
  for (std::uint8_t s = 0; s < trace_fiber_source_count; ++s)
    build_candidate(out, workspace, s, trace_fiber_target::product,
                    trace_fiber_feature_mode::complete,
                    out.triple_count[s], out.candidates[4U + s]);
  out.candidates[7] = out.candidates[4];
  out.candidates[7].rows = trace_fiber_triple_capacity;
  out.candidates[7].selected = true;
  build_candidate(out, workspace, 0, trace_fiber_target::sum,
                  trace_fiber_feature_mode::degree_two,
                  out.triple_count[0], out.candidates[8]);
  build_candidate(out, workspace, 0, trace_fiber_target::product,
                  trace_fiber_feature_mode::degree_two,
                  out.triple_count[0], out.candidates[9]);
  build_candidate(out, workspace, 0, trace_fiber_target::sum,
                  trace_fiber_feature_mode::sixth_coordinate_deleted,
                  out.triple_count[0], out.candidates[10]);
  build_candidate(out, workspace, 0, trace_fiber_target::product,
                  trace_fiber_feature_mode::sixth_coordinate_deleted,
                  out.triple_count[0], out.candidates[11]);
  build_candidate(out, workspace, 0, trace_fiber_target::sum,
                  trace_fiber_feature_mode::complete, 16, out.candidates[12]);
  build_candidate(out, workspace, 0, trace_fiber_target::sum,
                  trace_fiber_feature_mode::target_deleted,
                  out.triple_count[0], out.candidates[13]);
}

} // namespace holonics::organ::trace_fiber_census_detail
