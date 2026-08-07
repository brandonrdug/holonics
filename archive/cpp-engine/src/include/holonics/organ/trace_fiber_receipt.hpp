#pragma once

#include <holonics/organ/trace_fiber_schema.hpp>

namespace holonics::organ {

enum class trace_fiber_obstruction : std::uint8_t {
  none,
  insufficient_rows,
  full_rank,
  nonunique_kernel,
  invalid_exact_row,
  residual,
  witness_absent,
  organ_absent,
  orientation_unresolved,
  unsupported_determinant,
  negative_discriminant,
  nonsquare_discriminant,
  comparison_residual
};
struct transition_triple_receipt final {
  exact_matrix2 matrices[8]{};
  std::int64_t lower[trace_fiber_lower_count]{};
  std::int64_t ordered[2]{};
  std::int64_t symmetric[2]{};
  std::int64_t discriminant{};
  std::int64_t root_gap{};
  std::uint16_t words[3]{};
  std::uint8_t source{};
  bool branch{};
  bool valid{};
};
struct trace_fiber_group_receipt final {
  std::int64_t lower[trace_fiber_lower_count]{};
  std::int64_t roots[2]{};
  std::uint16_t population{};
  bool branch{};
  bool valid{};
};
struct trace_fiber_candidate_receipt final {
  std::int64_t coefficients[trace_fiber_feature_count]{};
  std::uint16_t rows{};
  std::uint8_t features{};
  std::uint8_t rank{};
  std::uint8_t nullity{};
  trace_fiber_target target{trace_fiber_target::sum};
  trace_fiber_feature_mode mode{trace_fiber_feature_mode::complete};
  trace_fiber_obstruction obstruction{trace_fiber_obstruction::insufficient_rows};
  bool primitive{};
  bool selected{};
};
struct trace_fiber_collision_receipt final {
  std::uint16_t first{};
  std::uint16_t second{};
  std::uint8_t kind{};
  bool found{};
};
struct trace_fiber_organ final {
  std::int64_t coefficients[trace_fiber_feature_count]{};
  exact::word identity{};
  exact::word passage{};
  exact::word returned_event{};
  exact::word lineage{};
  trace_fiber_target target{trace_fiber_target::sum};
  bool primitive{};
  bool checker_founded{};
};
struct trace_fiber_discovery_receipt final {
  transition_word_population words[trace_fiber_source_count]{};
  transition_triple_receipt triples[trace_fiber_triple_capacity]{};
  trace_fiber_group_receipt groups[trace_fiber_group_capacity]{};
  trace_fiber_candidate_receipt candidates[trace_fiber_candidate_count]{};
  trace_fiber_collision_receipt witnesses[trace_fiber_witness_count]{};
  trace_fiber_organ organs[2]{};
  std::uint16_t triple_count[trace_fiber_source_count]{};
  std::uint16_t group_count{};
  std::uint16_t branch_count{};
  std::uint16_t two_sheet_count{};
  std::uint16_t residuals{};
  exact::word passage{};
  exact::word lineage{};
  bool development_ports_distinct{};
  bool census_complete{};
  bool witnesses_complete{};
  bool theory_formed{};
};
struct trace_fiber_basis final {
  exact::small_rational rows[trace_fiber_feature_count]
                            [trace_fiber_feature_count]{};
  std::uint8_t pivots[trace_fiber_feature_count]{};
  std::uint8_t rank{};
  bool exact{true};
};
/// The census scratch.
///
/// `first_of[i]` is the least index whose fiber key equals triple `i`'s, and
/// `ordinal_of[i]` is the group that index landed in. Sequential insertion
/// appends a group the first time a key appears, so a group's ordinal **is** the
/// rank of its first appearance in index order — which means computing
/// `first_of` in parallel and assembling in one linear pass returns byte-for-byte
/// what the quadratic scan returned.
struct trace_fiber_workspace final {
  trace_fiber_basis basis{};
  std::uint16_t first_of[trace_fiber_triple_capacity]{};
  std::uint16_t ordinal_of[trace_fiber_triple_capacity]{};
};

} // namespace holonics::organ
