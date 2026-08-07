#pragma once

#include <holonics/organ/cultivated_organ_schema.hpp>

namespace holonics::organ {
enum class cultivation_obstruction : std::uint8_t {
  none,
  insufficient_rows,
  full_rank,
  nonunique_kernel,
  zero_forward_face,
  nonzero_residual,
  candidate_absent,
  checker_refused,
  heldout_residual,
  insufficient_prefix,
  organ_absent
};

struct feature_geometry_receipt final {
  std::int64_t coefficients[cultivation_feature_capacity]{};
  exact::small_rational residual{};
  std::uint8_t pivot_columns[cultivation_feature_capacity]{};
  std::uint8_t order{};
  std::uint8_t degree{};
  std::uint8_t features{};
  std::uint8_t rows{};
  std::uint8_t rank{};
  std::uint8_t nullity{};
  cultivation_obstruction obstruction{cultivation_obstruction::candidate_absent};
  bool primitive{};
  bool selected{};
};

struct cultivated_shift_organ final {
  exact::word identity{};
  exact::word passage{};
  exact::word returned_event{};
  exact::word lineage{};
  std::int64_t coefficients[cultivation_feature_capacity]{};
  std::uint8_t order{};
  std::uint8_t degree{};
  std::uint8_t features{};
  std::uint8_t minimum_prefix{};
  cultivation_family family{};
  bool primitive{};
  bool checker_founded{};
};

struct cultivation_family_receipt final {
  feature_geometry_receipt candidates[cultivation_candidate_count]{};
  cultivated_shift_organ candidate{};
  std::uint8_t candidate_count{};
  bool source_current_independent{};
  bool selected_exact{};
};

struct cultivation_control_receipt final {
  cultivation_obstruction constant_stream{};
  cultivation_obstruction short_stream{};
};

struct cultivation_receipt final {
  cultivation_family_receipt families[cultivation_family_count]{};
  cultivation_control_receipt controls{};
  exact::word passage{};
  exact::word lineage{};
  std::uint16_t atlas_rows{};
  bool development_ports_distinct{};
  bool all_candidates_exact{};
  bool theory_formed{};
};

struct tail_receipt final {
  exact::small_rational source[cultivation_sample_capacity]{};
  exact::small_rational predicted[cultivation_sample_capacity]{};
  std::uint8_t sample_count{};
  std::uint8_t prefix_count{};
  std::uint8_t prediction_count{};
  cultivation_obstruction changed_source{cultivation_obstruction::none};
  cultivation_obstruction short_prefix{cultivation_obstruction::none};
  cultivation_obstruction exclusion{cultivation_obstruction::none};
  bool prediction_before_comparison{};
  bool exact{};
};

struct heldout_application_receipt final {
  tail_receipt tails[cultivation_family_count]{};
  exact::word passage{};
  exact::word lineage{};
  bool structure_ports_distinct{};
  bool development_sources_absent{};
  bool identity_ablation_exact{};
  bool all_exact{};
  bool theory_formed{};
};

struct acquired_organ_application final {
  exact::word identity{};
  exact::word passage{};
  exact::word returned_event{};
  exact::word lineage{};
  bool accepted{};
};

struct cultivation_workspace final {
  exact::small_rational matrices[cultivation_family_count]
                                 [cultivation_row_capacity]
                                 [cultivation_feature_capacity]{};
};

}  // namespace holonics::organ
