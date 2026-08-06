#pragma once

#include <cstdint>

#include <holonics/organ/arithmetic_curve_receipt.hpp>
#include <holonics/organ/arithmetic_field_receipt.hpp>

namespace holonics::organ {

enum class arithmetic_spectral_obstruction : std::uint8_t {
  none,
  card_refused,
  field_refused,
  curve_refused,
  correspondence_refused,
  trace_refused,
  render_refused,
  continuation_refused
};

struct trace_current_receipt final {
  std::uint8_t curve{};
  std::int8_t coefficient[arithmetic_degree_count]{};
  std::int64_t place_side{};
  std::int64_t normalization_side{};
  std::int64_t spectral_side{};
  std::int64_t residual{};
  exact::word lineage{};
};

struct norm_current_receipt final {
  std::uint8_t curve{};
  std::int8_t coefficient[arithmetic_degree_count + 1]{};
  gaussian_integer value{};
  std::int64_t norm{};
  bool nonnegative{};
  exact::word lineage{};
};

struct arithmetic_control_receipt final {
  bool twist_5_exact{};
  bool twist_13_exact{};
  bool changed_twist_exact{};
  bool even_counts_preserved{};
  bool odd_counts_reversed{};
  bool equal_factor_rechart{};
  std::uint16_t rechart_scale{};
  bool gaussian_phase_separated{};
  bool source_lineage_retained{};
  bool archimedean_inapplicable{};
  exact::word lineage{};
};

struct arithmetic_spectral_theory final {
  exact::word identity{};
  exact::word passage{};
  exact::word lineage{};
  std::uint32_t fixed_contributions{};
  std::uint32_t correspondence_candidates{};
  std::uint32_t correspondence_points{};
  std::uint32_t trace_currents{};
  std::uint32_t norm_currents{};
  bool complete{};
};

struct arithmetic_spectral_receipt final {
  arithmetic_spectral_card mounted{};
  arithmetic_spectral_question question{};
  field_tower_receipt towers[arithmetic_base_count]{};
  arithmetic_curve_receipt curves[arithmetic_curve_count]{};
  arithmetic_control_receipt controls{};
  arithmetic_spectral_theory theory{};
  arithmetic_spectral_obstruction obstruction{arithmetic_spectral_obstruction::none};
  bool no_expected_invariants{};
  bool alternatives_retained{};
  bool all_exact{};
  bool theory_formed{};
};

struct arithmetic_spectral_workspace final {
  fixed_locus_contribution fixed[arithmetic_fixed_capacity]{};
  correspondence_candidate_receipt candidates[arithmetic_curve_count][arithmetic_candidate_count]{};
  correspondence_point_receipt points[arithmetic_point_pair_capacity]{};
  trace_current_receipt trace_currents[arithmetic_curve_count][arithmetic_trace_current_count]{};
  norm_current_receipt norm_currents[arithmetic_curve_count][arithmetic_norm_current_count]{};
};

struct acquired_arithmetic_spectral final {
  exact::word identity{};
  exact::word passage{};
  exact::word returned_event{};
  exact::word lineage{};
  exact::word admitted_tally_delta{};
  bool accepted{};
};

}  // namespace holonics::organ
