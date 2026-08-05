#pragma once

#include <cstdint>

#include <holonics/organ/arithmetic_spectral_schema.hpp>

namespace holonics::organ {

struct correspondence_candidate_receipt final {
  std::uint8_t curve{};
  std::int8_t real{};
  std::int8_t imaginary{};
  std::uint32_t norm{};
  std::uint32_t points_tested{};
  std::uint32_t mismatches{};
  bool norm_matches{};
  bool selected{};
  exact::word lineage{};
};

struct correspondence_point_receipt final {
  std::uint8_t curve{};
  std::uint32_t pair_encoding{};
  elliptic_point source{};
  elliptic_point frobenius{};
  elliptic_point gaussian{};
  bool on_curve{};
  bool equal{};
  exact::word lineage{};
};

struct arithmetic_curve_receipt final {
  arithmetic_curve_source source{};
  std::int64_t discriminant{};
  std::uint16_t imaginary_unit{};
  std::uint32_t fixed_counts[arithmetic_degree_count]{};
  std::int64_t power_traces[arithmetic_degree_count + 1]{};
  std::uint32_t closed_places[arithmetic_degree_count]{};
  gaussian_integer frobenius{};
  std::int64_t matrix[2][2]{};
  std::int64_t characteristic[3]{};
  std::int64_t discriminant_characteristic{};
  std::int64_t alternating_pullback[2][2]{};
  std::int64_t positive_pullback[2][2]{};
  std::int64_t primary_eigenvectors[2][2][2]{};
  gaussian_integer primary_eigenvalues[2]{};
  gaussian_integer primary_gluing{};
  std::uint32_t pointwise_points{};
  std::uint32_t correspondence_bound{};
  bool smooth{};
  bool correspondence_exact{};
  bool correspondence_precedes_matrix{};
  bool degree_bound_closes{};
  bool fixed_trace_agrees{};
  bool forms_exact{};
  bool weight_exact{};
  bool functional_relation{};
  bool primary_exact{};
  bool euler_prefix_exact{};
  bool exact{};
  exact::word lineage{};
};

}  // namespace holonics::organ
