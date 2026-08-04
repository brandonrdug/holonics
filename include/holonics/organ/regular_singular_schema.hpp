#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>
#include <holonics/organ/characteristic_schema.hpp>

namespace holonics::organ {

inline constexpr std::size_t regular_singular_chart_capacity = 3;
inline constexpr std::size_t regular_singular_term_capacity = 12;

enum class regular_singular_obstruction : std::uint8_t {
  none,
  invalid_foundation,
  system_derivation_refused,
  chart_refused,
  recurrence_refused,
  connection_refused,
  continuation_refused,
  render_refused,
  checker_rejected,
  rest_refused
};

struct gauss_operator final {
  std::int64_t second[3]{};
  std::int64_t first[2]{};
  std::int64_t zeroth{};
};

struct fuchsian_system final {
  matrix_two zero{};
  matrix_two one{};
  matrix_two infinity{};
  bool derived{};
};

struct period_entry final {
  std::int64_t constant{};
  std::int64_t omega{};
};

struct period_matrix_two final {
  period_entry a{};
  period_entry b{};
  period_entry c{};
  period_entry d{};
};

struct regular_singular_foundation final {
  exact::word ecology{};
  exact::word differential_transport{};
  exact::word frobenius_transport{};
  exact::word resonance_transport{};
  exact::word chamber_transport{};
  exact::word monodromy_transport{};
  exact::word provenance{};
  exact::word term_seed{};
  gauss_operator mounted_operator{};
  std::uint16_t term_count{};
};

struct regular_singular_question final {
  exact::word identity{};
  exact::word receiver{};
  exact::word material{};
};

struct regular_singular_theory_plan final {
  exact::word passage{};
  exact::word residue_statement{};
  exact::word frobenius_statement{};
  exact::word resonance_statement{};
  exact::word connection_statement{};
  exact::word lineage{};
  bool residue_algebra{};
  bool frobenius_steps{};
  bool resonance_obstruction{};
  bool chamber_connection{};
  bool loop_product{};
  bool lineage_retained{};
};

struct acquired_regular_singular final {
  exact::word identity{};
  exact::word passage{};
  exact::word kernel_return{};
  exact::word lineage{};
  exact::word morphology_delta{};
  bool accepted{};
};

}  // namespace holonics::organ
