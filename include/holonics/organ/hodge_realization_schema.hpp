#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::organ {
inline constexpr std::size_t hodge_factor_capacity = 2;
inline constexpr std::size_t hodge_term_capacity = 6;
inline constexpr std::size_t hodge_rank = 6;
inline constexpr std::size_t hodge_blowup_rank = 7;
inline constexpr std::size_t hodge_translation_capacity = 4;
inline constexpr std::size_t hodge_cycle_generator_capacity = 7;
inline constexpr std::size_t hodge_target_capacity = 3;
inline constexpr std::size_t hodge_realizer_capacity = 16;

struct hodge_family_term final {
  std::int64_t coefficient{};
  std::uint8_t parameter_power{};
  std::uint8_t x_power{};
  std::uint8_t y_power{};
};

struct hodge_family_source final {
  exact::word identity{};
  exact::word lineage{};
  hodge_family_term terms[hodge_term_capacity]{};
  std::uint8_t term_count{};
  bool exact{};
};

struct hodge_class_question final {
  std::int64_t numerator[hodge_rank]{};
  std::uint8_t denominator{};
};

struct hodge_realization_card final {
  exact::word schema{};
  exact::word occurrence{};
  exact::word lineage{};
  std::uint64_t byte_fold{};
  std::uint64_t path_fold{};
  std::uint32_t byte_count{};
  hodge_family_source factors[hodge_factor_capacity]{};
  hodge_class_question questions[hodge_target_capacity]{};
  std::int8_t coefficient_min{};
  std::int8_t coefficient_max{};
  std::int8_t base_t{};
  std::int8_t base_u{};
  std::int8_t off_diagonal_u{};
  std::uint8_t denominator_aperture{};
  std::uint8_t center_selector{};
  std::uint8_t changed_center_selector{};
  std::uint8_t factor_count{};
  std::uint8_t rank{};
  std::uint8_t question_count{};
  bool parsed{};
};

struct hodge_realization_foundation final {
  exact::word ecology{};
  exact::word family{};
  exact::word cohomology{};
  exact::word filtration{};
  exact::word transport{};
  exact::word cycle{};
  exact::word blowup{};
  exact::word theorem{};
  exact::word provenance{};
  hodge_realization_card card{};
};

struct hodge_realization_question final {
  exact::word identity{};
  exact::word receiver{};
  exact::word material{};
};

enum class hodge_realization_obstruction : std::uint8_t {
  none,
  invalid_foundation,
  family_refused,
  cohomology_refused,
  filtration_refused,
  correspondence_refused,
  realization_refused,
  blowup_refused,
  continuation_refused,
  render_refused,
  checker_rejected,
  rest_refused
};

struct hodge_realization_plan final {
  exact::word passage{};
  exact::word statement{};
  exact::word lineage{};
  bool families_exact{};
  bool cohomology_exact{};
  bool filtration_exact{};
  bool cycles_exact{};
  bool blowup_exact{};
};

struct acquired_hodge_realization final {
  exact::word identity{};
  exact::word passage{};
  exact::word kernel_return{};
  exact::word lineage{};
  bool accepted{};
};

}  // namespace holonics::organ
