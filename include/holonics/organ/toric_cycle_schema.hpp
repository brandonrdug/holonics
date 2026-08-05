#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/small_rational.hpp>
#include <holonics/exact/word.hpp>

namespace holonics::organ {

inline constexpr std::size_t toric_fan_capacity = 2;
inline constexpr std::size_t toric_ray_capacity = 5;
inline constexpr std::size_t toric_rank_capacity = 3;
inline constexpr std::size_t toric_target_capacity = 3;
inline constexpr std::size_t toric_representative_capacity = 192;

struct toric_integer_pair final { std::int64_t x{}; std::int64_t y{}; };

struct toric_target final {
  exact::small_rational response[toric_ray_capacity]{};
};

struct toric_fan_card final {
  toric_integer_pair rays[toric_ray_capacity]{};
  std::uint8_t ray_count{};
};

struct toric_cycle_card final {
  exact::word schema{};
  exact::word occurrence{};
  exact::word lineage{};
  std::uint64_t byte_fold{};
  std::uint64_t path_fold{};
  std::uint32_t byte_count{};
  toric_fan_card fans[toric_fan_capacity]{};
  toric_target targets[toric_target_capacity]{};
  std::int16_t representative_min{};
  std::int16_t representative_max{};
  std::uint8_t fan_count{};
  std::uint8_t selected_fan{};
  std::uint8_t selected_cone{};
  std::uint8_t target_count{};
  bool parsed{};
};

struct toric_cycle_foundation final {
  exact::word ecology{};
  exact::word fan{};
  exact::word character{};
  exact::word quotient{};
  exact::word intersection{};
  exact::word realization{};
  exact::word transport{};
  exact::word provenance{};
  toric_cycle_card card{};
};

struct toric_cycle_question final {
  exact::word identity{};
  exact::word receiver{};
  exact::word material{};
};

enum class toric_obstruction : std::uint8_t {
  none,
  invalid_foundation,
  fan_refused,
  quotient_refused,
  intersection_refused,
  realization_refused,
  subdivision_refused,
  continuation_refused,
  render_refused,
  checker_rejected,
  rest_refused
};

struct toric_cycle_plan final {
  exact::word passage{};
  exact::word statement{};
  exact::word lineage{};
  bool fan_exact{};
  bool quotient_exact{};
  bool intersection_exact{};
  bool realization_exact{};
  bool subdivision_exact{};
  bool alternatives_retained{};
};

struct acquired_toric_cycle final {
  exact::word identity{};
  exact::word passage{};
  exact::word kernel_return{};
  exact::word lineage{};
  exact::word morphology_delta{};
  bool accepted{};
};

}  // namespace holonics::organ
