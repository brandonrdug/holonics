#pragma once

#include <cstdint>

#include <holonics/organ/characteristic_hypergeometry_schema.hpp>

namespace holonics::organ {

inline constexpr std::uint8_t trace_fiber_source_count = 3;
inline constexpr std::uint8_t trace_fiber_word_count = 12;
inline constexpr std::uint16_t trace_fiber_triple_stride = 1'728;
inline constexpr std::uint16_t trace_fiber_triple_capacity = 5'184;
inline constexpr std::uint16_t trace_fiber_group_capacity = 2'304;
inline constexpr std::uint8_t trace_fiber_lower_count = 6;
inline constexpr std::uint8_t trace_fiber_monomial_count = 84;
inline constexpr std::uint8_t trace_fiber_feature_count = 85;
inline constexpr std::uint8_t trace_fiber_candidate_count = 14;
inline constexpr std::uint8_t trace_fiber_witness_count = 5;

struct three_face_source_card final {
  transition_source_card transitions{};
  std::uint8_t admitted_words{};
};
struct three_face_development_bundle final {
  three_face_source_card sources[trace_fiber_source_count]{};
};
struct heldout_oriented_system_card final {
  cultivation_card_metadata metadata{};
  exact_matrix2 edges[6]{};
  std::uint8_t changed_matrix{};
  std::uint8_t changed_slot{};
  std::int64_t changed_value{};
};

enum class trace_fiber_target : std::uint8_t { sum, product };
enum class trace_fiber_feature_mode : std::uint8_t {
  complete,
  degree_two,
  sixth_coordinate_deleted,
  target_deleted
};

} // namespace holonics::organ
