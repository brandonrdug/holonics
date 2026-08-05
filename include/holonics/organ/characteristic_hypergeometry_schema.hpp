#pragma once

#include <cstdint>

#include <holonics/organ/elementary_calculus_schema.hpp>

namespace holonics::organ {

inline constexpr std::uint8_t characteristic_source_count = 3;
inline constexpr std::uint8_t characteristic_generator_capacity = 4;
inline constexpr std::uint8_t characteristic_word_length = 4;
inline constexpr std::uint8_t characteristic_word_capacity = 64;
inline constexpr std::uint16_t characteristic_pair_stride = 4096;
inline constexpr std::uint16_t characteristic_pair_capacity = 12'288;
inline constexpr std::uint16_t characteristic_group_capacity = 512;
inline constexpr std::uint8_t characteristic_feature_count = 21;
inline constexpr std::uint8_t characteristic_candidate_count = 7;
inline constexpr std::uint8_t characteristic_witness_count = 5;

struct transition_source_card final {
  cultivation_card_metadata metadata{};
  exact_matrix2 rechart{};
  exact_matrix2 generators[characteristic_generator_capacity]{};
  std::uint8_t inverse_letter[characteristic_generator_capacity]{};
  std::uint8_t alphabet_size{};
  std::uint8_t maximum_length{};
  bool recharted{};
};

struct characteristic_development_bundle final {
  transition_source_card sources[characteristic_source_count]{};
};

struct heldout_local_system_card final {
  cultivation_card_metadata metadata{};
  exact_matrix2 edges[5]{};
  std::uint8_t edge_count{};
  std::uint8_t split{};
  std::uint8_t changed_slot{};
  std::int64_t changed_value{};
};

struct reduced_transition_word final {
  exact_matrix2 matrix{};
  std::uint8_t letters[characteristic_word_length]{};
  std::uint8_t length{};
  std::uint16_t ordinal{};
  exact::word lineage{};
  bool valid{};
};

struct transition_word_population final {
  reduced_transition_word words[characteristic_word_capacity]{};
  std::uint8_t count{};
  exact::word lineage{};
  bool complete{};
};

} // namespace holonics::organ
