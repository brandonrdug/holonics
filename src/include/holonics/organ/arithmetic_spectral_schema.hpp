#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/config.hpp>
#include <holonics/exact/word.hpp>

namespace holonics::organ {

inline constexpr std::size_t arithmetic_base_count = 2;
inline constexpr std::size_t arithmetic_degree_count = 4;
inline constexpr std::size_t arithmetic_baseline_count = 6;
inline constexpr std::size_t arithmetic_curve_count = 7;
inline constexpr std::size_t arithmetic_candidate_side = 9;
inline constexpr std::size_t arithmetic_candidate_count = 81;
inline constexpr std::size_t arithmetic_field_candidate_capacity = 32;
inline constexpr std::size_t arithmetic_fixed_capacity = 156'260;
inline constexpr std::size_t arithmetic_point_pair_capacity = 144'062;
inline constexpr std::size_t arithmetic_trace_current_count = 81;
inline constexpr std::size_t arithmetic_norm_current_count = 243;

struct arithmetic_curve_source final {
  std::uint16_t prime{};
  std::uint16_t coefficient{};
  exact::word identity{};
  exact::word lineage{};
};

struct arithmetic_spectral_card final {
  exact::word schema{};
  exact::word occurrence{};
  arithmetic_curve_source baseline[arithmetic_baseline_count]{};
  std::uint16_t changed_prime{};
  std::uint16_t changed_from{};
  std::uint16_t changed_to{};
  std::uint8_t degree_min{};
  std::uint8_t degree_max{};
  std::int8_t candidate_min{};
  std::int8_t candidate_max{};
  std::uint8_t test_degree{};
  std::int8_t test_min{};
  std::int8_t test_max{};
  std::uint8_t rechart_left{};
  std::uint8_t rechart_right{};
  std::uint32_t byte_count{};
  std::uint64_t byte_fold{};
  std::uint64_t path_fold{};
  exact::word lineage{};
  bool parsed{};
};

struct extension_field_element final {
  std::uint16_t coefficient[arithmetic_degree_count]{};
};

struct extension_field_spec final {
  std::uint16_t prime{};
  std::uint8_t degree{};
  std::uint32_t order{};
  std::uint16_t modulus[arithmetic_degree_count + 1]{};
  exact::word lineage{};
  bool irreducible{};
};

struct elliptic_point final {
  extension_field_element x{};
  extension_field_element y{};
  bool infinite{};
};

struct gaussian_integer final {
  std::int64_t real{};
  std::int64_t imaginary{};
};

struct arithmetic_spectral_question final {
  exact::word identity{};
  exact::word receiver{};
  exact::word material{};
};

struct arithmetic_spectral_foundation final {
  arithmetic_spectral_card card{};
  exact::word event{};
  exact::word incoming_port{};
  exact::word return_port{};
  exact::word lineage{};
};

}  // namespace holonics::organ
