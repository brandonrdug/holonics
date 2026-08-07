#pragma once

#include <holonics/codec/blind_reconstruction_face.hpp>
#include <holonics/exact/small_rational.hpp>

namespace holonics::codec {

inline constexpr std::size_t elementary_formal_capacity = 65'536;
inline constexpr std::size_t elementary_dossier_capacity = 24'576;
using elementary_formal_face = blind_formal_face<elementary_formal_capacity>;

struct elementary_dossier_face final {
  exact::word identity{};
  exact::word passage{};
  std::uint16_t byte_count{};
  char bytes[elementary_dossier_capacity]{};
};

struct elementary_matrix2_surface final { std::int64_t value[4]{}; };

struct elementary_occurrence_surface final {
  std::uint64_t coordinates[6][5]{};
  std::int64_t payload[6]{};
  std::int8_t boundary_one[4][5]{};
  std::int8_t boundary_two[5][2]{};
  std::uint8_t selected_mask{};
  std::int64_t unsigned_residual[4][2]{};
  std::int64_t incoherent_residual[4][2]{};
};

struct elementary_composition_surface final {
  std::int64_t forward[5][4]{};
  std::int64_t reverse[5][4]{};
  std::uint8_t codes[5]{};
  std::uint8_t visible[5]{};
  bool contact[5]{};
  bool predecessor_link[5]{};
  bool forward_available[5]{};
  bool reverse_available[5]{};
};

struct elementary_receiver_surface final {
  std::int64_t coarse[6]{};
  std::int64_t fine[6]{};
  std::int64_t first[6]{};
  std::int64_t strict[6]{};
  std::uint8_t coarse_fibers{};
  std::uint8_t fine_fibers{};
  std::uint8_t strict_witnesses{};
};

struct elementary_chart_surface final {
  elementary_matrix2_surface first{};
  elementary_matrix2_surface second{};
  elementary_matrix2_surface first_path{};
  elementary_matrix2_surface second_path{};
  elementary_matrix2_surface residual{};
  elementary_matrix2_surface closed{};
  std::int64_t determinant{};
  std::int64_t trace{};
};

struct elementary_conduct_surface final {
  std::uint8_t cases[8][8]{};
  std::uint8_t conditions[7]{};
  std::uint16_t selected_code{};
};

struct elementary_organ_surface final {
  std::int64_t coefficients[3]{};
  exact::small_rational trace[9]{};
  std::uint8_t trace_count{};
};

struct elementary_calculus_surface final {
  elementary_occurrence_surface occurrence{};
  elementary_composition_surface composition{};
  elementary_receiver_surface receiver{};
  elementary_chart_surface chart{};
  elementary_conduct_surface conduct{};
  elementary_organ_surface organ{};
  exact::word passage{};
  bool exact{};
};

struct heldout_holonomy_surface final {
  elementary_matrix2_surface product{};
  elementary_organ_surface organ{};
  exact::small_rational source[9]{};
  exact::small_rational predicted[9]{};
  std::uint8_t sample_count{};
  std::uint8_t prefix_count{};
  std::uint8_t changed{};
  std::uint8_t exclusion{};
  exact::word passage{};
  bool prediction_before_comparison{};
  bool source_detached{};
  bool exact{};
};

}  // namespace holonics::codec
