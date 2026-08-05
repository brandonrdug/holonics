#pragma once

#include <cstdint>

#include <holonics/codec/blind_reconstruction_face.hpp>

namespace holonics::codec {

inline constexpr std::size_t hodge_formal_capacity = 32'768;
inline constexpr std::size_t hodge_explanation_capacity = 4'096;
inline constexpr std::size_t hodge_surface_rank = 6;
inline constexpr std::size_t hodge_surface_blowup_rank = 7;
using hodge_formal_face = blind_formal_face<hodge_formal_capacity>;

struct hodge_explanation final {
  exact::word identity{};
  exact::word passage{};
  std::uint16_t byte_count{};
  char bytes[hodge_explanation_capacity]{};
};

struct hodge_realization_surface final {
  std::int64_t discriminant[5]{};
  std::int64_t cup[hodge_surface_rank][hodge_surface_rank]{};
  std::int64_t connection_t[hodge_surface_rank][hodge_surface_rank]{};
  std::int64_t connection_u[hodge_surface_rank][hodge_surface_rank]{};
  std::int64_t graph[hodge_surface_rank]{};
  std::int64_t negation[hodge_surface_rank]{};
  std::int64_t primitive[hodge_surface_rank]{};
  std::int64_t polarization[hodge_surface_rank]{};
  std::int64_t quotient_obstruction[2]{};
  std::int64_t blowup_pairing[hodge_surface_blowup_rank][hodge_surface_blowup_rank]{};
  std::int64_t selected_strict[hodge_surface_blowup_rank]{};
  std::int64_t exceptional[hodge_surface_blowup_rank]{};
  std::int64_t pullback[hodge_surface_blowup_rank][hodge_surface_rank]{};
  std::int64_t pushforward[hodge_surface_rank][hodge_surface_blowup_rank]{};
  exact::word passage{};
  std::int64_t common_denominator{};
  std::int64_t graph_square{};
  std::int64_t mutual_intersection{};
  std::int64_t primitive_square{};
  std::int64_t tangent_obstruction{};
  std::int64_t normal_obstruction{};
  std::int64_t selected_self_intersection{};
  std::uint16_t enumerated{};
  std::uint8_t rational_rank{};
  std::uint8_t f2_rank{};
  std::uint8_t f1_rank{};
  std::uint8_t h20{};
  std::uint8_t h11{};
  std::uint8_t h02{};
  std::uint8_t integral_realizers{};
  std::uint8_t rational_realizers{};
  std::uint8_t effective_graphs{};
  std::uint8_t translation_count{};
  std::uint8_t blowup_rank{};
  std::uint8_t changed_center{};
  std::uint8_t center{};
  std::uint8_t multiplicity{};
  bool factor_exact{};
  bool cup_exact{};
  bool transport_exact{};
  bool locus_exact{};
  bool translations_exact{};
  bool fibers_exact{};
  bool blowup_exact{};
  bool changed_sensitive{};
  bool alternatives_retained{};
  bool rational_integral_separated{};
  bool outside_image{};
};

}  // namespace holonics::codec
