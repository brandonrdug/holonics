#pragma once

#include <holonics/codec/blind_reconstruction_face.hpp>

namespace holonics::codec {

inline constexpr std::size_t causal_linear_formal_capacity = 24'576;
inline constexpr std::size_t causal_linear_explanation_capacity = 4'096;

using causal_linear_formal_face = blind_formal_face<causal_linear_formal_capacity>;

struct causal_linear_explanation final {
  exact::word identity{};
  exact::word passage{};
  std::uint16_t byte_count{};
  char bytes[causal_linear_explanation_capacity]{};
};

struct causal_linear_surface final {
  exact::word passage{};
  std::int64_t cm_characteristic[17]{};
  std::int64_t cm_factor_roots[6]{};
  std::uint8_t cm_factor_multiplicities[6]{};
  std::int64_t toric_smith[3][2]{};
  std::int64_t pencil[2][2][2]{};
  std::int64_t determinant[3]{};
  std::int64_t form[2][2]{};
  std::int64_t loops[3][2][2]{};
  std::int64_t identity_characteristic[3]{};
  std::int64_t jordan_characteristic[3]{};
  std::uint8_t phase_counts[3]{};
  std::uint8_t phase_ranks[2]{};
  std::uint8_t phase_betti[3]{};
  std::uint8_t phase_tours{};
  std::uint8_t phase_tour_length{};
  std::uint8_t cm_rank{};
  std::uint8_t cm_homology[2]{};
  std::uint8_t toric_cokernel[3]{};
  std::uint8_t factor_count{};
  std::uint8_t identity_fixed{};
  std::uint8_t jordan_fixed{};
  bool chain_exact{};
  bool characteristics_exact{};
  bool multilinear_exact{};
  bool controls_exact{};
  bool alternatives_retained{};
};

}  // namespace holonics::codec
