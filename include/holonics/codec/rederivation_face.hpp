#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/codec/blind_reconstruction_face.hpp>

namespace holonics::codec {

inline constexpr std::size_t rederivation_formal_capacity = 262'144;
inline constexpr std::size_t rederivation_foil_capacity = 1'024;
inline constexpr std::size_t rederivation_dossier_capacity = 16'384;
inline constexpr std::size_t rederivation_surface_jacobians = 2'401;
inline constexpr std::size_t rederivation_surface_factors = 49;
inline constexpr std::size_t rederivation_surface_polygons = 4;
inline constexpr std::size_t rederivation_surface_pairs = 64;
using rederivation_formal_face =
    blind_formal_face<rederivation_formal_capacity>;
using rederivation_foil_face = blind_formal_face<rederivation_foil_capacity>;

struct rederivation_dossier_face final {
  exact::word identity{};
  exact::word passage{};
  std::uint32_t byte_count{};
  char bytes[rederivation_dossier_capacity]{};
};

struct rederivation_jacobian_surface final {
  std::int64_t value{};
  std::int64_t row_factor{};
  std::int64_t p_evaluation{};
  std::int64_t q_evaluation{};
};
struct rederivation_factor_surface final {
  std::int16_t p_leading{};
  std::int16_t q_leading{};
  std::int64_t row_factor{};
};
struct rederivation_polygon_surface final {
  std::int32_t area_twice{};
  std::int32_t boundary{};
  std::int32_t interior{};
  std::int32_t lattice_count[5]{};
  std::int32_t reciprocal_interior[5]{};
};
struct rederivation_pair_surface final {
  std::uint8_t x{};
  std::uint8_t y{};
  std::uint8_t witness{};
  bool left{};
  bool right{};
};
struct rederivation_surface final {
  exact::word passage{};
  rederivation_jacobian_surface jacobian[rederivation_surface_jacobians]{};
  rederivation_factor_surface factors[rederivation_surface_factors]{};
  rederivation_polygon_surface polygons[rederivation_surface_polygons]{};
  rederivation_pair_surface pairs[rederivation_surface_pairs]{};
  std::int64_t p_vandermonde{};
  std::int64_t q_vandermonde{};
  std::int64_t duplicate_q_vandermonde{};
  std::int32_t potential_matrix[4]{};
  std::int32_t potential_boundary[2]{};
  std::int32_t potential_solution[2]{};
  std::int32_t potential_characteristic[3]{};
  std::int32_t potential_eigenvalues[2]{};
  std::int32_t potential_eigenvectors[4]{};
  std::int32_t potential_energy[3]{};
  std::int32_t disconnected_determinant{};
  std::uint16_t coefficient_count{};
  std::uint16_t jacobian_count{};
  std::uint16_t injection_count{};
  std::uint8_t cover_words{};
  std::uint8_t cover_width{};
  std::uint8_t cover_f[8]{};
  std::uint8_t cover_g[8]{};
  std::uint8_t cover_exceptional[8]{};
  std::uint8_t subset_count{};
  std::uint8_t pair_count{};
  std::uint8_t width_one_collision[2]{};
  std::uint8_t width_two_collision[2]{};
  bool self_crossing_obstructed{};
  bool all_exact{};
};

} // namespace holonics::codec
