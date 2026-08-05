#pragma once

#include <cstdint>

#include <holonics/organ/rederivation_schema.hpp>

namespace holonics::organ {

enum class rederivation_obstruction : std::uint8_t {
  none,
  card_refused,
  matching_refused,
  geometry_refused,
  potential_refused,
  cover_refused,
  foil_expected_rejection_absent,
  valid_checker_refused,
  render_refused,
  continuation_refused
};

struct injection_receipt final {
  std::uint8_t side{};
  std::uint8_t subset{};
  std::uint8_t forbidden{};
  std::uint8_t image[3]{};
  std::uint8_t size{};
  std::int64_t weight{};
  exact::word lineage{};
};

struct jacobian_receipt final {
  std::uint8_t alpha{};
  std::uint8_t beta{};
  std::uint8_t row{};
  std::uint8_t column{};
  std::uint8_t p_size{};
  std::uint8_t q_size{};
  std::int64_t p_evaluation{};
  std::int64_t q_evaluation{};
  std::int64_t row_factor{};
  std::int64_t value{};
  exact::word lineage{};
};

struct coefficient_factor_receipt final {
  std::uint8_t alpha{};
  std::uint8_t beta{};
  std::uint8_t p_size{};
  std::uint8_t q_size{};
  std::int16_t p_leading{};
  std::int16_t q_leading{};
  std::int64_t row_factor{};
  bool nonzero{};
  exact::word lineage{};
};

struct matching_rederivation_receipt final {
  std::uint16_t injection_count[2]{};
  std::uint16_t coefficient_count{};
  std::uint16_t jacobian_entries{};
  bool kronecker_exact{};
  bool vandermonde_nonzero{};
  bool determinant_factored{};
  bool independence_supported{};
  bool duplicate_q_obstructed{};
  bool changed_independence_undetermined{};
  std::int64_t p_vandermonde{};
  std::int64_t q_vandermonde{};
  std::int64_t duplicate_q_vandermonde{};
  exact::word identity{};
  exact::word lineage{};
};

struct lattice_point_receipt final {
  std::uint8_t polygon{};
  std::uint8_t dilation{};
  std::int16_t x{};
  std::int16_t y{};
  bool in_box{};
  bool included{};
  bool boundary{};
  exact::word lineage{};
};

struct polygon_rederivation_receipt final {
  std::int32_t double_area{};
  std::int32_t boundary{};
  std::int32_t interior{};
  std::int32_t lattice_count[rederivation_dilation_count]{};
  std::int32_t reciprocal_interior[rederivation_dilation_count]{};
  bool simple{};
  bool pick_exact{};
  bool ehrhart_exact{};
  bool reciprocity_exact{};
  exact::word identity{};
  exact::word lineage{};
};

struct potential_rederivation_receipt final {
  std::int32_t matrix[4]{};
  std::int32_t boundary[2]{};
  std::int32_t solution[2]{};
  std::int32_t characteristic[3]{};
  std::int32_t eigenvalues[2]{};
  std::int32_t eigenvectors[4]{};
  std::int32_t energy[3]{};
  bool geometry_return_mounted{};
  bool equations_exact{};
  bool eigen_exact{};
  bool symbolic_minimum{};
  bool disconnected_obstructed{};
  std::int32_t disconnected_determinant{};
  exact::word identity{};
  exact::word lineage{};
};

struct saturation_receipt final {
  std::uint8_t columns[4]{};
  std::uint8_t witness_row{};
  bool saturated{};
  exact::word lineage{};
};

struct cover_pair_receipt final {
  std::uint8_t x{};
  std::uint8_t y{};
  std::uint8_t witness{};
  bool left{};
  bool right{};
  exact::word lineage{};
};

struct cover_rederivation_receipt final {
  std::uint8_t rows[3]{};
  std::uint8_t f[8]{};
  std::uint8_t g[8]{};
  std::uint8_t exceptional[8]{};
  std::uint8_t width{};
  std::uint8_t subset_receipts{};
  std::uint8_t pair_receipts{};
  bool width_one_obstructed{};
  bool width_two_obstructed{};
  bool saturation_exact{};
  bool cover_exact{};
  std::uint8_t width_one_collision[2]{};
  std::uint8_t width_two_collision[2]{};
  exact::word identity{};
  exact::word lineage{};
};

struct rederivation_theory final {
  exact::word identity{};
  exact::word passage{};
  exact::word lineage{};
  std::uint32_t atlas_entries{};
  std::uint8_t theorem_families{};
  std::uint8_t dependency_edges{};
  bool complete{};
};

struct rederivation_receipt final {
  matching_problem_card matching_card{};
  lattice_problem_card lattice_card{};
  cover_problem_card cover_card{};
  rederivation_question question{};
  matching_rederivation_receipt matching{};
  polygon_rederivation_receipt polygons[rederivation_polygon_count]{};
  potential_rederivation_receipt potential{};
  cover_rederivation_receipt cover{};
  rederivation_theory theory{};
  rederivation_obstruction obstruction{rederivation_obstruction::none};
  bool source_separated{};
  bool comparison_withheld{};
  bool alternatives_retained{};
  bool dependency_exact{};
  bool self_crossing_obstructed{};
  bool all_exact{};
  bool theory_formed{};
};

struct rederivation_workspace final {
  injection_receipt injections[2][rederivation_injection_capacity]{};
  jacobian_receipt jacobian[rederivation_jacobian_count]{};
  coefficient_factor_receipt factors[rederivation_coefficient_count]{};
  lattice_point_receipt lattice[rederivation_polygon_count]
                               [rederivation_dilation_count]
                               [rederivation_lattice_x_capacity]
                               [rederivation_lattice_y_capacity]{};
  saturation_receipt subsets[rederivation_subset_count]{};
  cover_pair_receipt pairs[rederivation_pair_count]{};
};

struct acquired_rederivation_fiber final {
  exact::word identity{};
  exact::word passage{};
  exact::word returned_event{};
  exact::word lineage{};
  exact::word morphology_delta{};
  bool accepted{};
};

namespace rederivation_detail {
[[nodiscard]] HOLONICS_CALLABLE inline bool
valid(const rederivation_foundation &value) noexcept {
  return value.matching.metadata.parsed && value.lattice.metadata.parsed &&
         value.cover.metadata.parsed && value.matching.matrix_size == 13 &&
         value.matching.marked_count == 6 && value.matching.side_count == 3 &&
         value.matching.external_count == 7 &&
         value.lattice.dilation_max == 4 && value.cover.alphabet == 2 &&
         value.lattice.potential_polygon < rederivation_polygon_count &&
         value.cover.words == 8 && value.cover.maximum_width == 3 &&
         value.cover.subset_size == 4 && value.event.value() != 0 &&
         value.incoming_port.value() != 0 && value.return_port.value() != 0 &&
         value.lineage.value() != 0;
}
} // namespace rederivation_detail

} // namespace holonics::organ
