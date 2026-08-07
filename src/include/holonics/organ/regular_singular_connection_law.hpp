#pragma once

#include <holonics/organ/regular_singular_exact.hpp>

namespace holonics::organ::regular_singular_detail {

HOLONICS_CALLABLE constexpr void form_connection(
    const regular_singular_foundation& foundation,
    chamber_connection_receipt& result) noexcept {
  result.zero_to_one = {0, 1, 1, 0};
  result.one_to_zero = result.zero_to_one;
  result.monodromy_zero = period_matrix_two{{1, 0}, {0, 0}, {0, 0}, {1, 0}};
  result.monodromy_one = period_matrix_two{{1, 0}, {0, -1}, {0, 0}, {1, 0}};
  result.monodromy_infinity = period_matrix_two{{1, 0}, {0, 1}, {0, 0}, {1, 0}};
  result.zero_basis = exact::word{158'400};
  result.one_basis = exact::word{158'401};
  result.overlap_path = exact::word{158'402};
  result.zero_loop = exact::word{158'403};
  result.one_loop = exact::word{158'404};
  result.infinity_loop = exact::word{158'405};
  result.connection_determinant = -1;
  result.zero_fixed_dimension = 2;
  result.one_fixed_dimension = 1;
  result.infinity_fixed_dimension = 1;
  result.one_nilpotent_rank = 1;
  result.infinity_nilpotent_rank = 1;
  period_matrix_two intermediate{};
  period_matrix_two connection_left{};
  period_matrix_two connection_result{};
  result.punctured_sphere_product_exact =
      multiply(result.monodromy_zero, result.monodromy_one, intermediate) &&
      multiply(intermediate, result.monodromy_infinity, result.loop_product) &&
      same(result.loop_product, lift({1, 0, 0, 1}));
  result.conjugacy_exact = multiply(lift(result.one_to_zero), result.monodromy_one,
      connection_left) && multiply(connection_left, lift(result.zero_to_one),
      connection_result);
  result.one_loop_in_zero_basis = connection_result;
  const period_matrix_two expected_zero_basis{{1, 0}, {0, 0}, {0, -1}, {1, 0}};
  result.conjugacy_exact = result.conjugacy_exact &&
      same(result.one_loop_in_zero_basis, expected_zero_basis);
  matrix_two inverse_check{};
  result.inverse_exact = characteristic_detail::multiply(result.zero_to_one,
      result.one_to_zero, inverse_check) &&
      characteristic_detail::same_matrix(inverse_check, {1, 0, 0, 1});
  const std::int64_t connection_values[11]{
      static_cast<std::int64_t>(foundation.chamber_transport.value()),
      static_cast<std::int64_t>(result.zero_basis.value()),
      static_cast<std::int64_t>(result.one_basis.value()),
      static_cast<std::int64_t>(result.overlap_path.value()),
      result.zero_to_one.a, result.zero_to_one.b, result.zero_to_one.c,
      result.zero_to_one.d, result.one_to_zero.b, result.one_to_zero.c,
      result.connection_determinant};
  result.connection_lineage = fold_values(connection_values, 11);
  const std::int64_t zero_loop_values[4]{
      static_cast<std::int64_t>(foundation.monodromy_transport.value()),
      static_cast<std::int64_t>(result.zero_loop.value()), 0, 0};
  const std::int64_t one_loop_values[4]{
      static_cast<std::int64_t>(foundation.monodromy_transport.value()),
      static_cast<std::int64_t>(result.one_loop.value()), -1, 1};
  const std::int64_t infinity_loop_values[4]{
      static_cast<std::int64_t>(foundation.monodromy_transport.value()),
      static_cast<std::int64_t>(result.infinity_loop.value()), 1, 1};
  result.loop_lineages[0] = fold_values(zero_loop_values, 4);
  result.loop_lineages[1] = fold_values(one_loop_values, 4);
  result.loop_lineages[2] = fold_values(infinity_loop_values, 4);
  const std::int64_t loop_values[7]{
      static_cast<std::int64_t>(foundation.monodromy_transport.value()),
      static_cast<std::int64_t>(result.loop_lineages[0]),
      static_cast<std::int64_t>(result.loop_lineages[1]),
      static_cast<std::int64_t>(result.loop_lineages[2]), 0, -1, 1};
  result.loop_lineage = fold_values(loop_values, 7);
  result.period_symbolic = true;
  result.exact = result.inverse_exact && result.conjugacy_exact &&
      result.punctured_sphere_product_exact && result.period_symbolic;
}

}  // namespace holonics::organ::regular_singular_detail
