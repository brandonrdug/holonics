#pragma once

#include <holonics/organ/characteristic_exact.hpp>

namespace holonics::organ::characteristic_detail {

HOLONICS_CALLABLE constexpr void form_scalar_control(scalar_cycle_control& receipt) noexcept {
  constexpr std::uint16_t first[3]{2, 3, 5};
  constexpr std::uint16_t second[3]{2, 5, 3};
  receipt.length = 3;
  receipt.first_product = 1;
  receipt.second_product = 1;
  for (std::size_t slot = 0; slot < 3; ++slot) {
    receipt.first_product *= first[slot];
    receipt.second_product *= second[slot];
  }
  receipt.first_lineage = fold_word(first, 3);
  receipt.second_lineage = fold_word(second, 3);
  receipt.characteristic_equal = receipt.first_product == receipt.second_product;
  receipt.lineage_distinct = receipt.first_lineage != receipt.second_lineage;
  receipt.exact = receipt.characteristic_equal && receipt.lineage_distinct;
}

HOLONICS_CALLABLE constexpr void form_matrix_control(
    matrix_control_receipt& receipt) noexcept {
  constexpr matrix_two a{1, 1, 0, 1};
  constexpr matrix_two b{1, 0, 1, 1};
  constexpr matrix_two c{2, 0, 0, 1};
  receipt.first_word[0] = a;
  receipt.first_word[1] = b;
  receipt.first_word[2] = c;
  receipt.second_word[0] = a;
  receipt.second_word[1] = c;
  receipt.second_word[2] = b;
  receipt.first_lineage = fold_matrix_word(receipt.first_word, 3);
  receipt.second_lineage = fold_matrix_word(receipt.second_word, 3);
  receipt.order_lineage_distinct = receipt.first_lineage != receipt.second_lineage;
  matrix_two ab{};
  matrix_two ac{};
  const bool first_ok = multiply(a, b, ab) && multiply(ab, c, receipt.ordered_first);
  const bool second_ok = multiply(a, c, ac) && multiply(ac, b, receipt.ordered_second);
  receipt.first_trace = trace(receipt.ordered_first);
  receipt.second_trace = trace(receipt.ordered_second);
  receipt.first_determinant = determinant(receipt.ordered_first);
  receipt.second_determinant = determinant(receipt.ordered_second);
  receipt.order_changes_characteristic = receipt.first_trace != receipt.second_trace &&
      receipt.first_determinant == receipt.second_determinant;

  receipt.rechart_source = {2, 1, 1, 1};
  receipt.rechart = {1, 1, 0, 1};
  receipt.rechart_inverse = {1, -1, 0, 1};
  const matrix_two rechart_word[3]{
      receipt.rechart, receipt.rechart_source, receipt.rechart_inverse};
  receipt.rechart_lineage = fold_matrix_word(rechart_word, 3);
  matrix_two pm{};
  const bool rechart_ok = multiply(receipt.rechart, receipt.rechart_source, pm) &&
      multiply(pm, receipt.rechart_inverse, receipt.rechart_target);
  receipt.rechart_trace = trace(receipt.rechart_target);
  receipt.rechart_determinant = determinant(receipt.rechart_target);
  receipt.rechart_preserves_characteristic =
      receipt.rechart_trace == trace(receipt.rechart_source) &&
      receipt.rechart_determinant == determinant(receipt.rechart_source) &&
      !same_matrix(receipt.rechart_source, receipt.rechart_target);

  receipt.independent_return = {1, 0, 0, 1};
  receipt.coupled_return = {1, 1, 0, 1};
  receipt.independent_fixed_dimension = fixed_dimension(receipt.independent_return);
  receipt.coupled_fixed_dimension = fixed_dimension(receipt.coupled_return);
  receipt.equal_characteristic_unequal_conduct =
      trace(receipt.independent_return) == trace(receipt.coupled_return) &&
      determinant(receipt.independent_return) == determinant(receipt.coupled_return) &&
      receipt.independent_fixed_dimension == 2 && receipt.coupled_fixed_dimension == 1;
  receipt.exact = first_ok && second_ok && rechart_ok &&
      receipt.order_changes_characteristic && receipt.order_lineage_distinct &&
      receipt.rechart_preserves_characteristic &&
      receipt.equal_characteristic_unequal_conduct;
}

HOLONICS_CALLABLE constexpr void form_indicial(indicial_receipt& receipt) noexcept {
  receipt.zero_coefficients[0] = 0;
  receipt.zero_coefficients[1] = 1;
  receipt.zero_coefficients[2] = 1;
  receipt.one_coefficients[0] = 0;
  receipt.one_coefficients[1] = 0;
  receipt.one_coefficients[2] = 1;
  receipt.infinity_coefficients[0] = 1;
  receipt.infinity_coefficients[1] = -2;
  receipt.infinity_coefficients[2] = 1;
  receipt.zero_roots_zero_negative_one = true;
  receipt.one_repeated_zero = true;
  receipt.infinity_repeated_one = true;
  receipt.recurrence_is_only_one_local_branch = true;
  receipt.exact = true;
}

}  // namespace holonics::organ::characteristic_detail
