#pragma once

#include <holonics/organ/algebraic_variation_law.hpp>
#include <holonics/organ/causal_linear_toric_law.hpp>

namespace holonics::organ::causal_linear_detail {

HOLONICS_CALLABLE constexpr void pencil_rank(const causal_variation_section& source,
    std::int8_t parameter, std::uint8_t& rank, bool& exact) noexcept {
  causal_integer_matrix matrix{};
  set_matrix(matrix, 2, 2, 192'479U + static_cast<std::uint8_t>(parameter + 2),
      source.lineage.value() + static_cast<std::uint8_t>(parameter + 2));
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      std::int64_t scaled = 0;
      exact = exact && blind_integer_detail::multiply(
          source.pencil[row][column][1], parameter, scaled) &&
          blind_integer_detail::add(source.pencil[row][column][0], scaled,
              matrix.values[row][column]);
    }
  }
  causal_matrix_analysis analysis{}; analyze(matrix, analysis, matrix.identity.value() + 20U);
  exact = exact && analysis.exact; rank = analysis.rank;
}

HOLONICS_CALLABLE constexpr void derive_variation(const algebraic_variation_card& card,
    causal_variation_section& out) noexcept {
  out.identity = exact::word{192'470};
  out.lineage = exact::word{card.lineage.value() + 70U};
  const algebraic_variation_foundation foundation{exact::word{139'740},
      exact::word{139'741}, exact::word{139'742}, exact::word{139'743},
      exact::word{139'744}, exact::word{139'745}, exact::word{139'746},
      exact::word{139'747}, card};
  const algebraic_variation_question question{exact::word{149'740},
      exact::word{149'741}, exact::word{149'742}};
  const auto source = algebraic_variation_detail::derive(foundation, question);
  if (!source.all_exact) { return; }
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      out.pencil[row][column][0] = source.connection.numerator[row][column].constant;
      out.pencil[row][column][1] = source.connection.numerator[row][column].parameter;
      out.form[row][column] = source.invariant.selected[row][column];
      for (std::uint8_t loop = 0; loop < 3; ++loop) {
        out.loops[loop][row][column] = source.loops.monodromy[loop][row][column];
      }
    }
  }
  bool exact = true;
  for (std::uint8_t left = 0; left < 2; ++left) {
    for (std::uint8_t right = 0; right < 2; ++right) {
      const auto degree = static_cast<std::uint8_t>(left + right);
      std::int64_t first = 0; std::int64_t second = 0; std::int64_t difference = 0;
      exact = exact && blind_integer_detail::multiply(
          out.pencil[0][0][left], out.pencil[1][1][right], first) &&
          blind_integer_detail::multiply(
              out.pencil[0][1][left], out.pencil[1][0][right], second) &&
          blind_integer_detail::subtract(first, second, difference) &&
          blind_integer_detail::add(out.determinant[degree], difference,
              out.determinant[degree]);
    }
  }
  out.parameters[0] = 0; out.parameters[1] = 1; out.parameters[2] = 2;
  for (std::uint8_t slot = 0; slot < 3; ++slot) {
    pencil_rank(out, out.parameters[slot], out.ranks[slot], exact);
  }
  out.rank_strata_exact = exact && out.determinant[0] == 0 &&
      out.determinant[1] == 1 && out.determinant[2] == -1 &&
      out.ranks[0] == 1 && out.ranks[1] == 1 && out.ranks[2] == 2;
  out.adjoints_exact = true; out.exterior_exact = true;
  for (std::uint8_t loop = 0; loop < 3; ++loop) {
    bool determinant_exact = true;
    out.adjoints_exact = out.adjoints_exact && preserves_form(out.loops[loop], out.form);
    out.exterior_exact = out.exterior_exact &&
        determinant_two(out.loops[loop], determinant_exact) == 1 && determinant_exact;
  }
  kronecker(out.loops[0], out.loops[1], out.tensor, 192'476, out.lineage.value() + 6U);
  characteristic(out.tensor, out.tensor_characteristic, 192'477);
  out.exact = out.rank_strata_exact && out.adjoints_exact && out.exterior_exact &&
      out.tensor.exact && out.tensor_characteristic.exact;
}

}  // namespace holonics::organ::causal_linear_detail
