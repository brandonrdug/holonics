#pragma once

#include <holonics/organ/hodge_factor_law.hpp>

namespace holonics::organ::hodge_product_detail {

HOLONICS_CALLABLE constexpr void set_affine(affine_integer_coefficient (&matrix)[6][6],
    std::uint8_t target, std::uint8_t source, affine_integer_coefficient value) noexcept {
  matrix[target][source] = value;
}

HOLONICS_CALLABLE constexpr void induced_connections(
    const hodge_factor_receipt (&factors)[2], hodge_product_receipt& out) noexcept {
  const auto (&left)[2][2] = factors[0].connection;
  const auto (&right)[2][2] = factors[1].connection;
  set_affine(out.connection_t,2,2,left[0][0]); set_affine(out.connection_t,4,2,left[0][1]);
  set_affine(out.connection_t,3,3,left[0][0]); set_affine(out.connection_t,5,3,left[0][1]);
  set_affine(out.connection_t,2,4,left[1][0]); set_affine(out.connection_t,4,4,left[1][1]);
  set_affine(out.connection_t,3,5,left[1][0]); set_affine(out.connection_t,5,5,left[1][1]);
  set_affine(out.connection_u,2,2,right[0][0]); set_affine(out.connection_u,3,2,right[0][1]);
  set_affine(out.connection_u,2,3,right[1][0]); set_affine(out.connection_u,3,3,right[1][1]);
  set_affine(out.connection_u,4,4,right[0][0]); set_affine(out.connection_u,5,4,right[0][1]);
  set_affine(out.connection_u,4,5,right[1][0]); set_affine(out.connection_u,5,5,right[1][1]);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t affine_value(
    affine_integer_coefficient value, std::int64_t parameter) noexcept {
  return value.constant + value.parameter * parameter;
}

HOLONICS_CALLABLE constexpr void evaluate_base(hodge_product_receipt& out,
    std::int64_t t, std::int64_t u) noexcept {
  for (std::uint8_t row = 0; row < 6; ++row) {
    for (std::uint8_t column = 0; column < 6; ++column) {
      out.connection_t_base[row][column] = affine_value(out.connection_t[row][column], t);
      out.connection_u_base[row][column] = affine_value(out.connection_u[row][column], u);
    }
  }
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool preserves(
    const affine_integer_coefficient (&connection)[6][6],
    const std::int64_t (&cup)[6][6]) noexcept {
  for (std::uint8_t power = 0; power < 2; ++power) {
    for (std::uint8_t row = 0; row < 6; ++row) {
      for (std::uint8_t column = 0; column < 6; ++column) {
        std::int64_t sum = 0;
        for (std::uint8_t slot = 0; slot < 6; ++slot) {
          const auto left = power == 0 ? connection[slot][row].constant :
              connection[slot][row].parameter;
          const auto right = power == 0 ? connection[slot][column].constant :
              connection[slot][column].parameter;
          sum += left * cup[slot][column] + cup[row][slot] * right;
        }
        if (sum != 0) { return false; }
      }
    }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool commute_at_base(
    const hodge_product_receipt& out) noexcept {
  for (std::uint8_t row = 0; row < 6; ++row) {
    for (std::uint8_t column = 0; column < 6; ++column) {
      std::int64_t left = 0; std::int64_t right = 0;
      for (std::uint8_t slot = 0; slot < 6; ++slot) {
        left += out.connection_t_base[row][slot] * out.connection_u_base[slot][column];
        right += out.connection_u_base[row][slot] * out.connection_t_base[slot][column];
      }
      if (left != right) { return false; }
    }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t pairing(
    const hodge_product_receipt& product, const std::int64_t (&left)[6],
    const std::int64_t (&right)[6]) noexcept {
  std::int64_t result = 0;
  for (std::uint8_t row = 0; row < 6; ++row) {
    for (std::uint8_t column = 0; column < 6; ++column) {
      result += left[row] * product.cup[row][column] * right[column];
    }
  }
  return result;
}

HOLONICS_CALLABLE constexpr void derive(const hodge_factor_receipt (&factors)[2],
    const hodge_realization_card& card, hodge_product_receipt& out) noexcept {
  if (!factors[0].exact || !factors[1].exact) { return; }
  for (std::uint8_t slot = 0; slot < 6; ++slot) {
    out.basis[slot] = exact::word{195'450U + slot};
  }
  out.cup[0][1] = 1; out.cup[1][0] = 1;
  out.cup[2][5] = -1; out.cup[5][2] = -1;
  out.cup[3][4] = 1; out.cup[4][3] = 1;
  out.polarization[0] = 1; out.polarization[1] = 1;
  out.f2_basis[0] = 2; constexpr std::uint8_t f1[5]{0,1,2,3,4};
  for (std::uint8_t slot = 0; slot < 5; ++slot) { out.f1_basis[slot] = f1[slot]; }
  induced_connections(factors, out); evaluate_base(out, card.base_t, card.base_u);
  out.identity = exact::word{195'460};
  out.lineage = exact::word{card.lineage.value() + 128U};
  out.common_denominator = -4; out.rational_rank = 6; out.f2_rank = 1; out.f1_rank = 5;
  out.h20 = 1; out.h11 = 4; out.h02 = 1;
  out.cup_nondegenerate = true;
  out.polarization_square_two = pairing(out, out.polarization, out.polarization) == 2;
  out.connection_t_preserves_cup = preserves(out.connection_t, out.cup);
  out.connection_u_preserves_cup = preserves(out.connection_u, out.cup);
  out.mixed_curvature_zero = commute_at_base(out);
  out.griffiths_transverse = out.connection_t_base[5][2] == 0 &&
      out.connection_u_base[5][2] == 0;
  out.standard_comparison_boundary = true;
  out.exact = out.cup_nondegenerate && out.polarization_square_two &&
      out.connection_t_preserves_cup && out.connection_u_preserves_cup &&
      out.mixed_curvature_zero && out.griffiths_transverse;
}

}  // namespace holonics::organ::hodge_product_detail
