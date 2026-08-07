#pragma once

#include <holonics/codec/algebraic_variation_renderer_atoms.hpp>

namespace holonics::codec::variation_render_detail {

HOLONICS_CALLABLE constexpr bool preservation_atom(variation_formal_face& out, bool& first,
    const std::int64_t matrix[2][2], const std::int64_t form[2][2]) noexcept {
  if (!atom_prefix(out, first)) { return false; }
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      if ((row != 0 || column != 0) &&
          !append_blind(out.bytes, out.byte_count, " ∧ ")) { return false; }
      if (!append_blind(out.bytes, out.byte_count, "((") ||
          !integer(out, matrix[0][row]) || !append_blind(out.bytes, out.byte_count, "*") ||
          !integer(out, form[0][0]) || !append_blind(out.bytes, out.byte_count, " + ") ||
          !integer(out, matrix[1][row]) || !append_blind(out.bytes, out.byte_count, "*") ||
          !integer(out, form[1][0]) || !append_blind(out.bytes, out.byte_count, ")*") ||
          !integer(out, matrix[0][column]) || !append_blind(out.bytes, out.byte_count, " + (") ||
          !integer(out, matrix[0][row]) || !append_blind(out.bytes, out.byte_count, "*") ||
          !integer(out, form[0][1]) || !append_blind(out.bytes, out.byte_count, " + ") ||
          !integer(out, matrix[1][row]) || !append_blind(out.bytes, out.byte_count, "*") ||
          !integer(out, form[1][1]) || !append_blind(out.bytes, out.byte_count, ")*") ||
          !integer(out, matrix[1][column]) ||
          !append_blind(out.bytes, out.byte_count, " : ℤ) = ") ||
          !integer(out, form[row][column])) { return false; }
    }
  }
  return atom_suffix(out);
}

HOLONICS_CALLABLE constexpr bool ordered_product_atom(variation_formal_face& out, bool& first,
    const std::int64_t first_matrix[2][2], const std::int64_t second_matrix[2][2],
    const std::int64_t third_matrix[2][2]) noexcept {
  if (!atom_prefix(out, first)) { return false; }
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      if ((row != 0 || column != 0) &&
          !append_blind(out.bytes, out.byte_count, " ∧ ")) { return false; }
      if (!append_blind(out.bytes, out.byte_count, "((") ||
          !integer(out, first_matrix[row][0]) || !append_blind(out.bytes, out.byte_count, "*") ||
          !integer(out, second_matrix[0][0]) || !append_blind(out.bytes, out.byte_count, " + ") ||
          !integer(out, first_matrix[row][1]) || !append_blind(out.bytes, out.byte_count, "*") ||
          !integer(out, second_matrix[1][0]) || !append_blind(out.bytes, out.byte_count, ")*") ||
          !integer(out, third_matrix[0][column]) || !append_blind(out.bytes, out.byte_count, " + (") ||
          !integer(out, first_matrix[row][0]) || !append_blind(out.bytes, out.byte_count, "*") ||
          !integer(out, second_matrix[0][1]) || !append_blind(out.bytes, out.byte_count, " + ") ||
          !integer(out, first_matrix[row][1]) || !append_blind(out.bytes, out.byte_count, "*") ||
          !integer(out, second_matrix[1][1]) || !append_blind(out.bytes, out.byte_count, ")*") ||
          !integer(out, third_matrix[1][column]) ||
          !append_blind(out.bytes, out.byte_count, " : ℤ) = ") ||
          !integer(out, row == column ? 1 : 0)) { return false; }
    }
  }
  return atom_suffix(out);
}

}  // namespace holonics::codec::variation_render_detail
