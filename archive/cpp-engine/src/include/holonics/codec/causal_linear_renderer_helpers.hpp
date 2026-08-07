#pragma once

#include <holonics/codec/causal_linear_face.hpp>

namespace holonics::codec::causal_linear_render_detail {

template<class Face>
HOLONICS_CALLABLE constexpr bool integer(Face& out, std::int64_t value) noexcept {
  return append_blind_integer(out.bytes, out.byte_count, value);
}

template<class Face>
HOLONICS_CALLABLE constexpr bool natural(Face& out, std::uint8_t value) noexcept {
  return integer(out, value);
}

template<class Face>
HOLONICS_CALLABLE constexpr bool cm_factor(const causal_linear_surface& surface,
    Face& out) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "  (∀ x : ℤ, ((")) { return false; }
  for (std::uint8_t factor = 0; factor < surface.factor_count; ++factor) {
    if (factor != 0 && !append_blind(out.bytes, out.byte_count, " * ")) { return false; }
    if (!append_blind(out.bytes, out.byte_count, "(x - (") ||
        !integer(out, surface.cm_factor_roots[factor]) ||
        !append_blind(out.bytes, out.byte_count, "))^") ||
        !natural(out, surface.cm_factor_multiplicities[factor])) { return false; }
  }
  if (!append_blind(out.bytes, out.byte_count, ") = (") ) { return false; }
  for (std::uint8_t slot = 0; slot < 17; ++slot) {
    if (slot != 0 && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
    if (!integer(out, surface.cm_characteristic[slot]) ||
        !append_blind(out.bytes, out.byte_count, "*x^") ||
        !natural(out, static_cast<std::uint8_t>(16U - slot))) { return false; }
  }
  return append_blind(out.bytes, out.byte_count, "))) ∧\n");
}

template<class Face>
HOLONICS_CALLABLE constexpr bool pencil(const causal_linear_surface& surface,
    Face& out) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "  (∀ t : ℤ, ((")) { return false; }
  const std::uint8_t entries[4][2]{{0,0},{1,1},{0,1},{1,0}};
  for (std::uint8_t entry = 0; entry < 4; ++entry) {
    if (entry == 2 && !append_blind(out.bytes, out.byte_count, ") - ((")) { return false; }
    else if (entry != 0 && entry != 2 &&
        !append_blind(out.bytes, out.byte_count, ") * (")) { return false; }
    const auto row = entries[entry][0]; const auto column = entries[entry][1];
    if (!integer(out, surface.pencil[row][column][0]) ||
        !append_blind(out.bytes, out.byte_count, " + ") ||
        !integer(out, surface.pencil[row][column][1]) ||
        !append_blind(out.bytes, out.byte_count, "*t")) { return false; }
  }
  if (!append_blind(out.bytes, out.byte_count, ")) = (") ||
      !integer(out, surface.determinant[0]) ||
      !append_blind(out.bytes, out.byte_count, " + ") ||
      !integer(out, surface.determinant[1]) ||
      !append_blind(out.bytes, out.byte_count, "*t + ") ||
      !integer(out, surface.determinant[2]) ||
      !append_blind(out.bytes, out.byte_count, "*t^2))) ∧\n")) { return false; }
  return true;
}

template<class Face>
HOLONICS_CALLABLE constexpr bool form_entry(Face& out,
    const std::int64_t matrix[2][2], const std::int64_t form[2][2],
    std::uint8_t row, std::uint8_t column) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "((")) { return false; }
  for (std::uint8_t left = 0; left < 2; ++left) {
    for (std::uint8_t right = 0; right < 2; ++right) {
      if ((left != 0 || right != 0) && !append_blind(out.bytes, out.byte_count, " + ")) {
        return false;
      }
      if (!integer(out, matrix[left][row]) || !append_blind(out.bytes, out.byte_count, "*") ||
          !integer(out, form[left][right]) || !append_blind(out.bytes, out.byte_count, "*") ||
          !integer(out, matrix[right][column])) { return false; }
    }
  }
  return append_blind(out.bytes, out.byte_count, " : ℤ) = ") &&
      integer(out, form[row][column]) && append_blind(out.bytes, out.byte_count, ")");
}

template<class Face>
HOLONICS_CALLABLE constexpr bool form_atoms(const causal_linear_surface& surface,
    Face& out) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "  (")) { return false; }
  for (std::uint8_t loop = 0; loop < 3; ++loop) {
    for (std::uint8_t row = 0; row < 2; ++row) {
      for (std::uint8_t column = 0; column < 2; ++column) {
        if ((loop != 0 || row != 0 || column != 0) &&
            !append_blind(out.bytes, out.byte_count, " ∧ ")) { return false; }
        if (!form_entry(out, surface.loops[loop], surface.form, row, column)) { return false; }
      }
    }
  }
  return append_blind(out.bytes, out.byte_count, ")\n");
}

}  // namespace holonics::codec::causal_linear_render_detail
