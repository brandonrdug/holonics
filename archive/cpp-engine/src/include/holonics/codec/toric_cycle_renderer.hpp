#pragma once

#include <holonics/codec/toric_cycle_face.hpp>

namespace holonics::codec::toric_render_detail {

HOLONICS_CALLABLE constexpr bool integer(toric_formal_face& out,
    std::int64_t value) noexcept {
  return append_blind_integer(out.bytes, out.byte_count, value);
}

HOLONICS_CALLABLE constexpr bool quadratic(toric_formal_face& out,
    const std::int64_t form[2][2], const std::int64_t vector[2]) noexcept {
  return integer(out, vector[0]) && append_blind(out.bytes, out.byte_count, " * ") &&
      integer(out, form[0][0]) && append_blind(out.bytes, out.byte_count, " * ") &&
      integer(out, vector[0]) && append_blind(out.bytes, out.byte_count, " + ") &&
      integer(out, vector[0]) && append_blind(out.bytes, out.byte_count, " * ") &&
      integer(out, form[0][1]) && append_blind(out.bytes, out.byte_count, " * ") &&
      integer(out, vector[1]) && append_blind(out.bytes, out.byte_count, " + ") &&
      integer(out, vector[1]) && append_blind(out.bytes, out.byte_count, " * ") &&
      integer(out, form[1][0]) && append_blind(out.bytes, out.byte_count, " * ") &&
      integer(out, vector[0]) && append_blind(out.bytes, out.byte_count, " + ") &&
      integer(out, vector[1]) && append_blind(out.bytes, out.byte_count, " * ") &&
      integer(out, form[1][1]) && append_blind(out.bytes, out.byte_count, " * ") &&
      integer(out, vector[1]);
}

HOLONICS_CALLABLE constexpr bool atom_prefix(
    toric_formal_face& out, bool& first) noexcept {
  const bool returned = first ? append_blind(out.bytes, out.byte_count, "  (") :
      append_blind(out.bytes, out.byte_count, " ∧\n  (");
  first = false;
  return returned;
}

HOLONICS_CALLABLE constexpr bool atom_suffix(toric_formal_face& out) noexcept {
  return append_blind(out.bytes, out.byte_count, ")");
}

HOLONICS_CALLABLE constexpr bool determinant_atom(toric_formal_face& out, bool& first,
    const std::int64_t left[2], const std::int64_t right[2],
    std::int64_t returned) noexcept {
  return atom_prefix(out, first) && append_blind(out.bytes, out.byte_count, "(") &&
      integer(out, left[0]) && append_blind(out.bytes, out.byte_count, " * ") &&
      integer(out, right[1]) && append_blind(out.bytes, out.byte_count, " - ") &&
      integer(out, left[1]) && append_blind(out.bytes, out.byte_count, " * ") &&
      integer(out, right[0]) && append_blind(out.bytes, out.byte_count, " : ℤ) = ") &&
      integer(out, returned) && atom_suffix(out);
}

HOLONICS_CALLABLE constexpr bool relation_atom(toric_formal_face& out, bool& first,
    const toric_cycle_surface& surface, std::uint8_t fan, std::uint8_t relation,
    std::uint8_t coordinate) noexcept {
  if (!atom_prefix(out, first) || !append_blind(out.bytes, out.byte_count, "(")) {
    return false;
  }
  for (std::uint8_t ray = 0; ray < surface.ray_counts[fan]; ++ray) {
    if (ray != 0 && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
    if (!integer(out, surface.principal_relations[fan][relation][ray]) ||
        !append_blind(out.bytes, out.byte_count, " * ") ||
        !integer(out, surface.divisor_classes[fan][ray][coordinate])) { return false; }
  }
  return append_blind(out.bytes, out.byte_count, " : ℤ) = 0") && atom_suffix(out);
}

HOLONICS_CALLABLE constexpr bool equality_atom(toric_formal_face& out, bool& first,
    std::int64_t left, std::int64_t right) noexcept {
  return atom_prefix(out, first) && append_blind(out.bytes, out.byte_count, "(") &&
      integer(out, left) && append_blind(out.bytes, out.byte_count, " : ℤ) = ") &&
      integer(out, right) && atom_suffix(out);
}

HOLONICS_CALLABLE constexpr bool quadratic_atom(toric_formal_face& out, bool& first,
    const std::int64_t form[2][2], const std::int64_t vector[2],
    std::int64_t returned) noexcept {
  return atom_prefix(out, first) && append_blind(out.bytes, out.byte_count, "(") &&
      quadratic(out, form, vector) && append_blind(out.bytes, out.byte_count, " : ℤ) = ") &&
      integer(out, returned) && atom_suffix(out);
}

HOLONICS_CALLABLE constexpr bool proof(const toric_cycle_surface& surface,
    toric_formal_face& out) noexcept {
  if (!append_blind(out.bytes, out.byte_count,
      "import Mathlib.Tactic.NormNum\n\nnamespace Soma.Holonics.R23\n\n"
      "theorem generated_toric_cycle_transport :\n")) { return false; }
  bool first = true;
  for (std::uint8_t fan = 0; fan < 3; ++fan) {
    for (std::uint8_t ray = 0; ray < surface.ray_counts[fan]; ++ray) {
      const auto next = static_cast<std::uint8_t>(
          ray + 1U == surface.ray_counts[fan] ? 0U : ray + 1U);
      if (!determinant_atom(out, first, surface.rays[fan][ray],
          surface.rays[fan][next], surface.cone_determinants[fan][ray])) {
        return false;
      }
    }
  }
  for (std::uint8_t fan = 0; fan < 2; ++fan) {
    for (std::uint8_t relation = 0; relation < 2; ++relation) {
      for (std::uint8_t coordinate = 0; coordinate < surface.quotient_ranks[fan];
          ++coordinate) {
        if (!relation_atom(out, first, surface, fan, relation, coordinate)) {
          return false;
        }
      }
    }
  }
  for (std::uint8_t fan = 0; fan < 3; ++fan) {
    if (!equality_atom(out, first, surface.middle_betti[fan],
            surface.quotient_ranks[fan]) ||
        !equality_atom(out, first, surface.middle_hodge[fan],
            surface.quotient_ranks[fan])) { return false; }
  }
  if (!equality_atom(out, first, surface.base_form[0][0], 0) ||
      !equality_atom(out, first, surface.base_form[0][1], 1) ||
      !equality_atom(out, first, surface.base_form[1][1], 0)) { return false; }
  for (std::uint8_t row = 0; row < 2; ++row) {
    if (!atom_prefix(out, first) || !append_blind(out.bytes, out.byte_count, "(") ||
        !integer(out, surface.base_form[row][0]) ||
        !append_blind(out.bytes, out.byte_count, " * ") ||
        !integer(out, surface.integral_class[0]) ||
        !append_blind(out.bytes, out.byte_count, " + ") ||
        !integer(out, surface.base_form[row][1]) ||
        !append_blind(out.bytes, out.byte_count, " * ") ||
        !integer(out, surface.integral_class[1]) ||
        !append_blind(out.bytes, out.byte_count, " : ℤ) = ") ||
        !integer(out, surface.integral_response[row]) || !atom_suffix(out)) { return false; }
  }
  if (!atom_prefix(out, first) || !append_blind(out.bytes, out.byte_count, "((") ||
      !integer(out, surface.rational_numerator) ||
      !append_blind(out.bytes, out.byte_count, " : ℚ) / ") ||
      !integer(out, surface.rational_denominator) ||
      !append_blind(out.bytes, out.byte_count, ").den = ") ||
      !integer(out, surface.rational_denominator) || !atom_suffix(out)) { return false; }
  if (!atom_prefix(out, first) ||
      !integer(out, surface.incompatible_response[0]) ||
      !append_blind(out.bytes, out.byte_count, " ≠ ") ||
      !integer(out, surface.incompatible_response[2]) || !atom_suffix(out)) { return false; }
  for (std::uint8_t coordinate = 0; coordinate < 2; ++coordinate) {
    if (!atom_prefix(out, first) || !append_blind(out.bytes, out.byte_count, "(") ||
        !integer(out, surface.rays[0][0][coordinate]) ||
        !append_blind(out.bytes, out.byte_count, " + ") ||
        !integer(out, surface.rays[0][1][coordinate]) ||
        !append_blind(out.bytes, out.byte_count, " : ℤ) = ") ||
        !integer(out, surface.derived_ray[coordinate]) || !atom_suffix(out)) { return false; }
  }
  for (std::uint8_t ray = 0; ray < 2; ++ray) {
    for (std::uint8_t coordinate = 0; coordinate < 2; ++coordinate) {
      if (!atom_prefix(out, first) || !append_blind(out.bytes, out.byte_count, "(") ||
          !integer(out, surface.strict_transforms[ray][coordinate]) ||
          !append_blind(out.bytes, out.byte_count, " + ") ||
          !integer(out, surface.exceptional[coordinate]) ||
          !append_blind(out.bytes, out.byte_count, " : ℤ) = ") ||
          !integer(out, surface.total_transforms[ray][coordinate]) ||
          !atom_suffix(out)) { return false; }
    }
  }
  for (std::uint8_t coordinate = 0; coordinate < 2; ++coordinate) {
    if (!equality_atom(out, first, surface.total_transforms[2][coordinate],
        surface.pullback[coordinate])) { return false; }
  }
  if (!atom_prefix(out, first) || !append_blind(out.bytes, out.byte_count, "(") ||
      !integer(out, surface.exceptional[0]) ||
      !append_blind(out.bytes, out.byte_count, " * ") ||
      !integer(out, surface.pushforward[0]) ||
      !append_blind(out.bytes, out.byte_count, " + ") ||
      !integer(out, surface.exceptional[1]) ||
      !append_blind(out.bytes, out.byte_count, " * ") ||
      !integer(out, surface.pushforward[1]) ||
      !append_blind(out.bytes, out.byte_count, " : ℤ) = 0") || !atom_suffix(out)) { return false; }
  if (!quadratic_atom(out, first, surface.base_form, surface.negative_class,
          surface.negative_square) ||
      !quadratic_atom(out, first, surface.blowup_form, surface.exceptional,
          surface.exceptional_square) ||
      !quadratic_atom(out, first, surface.blowup_form, surface.blowup_negative,
          surface.blowup_negative_square)) { return false; }
  return append_blind(out.bytes, out.byte_count,
      " := by native_decide\n\nend Soma.Holonics.R23\n\n"
      "#check Soma.Holonics.R23.generated_toric_cycle_transport\n");
}

}  // namespace holonics::codec::toric_render_detail

namespace holonics::codec {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_toric_cycle(
    const toric_cycle_surface& surface, toric_formal_face& out) noexcept {
  if (surface.passage.value() == 0 || !surface.fan_chow_agree ||
      !surface.inverse_fibers_exact || !surface.blowup_transport_exact ||
      !surface.alternatives_retained) { return false; }
  out.identity = exact::word{127'500};
  out.passage = surface.passage;
  return toric_render_detail::proof(surface, out);
}

}  // namespace holonics::codec
