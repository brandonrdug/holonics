#pragma once

#include <holonics/codec/hodge_realization_face.hpp>

namespace holonics::codec::hodge_render_detail {

template<class Face>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool integer(Face& out, std::int64_t value) noexcept {
  return append_blind_integer(out.bytes, out.byte_count, value);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool discriminant(
    hodge_formal_face& out, const hodge_realization_surface& source) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "(∀ z : ℤ, (")) { return false; }
  for (std::uint8_t degree = 0; degree < 5; ++degree) {
    if (degree != 0 && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
    if (!integer(out, source.discriminant[degree]) ||
        !append_blind(out.bytes, out.byte_count, "*z^") || !integer(out, degree)) { return false; }
  }
  return append_blind(out.bytes, out.byte_count, ") = z^2*(1-z)^2)");
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool preservation_atom(hodge_formal_face& out,
    const std::int64_t (&connection)[hodge_surface_rank][hodge_surface_rank],
    const std::int64_t (&cup)[hodge_surface_rank][hodge_surface_rank],
    std::uint8_t row, std::uint8_t column) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "((")) { return false; }
  for (std::uint8_t k = 0; k < hodge_surface_rank; ++k) {
    if (k != 0 && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
    if (!integer(out, connection[k][row]) || !append_blind(out.bytes, out.byte_count, "*") ||
        !integer(out, cup[k][column]) || !append_blind(out.bytes, out.byte_count, " + ") ||
        !integer(out, cup[row][k]) || !append_blind(out.bytes, out.byte_count, "*") ||
        !integer(out, connection[k][column])) { return false; }
  }
  return append_blind(out.bytes, out.byte_count, " : ℤ) = 0)");
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool commutator_atom(hodge_formal_face& out,
    const hodge_realization_surface& source, std::uint8_t row, std::uint8_t column) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "((")) { return false; }
  for (std::uint8_t k = 0; k < hodge_surface_rank; ++k) {
    if (k != 0 && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
    if (!integer(out, source.connection_t[row][k]) ||
        !append_blind(out.bytes, out.byte_count, "*") ||
        !integer(out, source.connection_u[k][column]) ||
        !append_blind(out.bytes, out.byte_count, " - ") ||
        !integer(out, source.connection_u[row][k]) ||
        !append_blind(out.bytes, out.byte_count, "*") ||
        !integer(out, source.connection_t[k][column])) { return false; }
  }
  return append_blind(out.bytes, out.byte_count, " : ℤ) = 0)");
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool transport(
    hodge_formal_face& out, const hodge_realization_surface& source) noexcept {
  bool first = true;
  for (std::uint8_t family = 0; family < 3; ++family) {
    for (std::uint8_t row = 0; row < hodge_surface_rank; ++row) {
      for (std::uint8_t column = 0; column < hodge_surface_rank; ++column) {
        if (!first && !append_blind(out.bytes, out.byte_count, " ∧\n  ")) { return false; }
        first = false;
        if (family == 0 && !preservation_atom(out, source.connection_t, source.cup, row, column)) {
          return false;
        }
        if (family == 1 && !preservation_atom(out, source.connection_u, source.cup, row, column)) {
          return false;
        }
        if (family == 2 && !commutator_atom(out, source, row, column)) { return false; }
      }
    }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool pairing(hodge_formal_face& out,
    const std::int64_t (&left)[hodge_surface_rank],
    const std::int64_t (&cup)[hodge_surface_rank][hodge_surface_rank],
    const std::int64_t (&right)[hodge_surface_rank], std::int64_t result) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "((")) { return false; }
  bool first = true;
  for (std::uint8_t row = 0; row < hodge_surface_rank; ++row) {
    for (std::uint8_t column = 0; column < hodge_surface_rank; ++column) {
      if (!first && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
      first = false;
      if (!integer(out, left[row]) || !append_blind(out.bytes, out.byte_count, "*") ||
          !integer(out, cup[row][column]) || !append_blind(out.bytes, out.byte_count, "*") ||
          !integer(out, right[column])) { return false; }
    }
  }
  return append_blind(out.bytes, out.byte_count, " : ℤ) = ") && integer(out, result) &&
      append_blind(out.bytes, out.byte_count, ")");
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool graph_relations(
    hodge_formal_face& out, const hodge_realization_surface& source) noexcept {
  for (std::uint8_t slot = 0; slot < hodge_surface_rank; ++slot) {
    if (slot != 0 && !append_blind(out.bytes, out.byte_count, " ∧\n  ")) { return false; }
    if (!append_blind(out.bytes, out.byte_count, "((") || !integer(out, source.graph[slot]) ||
        !append_blind(out.bytes, out.byte_count, " + ") || !integer(out, source.negation[slot]) ||
        !append_blind(out.bytes, out.byte_count, " : ℤ) = 2*") ||
        !integer(out, source.polarization[slot]) || !append_blind(out.bytes, out.byte_count, ")")) {
      return false;
    }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool pull_push_atom(hodge_formal_face& out,
    const hodge_realization_surface& source, std::uint8_t row, std::uint8_t column) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "((")) { return false; }
  for (std::uint8_t slot = 0; slot < hodge_surface_blowup_rank; ++slot) {
    if (slot != 0 && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
    if (!integer(out, source.pushforward[row][slot]) ||
        !append_blind(out.bytes, out.byte_count, "*") ||
        !integer(out, source.pullback[slot][column])) { return false; }
  }
  return append_blind(out.bytes, out.byte_count, " : ℤ) = ") &&
      integer(out, row == column ? 1 : 0) && append_blind(out.bytes, out.byte_count, ")");
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool projection_atom(hodge_formal_face& out,
    const hodge_realization_surface& source, std::uint8_t owner, std::uint8_t target) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "((")) { return false; }
  for (std::uint8_t row = 0; row < hodge_surface_rank; ++row) {
    if (row != 0 && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
    if (!integer(out, source.pushforward[row][owner]) ||
        !append_blind(out.bytes, out.byte_count, "*") ||
        !integer(out, source.cup[row][target])) { return false; }
  }
  if (!append_blind(out.bytes, out.byte_count, " : ℤ) = (")) { return false; }
  for (std::uint8_t row = 0; row < hodge_surface_blowup_rank; ++row) {
    if (row != 0 && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
    if (!integer(out, source.blowup_pairing[owner][row]) ||
        !append_blind(out.bytes, out.byte_count, "*") ||
        !integer(out, source.pullback[row][target])) { return false; }
  }
  return append_blind(out.bytes, out.byte_count, " : ℤ))");
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool blowup_maps(
    hodge_formal_face& out, const hodge_realization_surface& source) noexcept {
  bool first = true;
  for (std::uint8_t row = 0; row < hodge_surface_rank; ++row) {
    for (std::uint8_t column = 0; column < hodge_surface_rank; ++column) {
      if (!first && !append_blind(out.bytes, out.byte_count, " ∧\n  ")) { return false; }
      first = false; if (!pull_push_atom(out, source, row, column)) { return false; }
    }
  }
  for (std::uint8_t owner = 0; owner < hodge_surface_blowup_rank; ++owner) {
    for (std::uint8_t target = 0; target < hodge_surface_rank; ++target) {
      if (!append_blind(out.bytes, out.byte_count, " ∧\n  ") ||
          !projection_atom(out, source, owner, target)) { return false; }
    }
  }
  for (std::uint8_t row = 0; row < hodge_surface_rank; ++row) {
    if (!append_blind(out.bytes, out.byte_count, " ∧\n  ((") ||
        !integer(out, source.pushforward[row][6]) ||
        !append_blind(out.bytes, out.byte_count, " : ℤ) = 0)")) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool blowup_pairing(hodge_formal_face& out,
    const std::int64_t (&left)[hodge_surface_blowup_rank],
    const std::int64_t (&pairing_matrix)[hodge_surface_blowup_rank][hodge_surface_blowup_rank],
    const std::int64_t (&right)[hodge_surface_blowup_rank], std::int64_t result) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "((")) { return false; }
  bool first = true;
  for (std::uint8_t row = 0; row < hodge_surface_blowup_rank; ++row) {
    for (std::uint8_t column = 0; column < hodge_surface_blowup_rank; ++column) {
      if (!first && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
      first = false;
      if (!integer(out, left[row]) || !append_blind(out.bytes, out.byte_count, "*") ||
          !integer(out, pairing_matrix[row][column]) ||
          !append_blind(out.bytes, out.byte_count, "*") || !integer(out, right[column])) {
        return false;
      }
    }
  }
  return append_blind(out.bytes, out.byte_count, " : ℤ) = ") && integer(out, result) &&
      append_blind(out.bytes, out.byte_count, ")");
}

}  // namespace holonics::codec::hodge_render_detail
