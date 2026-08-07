#pragma once

#include <holonics/codec/causal_linear_renderer_helpers.hpp>
#include <holonics/codec/intrinsic_hypergeometry_face.hpp>

namespace holonics::codec::intrinsic_hypergeometry_render_detail {

using intrinsic_hypergeometry_formal_face = codec::intrinsic_hypergeometry_formal_face;

[[nodiscard]] HOLONICS_CALLABLE constexpr bool natural(
    intrinsic_hypergeometry_formal_face& out, std::uint64_t value) noexcept {
  return causal_linear_render_detail::integer(out, static_cast<std::int64_t>(value));
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool integer(
    intrinsic_hypergeometry_formal_face& out, std::int64_t value) noexcept {
  return causal_linear_render_detail::integer(out, value);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool append_case(
    intrinsic_hypergeometry_formal_face& out, const intrinsic_case_surface& value) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "  ((") || !natural(out, value.vertices) ||
      !append_blind(out.bytes, out.byte_count, " : ℕ) + ") || !natural(out, value.faces) ||
      !append_blind(out.bytes, out.byte_count, " = ") || !natural(out, value.edges) ||
      !append_blind(out.bytes, out.byte_count, " ∧ (") || !natural(out, value.flags) ||
      !append_blind(out.bytes, out.byte_count, " : ℕ) = 8 * ") || !natural(out, value.faces) ||
      !append_blind(out.bytes, out.byte_count, " ∧ (") || !natural(out, value.tours) ||
      !append_blind(out.bytes, out.byte_count, " : ℕ) * ") || !natural(out, value.lcm) ||
      !append_blind(out.bytes, out.byte_count, " = ") || !natural(out, value.vertices) ||
      !append_blind(out.bytes, out.byte_count, " ∧ (") || !natural(out, value.seams[0]) ||
      !append_blind(out.bytes, out.byte_count, " : ℕ) + ") || !natural(out, value.seams[1]) ||
      !append_blind(out.bytes, out.byte_count, " + ") || !natural(out, value.seams[2]) ||
      !append_blind(out.bytes, out.byte_count, " + ") || !natural(out, value.seams[3]) ||
      !append_blind(out.bytes, out.byte_count, " = ") || !natural(out, value.vertices)) {
    return false;
  }
  for (std::uint8_t row = 0; row < 4; ++row) {
    if (!append_blind(out.bytes, out.byte_count, " ∧ (") ||
        !natural(out, value.transition_rows[row]) ||
        !append_blind(out.bytes, out.byte_count, " : ℕ) = ") ||
        !natural(out, value.seams[row])) { return false; }
  }
  return append_blind(out.bytes, out.byte_count, ")");
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool append_characteristic(
    intrinsic_hypergeometry_formal_face& out,
    const intrinsic_hypergeometry_surface& surface) noexcept {
  for (std::uint8_t slot = 0; slot < 5; ++slot) {
    if (slot != 0 && !append_blind(out.bytes, out.byte_count, " ∧ ")) { return false; }
    if (!append_blind(out.bytes, out.byte_count, "((") ||
        !integer(out, surface.phase_characteristic[slot]) ||
        !append_blind(out.bytes, out.byte_count, " : ℤ) = ") ||
        !integer(out, surface.cm_characteristic[slot]) ||
        !append_blind(out.bytes, out.byte_count, ")")) { return false; }
  }
  return true;
}

}  // namespace holonics::codec::intrinsic_hypergeometry_render_detail

namespace holonics::codec {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_intrinsic_hypergeometry(
    const intrinsic_hypergeometry_surface& surface,
    intrinsic_hypergeometry_formal_face& out) noexcept {
  using namespace intrinsic_hypergeometry_render_detail;
  if (surface.passage.value() == 0 || !surface.incidence_exact ||
      !surface.distributions_exact || !surface.sections_exact ||
      !surface.supports_separated || !surface.controls_exact ||
      !surface.changed_sensitive || !surface.alternatives_retained) { return false; }
  out.identity = exact::word{128'700}; out.passage = surface.passage;
  if (!append_blind(out.bytes, out.byte_count,
      "import Mathlib.Tactic.NormNum\n\nnamespace Soma.Holonics.R26\n\n"
      "theorem generated_intrinsic_archetype_calculus :\n")) { return false; }
  for (std::uint8_t slot = 0; slot < intrinsic_hypergeometry_case_capacity; ++slot) {
    if (!append_case(out, surface.cases[slot]) ||
        !append_blind(out.bytes, out.byte_count, " ∧\n")) { return false; }
  }
  if (!append_characteristic(out, surface) ||
      !append_blind(out.bytes, out.byte_count, " ∧\n  ") ||
      !append_blind(out.bytes, out.byte_count, "(") || !natural(out, surface.square_count) ||
      !append_blind(out.bytes, out.byte_count, " : ℕ) = 40 ∧ (2 : ℕ) ≠ 1 ∧\n  ((") ||
      !integer(out, surface.commutator[0]) ||
      !append_blind(out.bytes, out.byte_count, " : ℤ) ≠ 1 ∨ (") ||
      !integer(out, surface.commutator[1]) ||
      !append_blind(out.bytes, out.byte_count, " : ℤ) ≠ 0 ∨ (") ||
      !integer(out, surface.commutator[2]) ||
      !append_blind(out.bytes, out.byte_count, " : ℤ) ≠ 0 ∨ (") ||
      !integer(out, surface.commutator[3]) ||
      !append_blind(out.bytes, out.byte_count, " : ℤ) ≠ 1) ∧\n  (") ||
      !natural(out, surface.changed.vertices) ||
      !append_blind(out.bytes, out.byte_count, " : ℕ) ≠ ") ||
      !natural(out, surface.cases[2].vertices) ||
      !append_blind(out.bytes, out.byte_count, " ∧ (") ||
      !natural(out, surface.changed.lcm) ||
      !append_blind(out.bytes, out.byte_count, " : ℕ) ≠ ") ||
      !natural(out, surface.cases[2].lcm) ||
      !append_blind(out.bytes, out.byte_count, " ∧\n  (") ) { return false; }
  for (std::uint8_t slot = 0; slot < 4; ++slot) {
    if (slot != 0 && !append_blind(out.bytes, out.byte_count, " ∨ ")) { return false; }
    if (!append_blind(out.bytes, out.byte_count, "(") ||
        !natural(out, surface.changed.section_return[slot]) ||
        !append_blind(out.bytes, out.byte_count, " : ℕ) ≠ ") ||
        !natural(out, surface.cases[2].section_return[slot])) { return false; }
  }
  return append_blind(out.bytes, out.byte_count,
      ") := by\n  norm_num\n\nend Soma.Holonics.R26\n\n"
      "#check Soma.Holonics.R26.generated_intrinsic_archetype_calculus\n");
}

}  // namespace holonics::codec
