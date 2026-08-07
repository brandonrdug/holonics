#pragma once

#include <holonics/codec/algebraic_variation_renderer_equations.hpp>
#include <holonics/codec/algebraic_variation_renderer_matrices.hpp>

namespace holonics::codec::variation_render_detail {

HOLONICS_CALLABLE constexpr bool theorem(const algebraic_variation_surface& surface,
    variation_formal_face& out) noexcept {
  if (!append_blind(out.bytes, out.byte_count,
      "import Mathlib.Tactic.NormNum\nimport Mathlib.Tactic.Ring\n"
      "import Mathlib.Tactic.Linarith\n\nnamespace Soma.Holonics.R24\n\n"
      "theorem generated_algebraic_variation\n"
      "    (t x u v du dv ddu : ℚ)\n") ||
      !singular_hypotheses(surface, out) ||
      !connection_hypothesis(surface, out, 0, "h0", "du") ||
      !connection_hypothesis(surface, out, 1, "h1", "dv") ||
      !derivative_hypothesis(surface, out)) {
    return false;
  }
  bool first = true;
  if (!scalar_atom(surface, out, first) ||
      !polynomial_atom(surface, out, first) || !reduction_atom(surface, out, first, 0) ||
      !reduction_atom(surface, out, first, 1)) { return false; }
  for (std::uint8_t loop = 0; loop < 3; ++loop) {
    if (!preservation_atom(out, first, surface.monodromy[loop], surface.invariant)) {
      return false;
    }
  }
  if (!ordered_product_atom(out, first, surface.monodromy[0], surface.monodromy[1],
      surface.monodromy[2])) { return false; }
  for (std::uint8_t n = 0; n + 1U < surface.series_count; ++n) {
    if (!recurrence_atom(surface, out, first, n)) { return false; }
  }
  if (!append_blind(out.bytes, out.byte_count, " := by\n") ||
      !scalar_proof(surface, out)) { return false; }
  for (std::uint8_t atom = 0; atom < 3; ++atom) {
    if (!append_blind(out.bytes, out.byte_count, "  constructor\n  · ring\n")) {
      return false;
    }
  }
  if (!append_blind(out.bytes, out.byte_count,
      "  constructor\n  · norm_num\n  · norm_num\n\n"
      "end Soma.Holonics.R24\n\n"
      "#check Soma.Holonics.R24.generated_algebraic_variation\n")) { return false; }
  return true;
}

}  // namespace holonics::codec::variation_render_detail

namespace holonics::codec {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_algebraic_variation(
    const algebraic_variation_surface& surface, variation_formal_face& out) noexcept {
  if (surface.passage.value() == 0 || !surface.family_exact || !surface.reduction_exact ||
      !surface.connection_exact || !surface.invariant_exact || !surface.operator_exact ||
      !surface.loops_exact || !surface.selection_exact || !surface.alternatives_retained) {
    return false;
  }
  out.identity = exact::word{127'600}; out.passage = surface.passage;
  return variation_render_detail::theorem(surface, out);
}

}  // namespace holonics::codec
