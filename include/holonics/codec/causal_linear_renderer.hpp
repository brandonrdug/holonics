#pragma once

#include <holonics/codec/causal_linear_renderer_helpers.hpp>

namespace holonics::codec {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_causal_linear(
    const causal_linear_surface& surface, causal_linear_formal_face& out) noexcept {
  using namespace causal_linear_render_detail;
  if (surface.passage.value() == 0 || !surface.chain_exact ||
      !surface.characteristics_exact || !surface.multilinear_exact ||
      !surface.controls_exact || !surface.alternatives_retained) { return false; }
  out.identity = exact::word{128'600}; out.passage = surface.passage;
  if (!append_blind(out.bytes, out.byte_count,
      "import Mathlib.Tactic.NormNum\nimport Mathlib.Tactic.Ring\n"
      "import Mathlib.Tactic.Linarith\n\nnamespace Soma.Holonics.R25\n\n"
      "theorem generated_causal_linear_calculus :\n  (") ||
      !natural(out, surface.phase_ranks[0]) ||
      !append_blind(out.bytes, out.byte_count, " + ") ||
      !natural(out, surface.phase_betti[0]) ||
      !append_blind(out.bytes, out.byte_count, " = ") ||
      !natural(out, surface.phase_counts[0]) ||
      !append_blind(out.bytes, out.byte_count, " ∧ ") ||
      !natural(out, surface.phase_ranks[1]) ||
      !append_blind(out.bytes, out.byte_count, " + ") ||
      !natural(out, surface.phase_betti[2]) ||
      !append_blind(out.bytes, out.byte_count, " = ") ||
      !natural(out, surface.phase_counts[2]) ||
      !append_blind(out.bytes, out.byte_count, " ∧ ") ||
      !natural(out, surface.phase_betti[1]) ||
      !append_blind(out.bytes, out.byte_count, " = 2 ∧ ") ||
      !natural(out, surface.cm_rank) ||
      !append_blind(out.bytes, out.byte_count, " + ") ||
      !natural(out, surface.cm_homology[0]) ||
      !append_blind(out.bytes, out.byte_count, " = 16 ∧ ") ||
      !natural(out, surface.cm_homology[1]) ||
      !append_blind(out.bytes, out.byte_count, " = 25 ∧ (") ||
      !integer(out, surface.toric_smith[0][0]) ||
      !append_blind(out.bytes, out.byte_count, " : ℤ) = 1 ∧ (") ||
      !integer(out, surface.toric_smith[0][1]) ||
      !append_blind(out.bytes, out.byte_count, " : ℤ) = 1 ∧ ") ||
      !natural(out, surface.identity_fixed) ||
      !append_blind(out.bytes, out.byte_count, " ≠ ") ||
      !natural(out, surface.jordan_fixed) ||
      !append_blind(out.bytes, out.byte_count, ") ∧\n") ||
      !cm_factor(surface, out) || !pencil(surface, out) ||
      !append_blind(out.bytes, out.byte_count, "  (∀ q : ℚ, q^2 + 1 ≠ 0) ∧\n") ||
      !form_atoms(surface, out) ||
      !append_blind(out.bytes, out.byte_count,
      " := by\n  constructor\n  · norm_num\n  constructor\n"
      "  · intro x; ring\n  constructor\n  · intro t; ring\n  constructor\n"
      "  · intro q; nlinarith [sq_nonneg q]\n  · norm_num\n\n"
      "end Soma.Holonics.R25\n\n"
      "#check Soma.Holonics.R25.generated_causal_linear_calculus\n")) { return false; }
  return true;
}

}  // namespace holonics::codec
