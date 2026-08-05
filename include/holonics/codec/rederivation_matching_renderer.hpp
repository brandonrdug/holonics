#pragma once

#include <holonics/codec/rederivation_face.hpp>

namespace holonics::codec::rederivation_matching_render_detail {

template <class Writer>
HOLONICS_CALLABLE inline bool render(const rederivation_surface &source,
                                     Writer &out) noexcept {
  for (std::uint8_t block = 0; block < 49; ++block) {
    if (!out.text("def matchingBlock") || !out.natural(block) ||
        !out.text(" : Prop :=\n  "))
      return false;
    for (std::uint8_t slot = 0; slot < 49; ++slot) {
      const auto linear = static_cast<std::size_t>(block) * 49U + slot;
      const auto &entry = source.jacobian[linear];
      if (slot != 0 && !out.text(" ∧\n  "))
        return false;
      if (!out.text("((") || !out.integer(entry.value) ||
          !out.text(" : ℤ) = ") || !out.integer(entry.row_factor) ||
          !out.text(" * ") || !out.integer(entry.p_evaluation) ||
          !out.text(" * ") || !out.integer(entry.q_evaluation) ||
          !out.text(")"))
        return false;
    }
    if (!out.text("\n\ntheorem generated_matching_block_") ||
        !out.natural(block) || !out.text(" : matchingBlock") ||
        !out.natural(block) || !out.text(" := by\n  unfold matchingBlock") ||
        !out.natural(block) || !out.text("\n  norm_num\n\n"))
      return false;
  }
  if (!out.text("def matchingFactorStatement : Prop :=\n  "))
    return false;
  for (std::size_t slot = 0; slot < rederivation_surface_factors; ++slot) {
    const auto &factor = source.factors[slot];
    if (slot != 0 && !out.text(" ∧\n  "))
      return false;
    if (!out.text("((") || !out.integer(factor.p_leading) ||
        !out.text(" : ℤ) ≠ 0) ∧ ((") || !out.integer(factor.q_leading) ||
        !out.text(" : ℤ) ≠ 0) ∧ ((") || !out.integer(factor.row_factor) ||
        !out.text(" : ℤ) ≠ 0)"))
      return false;
  }
  if (!out.text(" ∧\n  ((") || !out.integer(source.p_vandermonde) ||
      !out.text(" : ℤ) ≠ 0) ∧ ((") || !out.integer(source.q_vandermonde) ||
      !out.text(
          " : ℤ) ≠ 0)\n\ntheorem generated_matching_nonzero_factors : "
          "matchingFactorStatement := by\n  unfold matchingFactorStatement\n  "
          "norm_num\n\ndef matchingStatement : Prop :=\n  "))
    return false;
  for (std::uint8_t block = 0; block < 49; ++block) {
    if (block != 0 && !out.text(" ∧\n  "))
      return false;
    if (!out.text("matchingBlock") || !out.natural(block))
      return false;
  }
  if (!out.text(
          " ∧\n  matchingFactorStatement\n\ntheorem "
          "generated_matching_independence : "
          "matchingStatement := by\n  unfold matchingStatement\n  exact ⟨"))
    return false;
  for (std::uint8_t block = 0; block < 49; ++block) {
    if (block != 0 && !out.text(", "))
      return false;
    if (!out.text("generated_matching_block_") || !out.natural(block))
      return false;
  }
  return out.text(", generated_matching_nonzero_factors⟩\n\n");
}

} // namespace holonics::codec::rederivation_matching_render_detail
