#pragma once

#include <holonics/codec/trace_fiber_renderer_atoms.hpp>

namespace holonics::codec::trace_fiber_countermodel_detail {

template <class Writer>
HOLONICS_CALLABLE inline bool trace_equalities(Writer &out, const char *left,
                                               const char *right) noexcept {
  constexpr const char *suffix[6]{"A", "B", "C", "AB", "AC", "BC"};
  for (std::uint8_t i = 0; i < 6; ++i) {
    if (i != 0 && !out.text(" ∧ "))
      return false;
    if (!out.text("matrixTrace ") || !out.text(left) || !out.text(suffix[i]) ||
        !out.text(" = matrixTrace ") || !out.text(right) ||
        !out.text(suffix[i]))
      return false;
  }
  return true;
}
template <class Writer>
HOLONICS_CALLABLE inline bool proof_tail(Writer &out, const char *left,
                                         const char *right) noexcept {
  constexpr const char *suffix[8]{"A", "B", "C", "AB", "AC", "BC", "ABC", "ACB"};
  if (!out.text(" := by\n  norm_num ["))
    return false;
  for (std::uint8_t side = 0; side < 2; ++side)
    for (std::uint8_t i = 0; i < 8; ++i) {
      if (side != 0 || i != 0)
        if (!out.text(", "))
          return false;
      if (!out.text(side == 0 ? left : right) || !out.text(suffix[i]))
        return false;
    }
  return out.text(", matrixTrace, matrixMultiply]\n\n");
}
template <class Writer>
HOLONICS_CALLABLE inline bool countermodel(
    Writer &out, const char *name, const char *left, const char *right,
    const trace_fiber_triple_surface &a, const trace_fiber_triple_surface &b,
    std::uint8_t kind) noexcept {
  using namespace trace_fiber_render_detail;
  if (!triple_definitions(out, left, a) || !triple_definitions(out, right, b) ||
      !out.text("theorem ") || !out.text(name) || !out.text(" :\n  ") ||
      !out.text(left) || !product_facts(out, left) || !out.text(right) ||
      !product_facts(out, right))
    return false;
  if (kind <= 2) {
    if (!trace_equalities(out, left, right) || !out.text(" ∧ "))
      return false;
    if (kind == 0) {
      if (!out.text("matrixTrace ") || !out.text(left) ||
          !out.text("ABC = matrixTrace ") || !out.text(right) ||
          !out.text("ACB ∧ matrixTrace ") || !out.text(left) ||
          !out.text("ACB = matrixTrace ") || !out.text(right) ||
          !out.text("ABC ∧ ") || !out.text(left) || !out.text("ABC ≠ ") ||
          !out.text(left) || !out.text("ACB"))
        return false;
    } else if (kind == 1) {
      if (!out.text("(") || !out.integer(a.source) || !out.text(" : ℕ) ≠ ") ||
          !out.integer(b.source))
        return false;
    } else if (!out.text("(") || !out.text(left) || !out.text("A ≠ ") ||
               !out.text(right) || !out.text("A ∨ ") || !out.text(left) ||
               !out.text("B ≠ ") || !out.text(right) || !out.text("B ∨ ") ||
               !out.text(left) || !out.text("C ≠ ") || !out.text(right) ||
               !out.text("C)"))
      return false;
  } else if (!out.text("matrixTrace ") || !out.text(left) ||
             !out.text("ABC ") || !out.text(kind == 3 ? "=" : "≠") ||
             !out.text(" matrixTrace ") || !out.text(left) ||
             !out.text("ACB"))
    return false;
  return proof_tail(out, left, right);
}

} // namespace holonics::codec::trace_fiber_countermodel_detail
