#pragma once

#include <holonics/codec/trace_fiber_renderer_atoms.hpp>

namespace holonics::codec {

HOLONICS_CALLABLE inline bool render_heldout_trace_fiber(
    const heldout_trace_fiber_surface &s,
    trace_fiber_formal_face &face) noexcept {
  using rederivation_render_detail::writer;
  using namespace trace_fiber_render_detail;
  writer out{face};
  face.identity = exact::word{201'411};
  face.passage = s.passage;
  trace_fiber_triple_surface triple{};
  for (std::uint8_t i = 0; i < 8; ++i)
    triple.matrices[i] = s.matrices[i];
  if (!s.exact || !s.prediction_before_comparison || !s.source_detached ||
      !out.text("import R34_TRACE_FIBER_LIFTING\n\nnamespace Soma.Holonics.R34\n\n") ||
      !triple_definitions(out, "held", triple) ||
      !out.text("def heldLower : List ℤ := ["))
    return false;
  for (std::uint8_t i = 0; i < 6; ++i) {
    if (i != 0 && !out.text(","))
      return false;
    if (!out.integer(s.lower[i]))
      return false;
  }
  if (!out.text("]\ndef heldAnchor : ℤ := ") || !out.integer(s.anchor) ||
      !out.text("\ndef heldCompanion : ℤ := ") || !out.integer(s.companion) ||
      !out.text("\ndef heldSourceCompanion : ℤ := ") ||
      !out.integer(s.source_companion) ||
      !out.text("\ndef heldQuadratic : List ℤ := [") ||
      !out.integer(s.quadratic[0]) || !out.text(",") ||
      !out.integer(s.quadratic[1]) || !out.text(",") ||
      !out.integer(s.quadratic[2]) ||
      !out.text("]\n\ntheorem heldoutTraceFiberTransport :\n  heldAB = "
                "matrixMultiply heldA heldB ∧ heldAC = matrixMultiply heldA heldC ∧\n  "
                "heldBC = matrixMultiply heldB heldC ∧ heldABC = matrixMultiply heldAB heldC ∧\n  "
                "heldACB = matrixMultiply heldAC heldB ∧ heldCompanion = "
                "heldSourceCompanion ∧\n  traceSumPolynomial ") ||
      !out.integer(s.lower[0]) || !out.text(" ") || !out.integer(s.lower[1]) ||
      !out.text(" ") || !out.integer(s.lower[2]) || !out.text(" ") ||
      !out.integer(s.lower[3]) || !out.text(" ") || !out.integer(s.lower[4]) ||
      !out.text(" ") || !out.integer(s.lower[5]) ||
      !out.text(" (heldAnchor+heldCompanion) = 0 ∧ traceProductPolynomial ") ||
      !out.integer(s.lower[0]) || !out.text(" ") || !out.integer(s.lower[1]) ||
      !out.text(" ") || !out.integer(s.lower[2]) || !out.text(" ") ||
      !out.integer(s.lower[3]) || !out.text(" ") || !out.integer(s.lower[4]) ||
      !out.text(" ") || !out.integer(s.lower[5]) ||
      !out.text(" (heldAnchor*heldCompanion) = 0 := by\n  have returned := "
                "discoveredTraceFiber "))
    return false;
  for (std::uint8_t m = 0; m < 3; ++m)
    for (std::uint8_t i = 0; i < 4; ++i)
      if (!out.integer(s.matrices[m].value[i]) || !out.text(" "))
        return false;
  return out.text(
      "(by norm_num) (by norm_num) (by norm_num)\n"
      "  constructor\n  · norm_num [heldA, heldB, heldAB, matrixMultiply]\n"
      "  constructor\n  · norm_num [heldA, heldC, heldAC, matrixMultiply]\n"
      "  constructor\n  · norm_num [heldB, heldC, heldBC, matrixMultiply]\n"
      "  constructor\n  · norm_num [heldAB, heldC, heldABC, matrixMultiply]\n"
      "  constructor\n  · norm_num [heldAC, heldB, heldACB, matrixMultiply]\n"
      "  constructor\n  · norm_num [heldCompanion, heldSourceCompanion]\n"
      "  constructor\n"
      "  · simpa [heldAnchor, heldCompanion, matrixMultiply, matrixTrace] using returned.1\n"
      "  · simpa [heldAnchor, heldCompanion, matrixMultiply, matrixTrace] using returned.2" ".1\n\n"
      "theorem generated_heldout_trace_fiber : heldCompanion = heldSourceCompanion := by\n"
      "  exact heldoutTraceFiberTransport.2" ".2" ".2" ".2" ".2" ".1\n\nend Soma.Holonics.R34\n\n"
      "#check Soma.Holonics.R34.generated_heldout_trace_fiber\n");
}

} // namespace holonics::codec
