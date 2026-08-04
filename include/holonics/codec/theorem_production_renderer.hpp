#pragma once

#include <holonics/codec/generated_math_face.hpp>

namespace holonics::codec {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_composed_trace_theorem(
    const theorem_production_surface& surface, formal_math_face& output) noexcept {
  if (surface.passage.value() == 0 || surface.statement.value() == 0 ||
      surface.proof.value() == 0 || !surface.closed || !surface.generated ||
      surface.form != theorem_surface_form::composed_trace_rebase) { return false; }
  output.identity = exact::word{123'201};
  output.passage = surface.passage;
  return append_face(output.bytes, output.byte_count,
      "import ElementaryHolonics.Algorithm.Rebase\n\nnamespace Soma.Holonics\n\n") &&
      append_face(output.bytes, output.byte_count, "open SituatedAlgorithm\n\n") &&
      append_face(output.bytes, output.byte_count,
      "theorem generated_trace_rebase_transports_composition {Theta I S O S2 : Type*}\n") &&
      append_face(output.bytes, output.byte_count,
      "    (A : SituatedAlgorithm Theta I S O) (e : S ≃ S2)\n") &&
      append_face(output.bytes, output.byte_count,
      "    (theta : Theta) {s t u : S}\n") &&
      append_face(output.bytes, output.byte_count,
      "    (hst : Trace (A.step theta) s t)\n") &&
      append_face(output.bytes, output.byte_count,
      "    (htu : Trace (A.step theta) t u) :\n") &&
      append_face(output.bytes, output.byte_count,
      "    Trace ((A.rebase e).step theta) (e s) (e u) := by\n") &&
      append_face(output.bytes, output.byte_count, "  exact (") &&
      append_face(output.bytes, output.byte_count, "trace_rebase_iff A e theta s u") &&
      append_face(output.bytes, output.byte_count, ").2 (") &&
      append_face(output.bytes, output.byte_count, "Trace.trans hst htu") &&
      append_face(output.bytes, output.byte_count, ")\n\nend Soma.Holonics\n");
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_composed_trace_explanation(
    const theorem_production_surface& surface, conversational_math_face& output) noexcept {
  if (surface.passage.value() == 0 || !surface.closed || !surface.generated ||
      surface.form != theorem_surface_form::composed_trace_rebase) { return false; }
  output.identity = exact::word{123'202};
  output.passage = surface.passage;
  return append_face(output.bytes, output.byte_count,
      "The two given traces meet at the same intermediate state, so exact trace transitivity ") &&
      append_face(output.bytes, output.byte_count,
      "first forms one trace from s to u. The inherited rebase equivalence then transports that ") &&
      append_face(output.bytes, output.byte_count,
      "composite through e, yielding a rebased trace from e s to e u. The local receiver selected ") &&
      append_face(output.bytes, output.byte_count,
      "this three-dependency passage while retaining the four-dependency alternative as open.\n");
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_returned_fiber_theorem(
    const theorem_production_surface& surface, formal_math_face& output) noexcept {
  if (surface.passage.value() == 0 || surface.statement.value() == 0 ||
      surface.proof.value() == 0 || !surface.closed || !surface.generated ||
      surface.form != theorem_surface_form::returned_fiber_extension) { return false; }
  output.identity = exact::word{123'203};
  output.passage = surface.passage;
  return append_face(output.bytes, output.byte_count,
      "import ElementaryHolonics.Algorithm.Rebase\n") &&
      append_face(output.bytes, output.byte_count,
      "import R14_GENERATED_TRACE_COMPOSITION\n\nnamespace Soma.Holonics\n\n") &&
      append_face(output.bytes, output.byte_count, "open SituatedAlgorithm\n\n") &&
      append_face(output.bytes, output.byte_count,
      "theorem generated_trace_rebase_transports_three {Theta I S O S2 : Type*}\n") &&
      append_face(output.bytes, output.byte_count,
      "    (A : SituatedAlgorithm Theta I S O) (e : S ≃ S2)\n") &&
      append_face(output.bytes, output.byte_count,
      "    (theta : Theta) {s t u v : S}\n") &&
      append_face(output.bytes, output.byte_count,
      "    (hst : Trace (A.step theta) s t)\n") &&
      append_face(output.bytes, output.byte_count,
      "    (htu : Trace (A.step theta) t u)\n") &&
      append_face(output.bytes, output.byte_count,
      "    (huv : Trace (A.step theta) u v) :\n") &&
      append_face(output.bytes, output.byte_count,
      "    Trace ((A.rebase e).step theta) (e s) (e v) := by\n") &&
      append_face(output.bytes, output.byte_count,
      "  exact generated_trace_rebase_transports_composition A e theta\n") &&
      append_face(output.bytes, output.byte_count,
      "    (Trace.trans hst htu) huv\n\nend Soma.Holonics\n");
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_returned_fiber_explanation(
    const theorem_production_surface& surface, conversational_math_face& output) noexcept {
  if (surface.passage.value() == 0 || !surface.closed || !surface.generated ||
      surface.form != theorem_surface_form::returned_fiber_extension) { return false; }
  output.identity = exact::word{123'204};
  output.passage = surface.passage;
  return append_face(output.bytes, output.byte_count,
      "The returned first theorem is used as an inherited local proof fiber. Trace transitivity ") &&
      append_face(output.bytes, output.byte_count,
      "first joins hst and htu into a two-segment trace. The acquired theorem is then applied to ") &&
      append_face(output.bytes, output.byte_count,
      "that trace and huv; its composition/rebase law joins the third segment and transports the ") &&
      append_face(output.bytes, output.byte_count,
      "entire trace. Removing the returned fiber obstructs this selected passage exactly.\n");
}

}  // namespace holonics::codec
