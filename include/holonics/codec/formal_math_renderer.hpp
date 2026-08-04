#pragma once

#include <holonics/codec/generated_math_face.hpp>

namespace holonics::codec {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_formal_math_face(
    const generated_math_surface& surface, formal_math_face& output) noexcept {
  if (surface.passage.value() == 0 || surface.statement.value() == 0 ||
      surface.proof.value() == 0 || surface.premise_declaration.value() == 0 ||
      surface.statement_form != 1 || surface.proof_form != 1) {
    return false;
  }
  output.identity = exact::word{123'001};
  output.passage = surface.passage;
  return append_face(output.bytes, output.byte_count,
      "import ElementaryHolonics.Algorithm.Rebase\n\n") &&
      append_face(output.bytes, output.byte_count,
      "namespace Soma.Holonics\n\nopen SituatedAlgorithm\n\n") &&
      append_face(output.bytes, output.byte_count,
      "theorem generated_semantics_rebase_reverse {Theta I S O S2 : Type*}\n") &&
      append_face(output.bytes, output.byte_count,
      "    (A : SituatedAlgorithm Theta I S O) (e : S ≃ S2)\n") &&
      append_face(output.bytes, output.byte_count,
      "    (theta : Theta) (input : I) (output : O) :\n") &&
      append_face(output.bytes, output.byte_count,
      "    A.Semantics theta input output ↔\n") &&
      append_face(output.bytes, output.byte_count,
      "      (A.rebase e).Semantics theta input output := by\n") &&
      append_face(output.bytes, output.byte_count,
      "  exact (semantics_rebase_iff A e theta input output).symm\n\n") &&
      append_face(output.bytes, output.byte_count, "end Soma.Holonics\n");
}

}  // namespace holonics::codec
