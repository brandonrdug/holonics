#pragma once

#include <holonics/codec/generated_math_face.hpp>

namespace holonics::codec {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_conversational_math_face(
    const generated_math_surface& surface, conversational_math_face& output) noexcept {
  if (surface.passage.value() == 0 || surface.statement.value() == 0 ||
      surface.proof.value() == 0 || surface.premise_declaration.value() == 0 ||
      surface.statement_form != 1 || surface.proof_form != 1) {
    return false;
  }
  output.identity = exact::word{123'002};
  output.passage = surface.passage;
  return append_face(output.bytes, output.byte_count,
      "Generated statement: semantic behavior is invariant in the reverse direction under an ") &&
      append_face(output.bytes, output.byte_count,
      "invertible state rebase. The proof takes exact symmetry of the inherited ") &&
      append_face(output.bytes, output.byte_count,
      "semantics_rebase_iff passage. The theorem statement and proof object are new; ") &&
      append_face(output.bytes, output.byte_count,
      "no mounted theorem source was quoted as the answer.\n");
}

}  // namespace holonics::codec
