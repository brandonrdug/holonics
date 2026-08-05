#pragma once

#include <holonics/codec/characteristic_hypergeometry_renderer.hpp>

namespace holonics::codec {

HOLONICS_CALLABLE inline bool
render_heldout_characteristic(const heldout_characteristic_surface &s,
                              characteristic_formal_face &face) noexcept {
  using rederivation_render_detail::writer;
  writer out{face};
  face.identity = exact::word{200'411};
  face.passage = s.passage;
  if (!s.exact || !s.prediction_before_comparison || !s.source_detached ||
      !out.text("import R33_CHARACTERISTIC_HYPERGEOMETRY\n\nnamespace "
                "Soma.Holonics.R33\n\n"
                "def heldoutVisible : ℤ × ℤ × ℤ := (") ||
      !out.integer(s.visible[0]) || !out.text(",") ||
      !out.integer(s.visible[1]) || !out.text(",") ||
      !out.integer(s.visible[2]) ||
      !out.text(")\ndef heldoutPredictedTrace : ℤ := ") ||
      !out.integer(s.predicted_trace) ||
      !out.text("\ndef heldoutSourceTrace : ℤ := ") ||
      !out.integer(s.source_trace) ||
      !out.text("\ndef heldoutCharacteristic : List ℤ := [") ||
      !out.integer(s.characteristic[0]) || !out.text(",") ||
      !out.integer(s.characteristic[1]) || !out.text(",") ||
      !out.integer(s.characteristic[2]) ||
      !out.text("]\n\ntheorem heldoutCharacteristicTransport :\n  "
                "tracePolynomial ") ||
      !out.integer(s.visible[0]) || !out.text(" ") ||
      !out.integer(s.visible[1]) || !out.text(" ") ||
      !out.integer(s.visible[2]) ||
      !out.text(" heldoutPredictedTrace = 0 ∧ heldoutPredictedTrace = "
                "heldoutSourceTrace ∧\n  heldoutCharacteristic = "
                "[1,-heldoutPredictedTrace,1] := by\n"
                "  have returned := discoveredCharacteristicTransport 2 1 1 1 "
                "2 1 (-1) 0 (by norm_num) (by norm_num)\n"
                "  norm_num [heldoutPredictedTrace, heldoutSourceTrace, "
                "heldoutCharacteristic, tracePolynomial] at returned ⊢\n\n"
                "theorem generated_heldout_characteristic_transport :\n  "
                "tracePolynomial ") ||
      !out.integer(s.visible[0]) || !out.text(" ") ||
      !out.integer(s.visible[1]) || !out.text(" ") ||
      !out.integer(s.visible[2]) ||
      !out.text(
          " heldoutPredictedTrace = 0 := by exact "
          "heldoutCharacteristicTransport.1\n\n"
          "end Soma.Holonics.R33\n\n#check "
          "Soma.Holonics.R33.generated_heldout_characteristic_transport\n"))
    return false;
  return true;
}

} // namespace holonics::codec
