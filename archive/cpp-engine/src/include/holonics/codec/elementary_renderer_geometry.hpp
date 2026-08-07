#pragma once

#include <holonics/codec/elementary_renderer_atoms.hpp>

namespace holonics::codec::elementary_render_detail {

template<class Writer>
HOLONICS_CALLABLE inline bool fin_vector(Writer &out, const std::int64_t *values) noexcept {
  if (!out.text("![")) return false;
  for (std::uint8_t i = 0; i < 6; ++i) {
    if (i != 0 && !out.text(",")) return false;
    if (!out.integer(values[i])) return false;
  }
  return out.text("]");
}

template<class Writer>
HOLONICS_CALLABLE inline bool render_receiver(Writer &out,
    const elementary_receiver_surface &surface) noexcept {
  if (!out.text(
      "abbrev FiberCompatible (q g : Fin 6 → ℤ) : Prop :=\n"
      "  ∀ i j, q i = q j → g i = g j\n\n"
      "abbrev Refines (fine coarse : Fin 6 → ℤ) : Prop :=\n"
      "  ∀ i j, fine i = fine j → coarse i = coarse j\n\n"
      "def coarseQuestion : Fin 6 → ℤ := ") || !fin_vector(out,surface.coarse) ||
      !out.text("\ndef fineQuestion : Fin 6 → ℤ := ") || !fin_vector(out,surface.fine) ||
      !out.text("\ndef firstConsequence : Fin 6 → ℤ := ") || !fin_vector(out,surface.first) ||
      !out.text("\ndef strictConsequence : Fin 6 → ℤ := ") || !fin_vector(out,surface.strict) ||
      !out.text("\n\nabbrev receiverStatement : Prop :=\n"
      "  FiberCompatible coarseQuestion firstConsequence ∧\n"
      "  ¬ FiberCompatible coarseQuestion strictConsequence ∧\n"
      "  FiberCompatible fineQuestion strictConsequence ∧\n"
      "  Refines fineQuestion coarseQuestion\n\n"
      "theorem receiverReturn : receiverStatement := by native_decide\n\n"
      "theorem coarseFactorization : FiberCompatible coarseQuestion firstConsequence := by\n"
      "  native_decide\n\n"
      "theorem strictQuestionReopensCoarseFiber :\n"
      "    ¬ FiberCompatible coarseQuestion strictConsequence := by\n"
      "  native_decide\n\n"
      "theorem refinedFactorization : FiberCompatible fineQuestion strictConsequence := by\n"
      "  native_decide\n\n"
      "theorem refinementPreservesCoarseQuestion : Refines fineQuestion coarseQuestion := by\n"
      "  native_decide\n\n"
      "theorem equalReceiverDoesNotIdentifySource :\n"
      "    coarseQuestion 0 = coarseQuestion 1 ∧ (0 : Fin 6) ≠ 1 := by\n"
      "  native_decide\n\n")) return false;
  return true;
}

template<class Writer>
HOLONICS_CALLABLE inline bool named_matrix(Writer &out, const char *name,
    const elementary_matrix2_surface &value) noexcept {
  return out.text("def ") && out.text(name) && out.text(" : ExactMatrix2 := ") &&
      matrix(out,value) && out.text("\n");
}

template<class Writer>
HOLONICS_CALLABLE inline bool render_chart(Writer &out,
    const elementary_chart_surface &surface) noexcept {
  if (!out.text(
      "structure ExactMatrix2 where\n"
      "  a : ℤ\n"
      "  b : ℤ\n"
      "  c : ℤ\n"
      "  d : ℤ\n"
      "  deriving DecidableEq, Repr\n\n"
      "def matrixMultiply (x y : ExactMatrix2) : ExactMatrix2 :=\n"
      "  {a := x.a*y.a+x.b*y.c, b := x.a*y.b+x.b*y.d,\n"
      "   c := x.c*y.a+x.d*y.c, d := x.c*y.b+x.d*y.d}\n\n"
      "def matrixSubtract (x y : ExactMatrix2) : ExactMatrix2 :=\n"
      "  {a := x.a-y.a, b := x.b-y.b, c := x.c-y.c, d := x.d-y.d}\n\n"
      "def matrixDeterminant (x : ExactMatrix2) : ℤ := x.a*x.d-x.b*x.c\n\n")) return false;
  if (!named_matrix(out,"chartA",surface.first) || !named_matrix(out,"chartB",surface.second) ||
      !named_matrix(out,"pathAB",surface.first_path) || !named_matrix(out,"pathBA",surface.second_path) ||
      !named_matrix(out,"pathResidual",surface.residual) || !named_matrix(out,"closedReturn",surface.closed))
    return false;
  return out.text("\nabbrev localChartStatement : Prop :=\n"
      "    matrixMultiply chartA chartB = pathAB ∧\n"
      "    matrixMultiply chartB chartA = pathBA ∧\n"
      "    matrixSubtract pathAB pathBA = pathResidual ∧\n"
      "    pathResidual ≠ {a := 0, b := 0, c := 0, d := 0} ∧\n"
      "    matrixDeterminant closedReturn = ") && out.integer(surface.determinant) &&
      out.text(" ∧ closedReturn.a + closedReturn.d = ") && out.integer(surface.trace) &&
      out.text("\n\ntheorem localChartTransport : localChartStatement := by\n  native_decide\n\n"
      "theorem curvedSquareCountermodel : pathAB ≠ pathBA := by native_decide\n\n");
}

template<class Writer>
HOLONICS_CALLABLE inline bool render_conduct_case(Writer &out, std::uint8_t index,
    const std::uint8_t *values) noexcept {
  constexpr const char *fields[7]{"returned","bodyDelta","detached","sourceAccess",
      "lossless","testimony","heldout"};
  if (!out.text("def conduct") || !out.natural(index) || !out.text(" : ConductObservation := {")) return false;
  for (std::uint8_t field = 0; field < 7; ++field) {
    if (field != 0 && !out.text(", ")) return false;
    if (!out.text(fields[field]) || !out.text(" := ") || !boolean(out,values[field] != 0)) return false;
  }
  return out.text("}\n");
}

template<class Writer>
HOLONICS_CALLABLE inline bool render_conduct(Writer &out,
    const elementary_conduct_surface &surface) noexcept {
  constexpr const char *fields[7]{"x.returned","x.bodyDelta","x.detached","x.sourceAccess",
      "x.lossless","x.testimony","x.heldout"};
  if (!out.text("structure ConductObservation where\n"
      "  returned : Bool\n"
      "  bodyDelta : Bool\n"
      "  detached : Bool\n"
      "  sourceAccess : Bool\n"
      "  lossless : Bool\n"
      "  testimony : Bool\n"
      "  heldout : Bool\n"
      "  deriving DecidableEq, Repr\n\n"
      "def foundedConduct (x : ConductObservation) : Bool := ")) return false;
  bool first = true;
  for (std::uint8_t field = 0; field < 7; ++field) {
    const auto condition = surface.conditions[field]; if (condition == 0) continue;
    if (!first && !out.text(" && ")) return false;
    first = false;
    if (condition == 1 && !out.text("!")) return false;
    if (!out.text(fields[field])) return false;
  }
  if (first && !out.text("true")) return false;
  if (!out.text("\n\n")) return false;
  for (std::uint8_t i = 0; i < 8; ++i)
    if (!render_conduct_case(out,i,surface.cases[i])) return false;
  if (!out.text("\nabbrev returnedConductStatement : Prop :=\n  ")) return false;
  for (std::uint8_t i = 0; i < 8; ++i) {
    if (i != 0 && !out.text(" ∧\n  ")) return false;
    if (!out.text("foundedConduct conduct") || !out.natural(i) || !out.text(" = ") ||
        !boolean(out,surface.cases[i][7] != 0)) return false;
  }
  return out.text("\n\ntheorem returnedConductCriterion : returnedConductStatement := by native_decide\n\n"
      "theorem lookupDoesNotFoundReusableConduct : foundedConduct conduct4 = false := by\n"
      "  native_decide\n\n");
}

template<class Writer>
HOLONICS_CALLABLE inline bool render_self_organ(Writer &out,
    const elementary_organ_surface &surface) noexcept {
  if (!out.text("def selfHolonomyKernel : List ℤ := ") ||
      !integer_list(out,surface.coefficients,3) ||
      !out.text("\n\ndef selfHolonomyTrace : List ℚ := [")) return false;
  for (std::uint8_t i = 0; i < surface.trace_count; ++i) {
    if (i != 0 && !out.text(",")) return false;
    if (!rational(out,surface.trace[i])) return false;
  }
  if (!out.text("]\n\ndef selfHolonomyRecurrenceStatement : Prop :=\n  ")) return false;
  for (std::uint8_t n = 0; n + 2U < surface.trace_count; ++n) {
    if (n != 0 && !out.text(" ∧\n  ")) return false;
    for (std::uint8_t shift = 0; shift < 3; ++shift) {
      if (shift != 0 && !out.text(" + ")) return false;
      if (!out.integer(surface.coefficients[shift]) || !out.text(" * ") ||
          !rational(out,surface.trace[n+shift])) return false;
    }
    if (!out.text(" = 0")) return false;
  }
  return out.text("\n\ntheorem selfHolonomyOrganReturn : selfHolonomyRecurrenceStatement := by\n"
      "  norm_num [selfHolonomyRecurrenceStatement]\n\n");
}

}  // namespace holonics::codec::elementary_render_detail
