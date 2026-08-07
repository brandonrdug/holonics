#pragma once

#include <holonics/codec/arithmetic_spectral_renderer_relations.hpp>

namespace holonics::codec::arithmetic_render_detail {

[[nodiscard]] HOLONICS_CALLABLE inline bool render_arithmetic_bundle(
    const arithmetic_spectral_surface& source, arithmetic_formal_face& out) noexcept {
  if (source.passage.value() == 0 || !source.fields_exact || !source.correspondences_exact ||
      !source.forms_exact || !source.traces_exact || !source.controls_exact ||
      !source.archimedean_inapplicable || !source.alternatives_retained) { return false; }
  out.identity = exact::word{129'000}; out.passage = source.passage;
  if (!append_blind(out.bytes, out.byte_count,
      "import Mathlib.Tactic.NormNum\nimport Mathlib.Tactic.Ring\n"
      "import Mathlib.Tactic.Positivity\nimport Mathlib.Data.ZMod.Basic\n\n"
      "namespace Soma.Holonics.R29\n\n"
      "def primaryEigenvectorRelation (a b : ℤ) : Prop :=\n"
      "  (a*1 + (-b)*0 = a) ∧ (a*0 + (-b)*(-1) = b) ∧\n"
      "  (b*1 + a*0 = b) ∧ (b*0 + a*(-1) = -a) ∧\n"
      "  (a*1 + (-b)*0 = a) ∧ (a*0 + (-b)*1 = -b) ∧\n"
      "  (b*1 + a*0 = b) ∧ (b*0 + a*1 = a)\n\n"
      "def smoothnessStatement : Prop :=\n  ") || !smoothness_atoms(out, source) ||
      !append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_smoothness : smoothnessStatement := by\n"
      "  unfold smoothnessStatement\n  native_decide\n\n"
      "def carrierStatement : Prop :=\n  ") || !carrier_atoms(out, source) ||
      !append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_carriers : carrierStatement := by\n"
      "  unfold carrierStatement\n  repeat' apply And.intro\n"
      "  all_goals intros\n  all_goals ring\n\n"
      "def traceStatement : Prop :=\n  ") || !trace_atoms(out, source) ||
      !append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_traces : traceStatement := by\n"
      "  unfold traceStatement\n  norm_num\n\n"
      "def recurrenceCountStatement : Prop :=\n  ") || !recurrence_atoms(out, source) ||
      !append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_recurrence_counts : recurrenceCountStatement := by\n"
      "  unfold recurrenceCountStatement\n  native_decide\n\n"
      "def zetaDualityStatement : Prop :=\n  ") || !duality_atoms(out, source) ||
      !append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_zeta_duality : zetaDualityStatement := by\n"
      "  unfold zetaDualityStatement\n  repeat' apply And.intro\n"
      "  all_goals intros\n  all_goals ring\n\n"
      "def eulerCoefficientStatement : Prop :=\n  ") || !euler_atoms(out, source) ||
      !append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_euler_coefficients : eulerCoefficientStatement := by\n"
      "  unfold eulerCoefficientStatement\n  native_decide\n\n"
      "def primaryEigenvectorStatement : Prop :=\n  ") || !primary_atoms(out, source) ||
      !append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_primary_eigenvectors : primaryEigenvectorStatement := by\n"
      "  unfold primaryEigenvectorStatement primaryEigenvectorRelation\n"
      "  repeat' apply And.intro\n  all_goals ring\n\n"
      "def explicitFormulaStatement : Prop :=\n  ") || !explicit_atoms(out, source) ||
      !append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_explicit_formula : explicitFormulaStatement := by\n"
      "  unfold explicitFormulaStatement\n  norm_num\n\n"
      "def positiveCurrentStatement : Prop :=\n  ") || !positivity_atoms(out, source) ||
      !append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_positive_currents : positiveCurrentStatement := by\n"
      "  unfold positiveCurrentStatement\n  repeat' apply And.intro\n"
      "  all_goals intros\n  all_goals positivity\n\n"
      "def controlStatement : Prop :=\n  ") || !control_atoms(out, source) ||
      !append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_controls : controlStatement := by\n"
      "  unfold controlStatement\n  native_decide\n\n"
      "theorem generated_arithmetic_spectral_placement : smoothnessStatement ∧ carrierStatement ∧ "
      "traceStatement ∧ recurrenceCountStatement ∧ zetaDualityStatement ∧ eulerCoefficientStatement ∧ "
      "primaryEigenvectorStatement ∧ explicitFormulaStatement ∧ positiveCurrentStatement ∧ "
      "controlStatement := by\n"
      "  exact ⟨generated_smoothness, generated_carriers, generated_traces, "
      "generated_recurrence_counts, generated_zeta_duality, generated_euler_coefficients, "
      "generated_primary_eigenvectors, generated_explicit_formula, generated_positive_currents, "
      "generated_controls⟩\n\n"
      "end Soma.Holonics.R29\n\n"
      "#check Soma.Holonics.R29.generated_arithmetic_spectral_placement\n")) { return false; }
  return true;
}

}  // namespace holonics::codec::arithmetic_render_detail
