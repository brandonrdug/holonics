#pragma once

namespace holonics::codec::expression_geometry_render_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_bundle(
    const expression_geometry_surface& source, expression_geometry_formal_face& out) noexcept {
  if (source.passage.value() == 0 || !source.ideals_exact || !source.differential_exact ||
      !source.residue_exact || !source.fibers_exact || !source.changed_sensitive ||
      !source.alternatives_retained) { return false; }
  out.identity = exact::word{128'800}; out.passage = source.passage;
  if (!append_blind(out.bytes, out.byte_count,
      "import Mathlib.Data.Complex.Basic\nimport Mathlib.Tactic.NormNum\n"
      "import Mathlib.Tactic.Ring\nimport Mathlib.Tactic.Linarith\n\n"
      "namespace Soma.Holonics.R27\n\ndef chartStatement : Prop := "
      "(∀ t u v : ℤ, v^2 - (u + (") || !integer(out, source.rational_shift) ||
      !append_blind(out.bytes, out.byte_count, "))^5 + t*(u + (") ||
      !integer(out, source.rational_shift) ||
      !append_blind(out.bytes, out.byte_count, ")) - (") ||
      !integer(out, source.family_constant) ||
      !append_blind(out.bytes, out.byte_count, ") = ") || !translated_polynomial(out, source) ||
      !append_blind(out.bytes, out.byte_count,
      ")\ntheorem generated_chart : chartStatement := by\n  unfold chartStatement\n  intro t u v; ring\n\n"
      "def gaussianChartStatement : Prop := "
      "(∀ t u v : ℂ, (Complex.I*v)^2 - (-u)^5 + t*(-u) - 1 = "
      "-(v^2-u^5+t*u+1))\ntheorem generated_gaussian_chart : gaussianChartStatement := by\n"
      "  unfold gaussianChartStatement\n  intro t u v; rw [mul_pow, Complex.I_sq]; ring\n\n"
      "def jacobianStatement : Prop := (∀ t x : ℤ, x*(t-5*x^4)+(x^5-t*x+") ||
      !integer(out, source.family_constant) ||
      !append_blind(out.bytes, out.byte_count, ") = ") ||
      !integer(out, source.family_constant) ||
      !append_blind(out.bytes, out.byte_count,
      "-4*x^5)\ntheorem generated_jacobian : jacobianStatement := by\n"
      "  unfold jacobianStatement\n  intro t x; ring\n\ndef bezoutStatement : Prop := ") ||
      !bezout(out, source) ||
      !append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_bezout : bezoutStatement := by\n"
      "  unfold bezoutStatement\n  intro t x; ring\n\n")) { return false; }
  for (std::uint8_t basis = 0; basis < 4; ++basis) {
    if (!append_blind(out.bytes, out.byte_count, "def reductionStatement_") ||
        !integer(out, basis) || !append_blind(out.bytes, out.byte_count, " : Prop := ") ||
        !reduction(out, source, basis) ||
        !append_blind(out.bytes, out.byte_count, "\ntheorem generated_reduction_") ||
        !integer(out, basis) || !append_blind(out.bytes, out.byte_count, " : reductionStatement_") ||
        !integer(out, basis) || !append_blind(out.bytes, out.byte_count,
        " := by\n  unfold reductionStatement_") || !integer(out, basis) ||
        !append_blind(out.bytes, out.byte_count, "\n  intro t x; ring\n\n")) { return false; }
  }
  if (!append_blind(out.bytes, out.byte_count, "def scalarStatement : Prop := ") ||
      !scalar(out, source) || !append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_scalar : scalarStatement := by\n  unfold scalarStatement\n"
      "  intro t z0 z1 z2 z3 z4; ring\n\n")) { return false; }
  for (std::uint8_t front = 0; front < 4; ++front) {
    if (!append_blind(out.bytes, out.byte_count, "def recurrenceStatement_") ||
        !integer(out, front) || !append_blind(out.bytes, out.byte_count, " : Prop := ") ||
        !recurrence(out, source, front) ||
        !append_blind(out.bytes, out.byte_count, "\ntheorem generated_recurrence_") ||
        !integer(out, front) || !append_blind(out.bytes, out.byte_count, " : recurrenceStatement_") ||
        !integer(out, front) || !append_blind(out.bytes, out.byte_count,
        " := by\n  unfold recurrenceStatement_") || !integer(out, front) ||
        !append_blind(out.bytes, out.byte_count, "\n  norm_num\n\n")) { return false; }
  }
  if (!append_blind(out.bytes, out.byte_count, "def finiteIndicialStatement : Prop := ") ||
      !indicial(out, source.finite_indicial, false) ||
      !append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_finite_indicial : finiteIndicialStatement := by\n"
      "  unfold finiteIndicialStatement\n  intro r; ring\n\ndef infinityIndicialStatement : Prop := ") ||
      !indicial(out, source.infinity_indicial, true) ||
      !append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_infinity_indicial : infinityIndicialStatement := by\n"
      "  unfold infinityIndicialStatement\n  intro r; ring\n\ndef residueStatement : Prop := ") ||
      !residue(out, source) ||
      !append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_residue_witness : residueStatement := by\n"
      "  unfold residueStatement\n  intro a h; constructor\n  · norm_num\n  · nlinarith [h]\n\n"
      "def separationStatement : Prop := ((") ||
      !integer(out, static_cast<std::int64_t>(source.fiber_members[0].value())) ||
      !append_blind(out.bytes, out.byte_count, " : ℕ) ≠ ") ||
      !integer(out, static_cast<std::int64_t>(source.fiber_members[1].value())) ||
      !append_blind(out.bytes, out.byte_count, " ∧ (") ||
      !integer(out, source.resultant[0]) || !append_blind(out.bytes, out.byte_count, " : ℤ) ≠ ") ||
      !integer(out, source.changed_resultant[0]) ||
      !append_blind(out.bytes, out.byte_count, " ∧ ") || !rational(out, source.series[0][5]) ||
      !append_blind(out.bytes, out.byte_count, " ≠ ") || !rational(out, source.changed_series) ||
      !append_blind(out.bytes, out.byte_count,
      ")\ntheorem generated_separation : separationStatement := by\n"
      "  unfold separationStatement\n  norm_num\n\n"
      "theorem generated_expression_geometry : chartStatement ∧ gaussianChartStatement ∧ "
      "jacobianStatement ∧ bezoutStatement ∧ reductionStatement_0 ∧ reductionStatement_1 ∧ "
      "reductionStatement_2 ∧ reductionStatement_3 ∧ scalarStatement ∧ recurrenceStatement_0 ∧ "
      "recurrenceStatement_1 ∧ recurrenceStatement_2 ∧ recurrenceStatement_3 ∧ "
      "finiteIndicialStatement ∧ infinityIndicialStatement ∧ residueStatement ∧ "
      "separationStatement := by\n"
      "  exact ⟨generated_chart, generated_gaussian_chart, generated_jacobian, generated_bezout, "
      "generated_reduction_0, generated_reduction_1, generated_reduction_2, "
      "generated_reduction_3, generated_scalar, generated_recurrence_0, generated_recurrence_1, "
      "generated_recurrence_2, generated_recurrence_3, generated_finite_indicial, "
      "generated_infinity_indicial, generated_residue_witness, generated_separation⟩\n\n"
      "end Soma.Holonics.R27\n\n#check Soma.Holonics.R27.generated_expression_geometry\n")) {
    return false;
  }
  return true;
}

}  // namespace holonics::codec::expression_geometry_render_detail
