#pragma once

#include <holonics/codec/hodge_realization_renderer_atoms.hpp>

namespace holonics::codec::hodge_render_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_hodge_bundle(
    const hodge_realization_surface& source, hodge_formal_face& out) noexcept {
  if (source.passage.value() == 0 || !source.factor_exact || !source.cup_exact ||
      !source.transport_exact || !source.locus_exact || !source.translations_exact ||
      !source.fibers_exact || !source.blowup_exact || !source.changed_sensitive ||
      !source.alternatives_retained) { return false; }
  out.identity = exact::word{128'900}; out.passage = source.passage;
  if (!append_blind(out.bytes, out.byte_count,
      "import Mathlib.Tactic.NormNum\nimport Mathlib.Tactic.Ring\n"
      "import Mathlib.Tactic.Linarith\n\nnamespace Soma.Holonics.R28\n\n"
      "def discriminantStatement : Prop := ") || !discriminant(out, source) ||
      !append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_discriminant : discriminantStatement := by\n"
      "  unfold discriminantStatement\n  intro z; ring\n\n"
      "def transportStatement : Prop :=\n  ") || !transport(out, source) ||
      !append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_transport : transportStatement := by\n"
      "  unfold transportStatement\n  norm_num\n\n"
      "def filtrationStatement : Prop := (") || !integer(out, source.rational_rank) ||
      !append_blind(out.bytes, out.byte_count, " : ℕ) = 6 ∧ (") ||
      !integer(out, source.f2_rank) || !append_blind(out.bytes, out.byte_count, " : ℕ) = 1 ∧ (") ||
      !integer(out, source.f1_rank) || !append_blind(out.bytes, out.byte_count, " : ℕ) = 5 ∧ (") ||
      !integer(out, source.h20) || !append_blind(out.bytes, out.byte_count, " : ℕ) = 1 ∧ (") ||
      !integer(out, source.h11) || !append_blind(out.bytes, out.byte_count, " : ℕ) = 4 ∧ (") ||
      !integer(out, source.h02) || !append_blind(out.bytes, out.byte_count, " : ℕ) = 1 ∧ (") ||
      !integer(out, source.connection_t[5][2]) ||
      !append_blind(out.bytes, out.byte_count, " : ℤ) = 0 ∧ (") ||
      !integer(out, source.connection_u[5][2]) ||
      !append_blind(out.bytes, out.byte_count, " : ℤ) = 0 ∧ (") ||
      !integer(out, source.common_denominator) ||
      !append_blind(out.bytes, out.byte_count,
      " : ℤ) ≠ 0\ntheorem generated_filtration : filtrationStatement := by\n"
      "  unfold filtrationStatement\n  norm_num\n\n"
      "def translationStatement : Prop :=\n"
      "  (∀ x z : ℤ, z^2*x*(x-1)*(x-z) = x*z*(z-x)*(z-z*x)) ∧\n"
      "  (∀ x z : ℤ, (1-z)^2*x*(x-1)*(x-z) = "
      "(x-1)*(x-z)*(1-z)*(x*(1-z))) ∧\n"
      "  (∀ x z : ℤ, (z*(z-1))^2*x*(x-1)*(x-z) = "
      "(x-z)*(z*(x-1))*(x*(z-1))*(z*(z-1))) ∧\n"
      "  (∀ x z : ℤ, 0*x-z*1 = -z) ∧\n"
      "  (∀ x z : ℤ, 1*(x-1)-(x-z)*1 = -(1-z)) ∧\n"
      "  (∀ x z : ℤ, z*(x-z)-z*(x-1) = -(z*(z-1)))\n"
      "theorem generated_translations : translationStatement := by\n"
      "  unfold translationStatement\n  constructor\n  · intro x z; ring\n"
      "  constructor\n  · intro x z; ring\n  constructor\n  · intro x z; ring\n"
      "  constructor\n  · intro x z; ring\n  constructor <;> intro x z <;> ring\n\n"
      "def locusStatement : Prop := (∀ dt du : ℤ, ") ||
      !integer(out, source.quotient_obstruction[0]) ||
      !append_blind(out.bytes, out.byte_count, "*dt + ") ||
      !integer(out, source.quotient_obstruction[1]) ||
      !append_blind(out.bytes, out.byte_count, "*du = 0 ↔ dt = du) ∧ (") ||
      !integer(out, source.tangent_obstruction) ||
      !append_blind(out.bytes, out.byte_count, " : ℤ) = 0 ∧ (") ||
      !integer(out, source.normal_obstruction) ||
      !append_blind(out.bytes, out.byte_count, " : ℤ) ≠ 0 ∧ (") ||
      !integer(out, source.multiplicity) ||
      !append_blind(out.bytes, out.byte_count, " : ℕ) = 1\n"
      "theorem generated_locus : locusStatement := by\n"
      "  unfold locusStatement\n  constructor\n  · intro dt du; constructor <;> intro h <;> linarith\n"
      "  norm_num\n\ndef intersectionStatement : Prop :=\n  ") ||
      !pairing(out, source.graph, source.cup, source.graph, source.graph_square) ||
      !append_blind(out.bytes, out.byte_count, " ∧\n  ") ||
      !pairing(out, source.graph, source.cup, source.negation, source.mutual_intersection) ||
      !append_blind(out.bytes, out.byte_count, " ∧\n  ") ||
      !pairing(out, source.primitive, source.cup, source.primitive, source.primitive_square) ||
      !append_blind(out.bytes, out.byte_count, " ∧\n  ") ||
      !pairing(out, source.polarization, source.cup, source.polarization, 2) ||
      !append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_intersections : intersectionStatement := by\n"
      "  unfold intersectionStatement\n  norm_num\n\n"
      "def graphClassStatement : Prop :=\n  ") || !graph_relations(out, source) ||
      !append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_graph_classes : graphClassStatement := by\n"
      "  unfold graphClassStatement\n  norm_num\n\n"
      "def fiberStatement : Prop := (") || !integer(out, source.enumerated) ||
      !append_blind(out.bytes, out.byte_count, " : ℕ) = 2187 ∧ (") ||
      !integer(out, source.integral_realizers) ||
      !append_blind(out.bytes, out.byte_count, " : ℕ) = 16 ∧ (") ||
      !integer(out, source.rational_realizers) ||
      !append_blind(out.bytes, out.byte_count, " : ℕ) = 16 ∧ (") ||
      !integer(out, source.effective_graphs) ||
      !append_blind(out.bytes, out.byte_count, " : ℕ) = 4 ∧ (") ||
      !integer(out, source.rational_integral_separated ? 1 : 0) ||
      !append_blind(out.bytes, out.byte_count, " : ℕ) = 1 ∧ (") ||
      !integer(out, source.outside_image ? 1 : 0) ||
      !append_blind(out.bytes, out.byte_count,
      " : ℕ) = 1 ∧ (∀ c0 c1 c2 c3 c4 c5 c6 : ℤ, "
      "0*c0+0*c1+0*c2+0*c3+0*c4+0*c5+0*c6 ≠ 1)\n"
      "theorem generated_fibers : fiberStatement := by\n"
      "  unfold fiberStatement\n  norm_num\n\n"
      "def blowupStatement : Prop := (") || !integer(out, source.blowup_rank) ||
      !append_blind(out.bytes, out.byte_count, " : ℕ) = 7 ∧ (") ||
      !integer(out, source.blowup_pairing[6][6]) ||
      !append_blind(out.bytes, out.byte_count, " : ℤ) = -1 ∧ (") ||
      !integer(out, source.selected_self_intersection) ||
      !append_blind(out.bytes, out.byte_count, " : ℤ) = -1 ∧ (") ||
      !integer(out, source.center) ||
      !append_blind(out.bytes, out.byte_count, " : ℕ) = 0 ∧ (") ||
      !integer(out, source.changed_center) ||
      !append_blind(out.bytes, out.byte_count, " : ℕ) = 1 ∧\n  ") ||
      !blowup_pairing(out, source.exceptional, source.blowup_pairing, source.exceptional, -1) ||
      !append_blind(out.bytes, out.byte_count, " ∧\n  ") ||
      !blowup_pairing(out, source.selected_strict, source.blowup_pairing,
          source.selected_strict, source.selected_self_intersection) ||
      !append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_blowup : blowupStatement := by\n"
      "  unfold blowupStatement\n  norm_num\n\n"
      "def blowupMapStatement : Prop :=\n  ") || !blowup_maps(out, source) ||
      !append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_blowup_maps : blowupMapStatement := by\n"
      "  unfold blowupMapStatement\n  norm_num\n\n"
      "theorem generated_hodge_realization : discriminantStatement ∧ transportStatement ∧ "
      "filtrationStatement ∧ translationStatement ∧ locusStatement ∧ intersectionStatement ∧ "
      "graphClassStatement ∧ fiberStatement ∧ blowupStatement ∧ blowupMapStatement := by\n"
      "  exact ⟨generated_discriminant, generated_transport, generated_filtration, "
      "generated_translations, generated_locus, generated_intersections, "
      "generated_graph_classes, generated_fibers, generated_blowup, generated_blowup_maps⟩\n\n"
      "end Soma.Holonics.R28\n\n"
      "#check Soma.Holonics.R28.generated_hodge_realization\n")) { return false; }
  return true;
}

}  // namespace holonics::codec::hodge_render_detail
