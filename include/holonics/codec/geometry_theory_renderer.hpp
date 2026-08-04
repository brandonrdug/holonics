#pragma once

#include <holonics/codec/geometry_theory_face.hpp>

namespace holonics::codec {
namespace geometry_render_detail {

HOLONICS_CALLABLE constexpr bool prelude(geometry_theory_face& out) noexcept {
  return append_geometry_face(out.bytes, out.byte_count,
      "import Mathlib.Algebra.Field.Basic\nimport Mathlib.Tactic.FieldSimp\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "import Mathlib.Tactic.Ring\nimport Mathlib.Tactic.NormNum\n\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "namespace Soma.Holonics.R17\n\nstructure RatioPresentation (K : Type*) where\n") &&
      append_geometry_face(out.bytes, out.byte_count, "  num : K\n  den : K\n\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "@[ext] theorem RatioPresentation.ext {K : Type*} {p q : RatioPresentation K}\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "    (hnum : p.num = q.num) (hden : p.den = q.den) : p = q := by\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "  cases p\n  cases q\n  simp_all\n\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "def RatioPresentation.scale {K : Type*} [Mul K] (u : K) ") &&
      append_geometry_face(out.bytes, out.byte_count,
      "(p : RatioPresentation K) : RatioPresentation K :=\n  ⟨u * p.num, u * p.den⟩\n\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "def RatioPresentation.ProjectivelyEq {K : Type*} [Mul K] ") &&
      append_geometry_face(out.bytes, out.byte_count,
      "(p q : RatioPresentation K) : Prop := p.num * q.den = q.num * p.den\n\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "def swingPair {K : Type*} [Ring K] (a b c d : K) : RatioPresentation K :=\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "  ⟨(c-a)*(d-b), (c-b)*(d-a)⟩\n\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "def crossRatio {K : Type*} [Field K] (a b c d : K) : K :=\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "  (swingPair a b c d).num / (swingPair a b c d).den\n\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "def mobius {K : Type*} [Field K] (al be ga de x : K) : K :=\n") &&
      append_geometry_face(out.bytes, out.byte_count, "  (al*x+be)/(ga*x+de)\n\n");
}

HOLONICS_CALLABLE constexpr bool auxiliary(geometry_theory_face& out) noexcept {
  return append_geometry_face(out.bytes, out.byte_count,
      "theorem generated_mobius_sub {K : Type*} [Field K]\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "    (al be ga de x y : K) (hx : ga*x+de ≠ 0) (hy : ga*y+de ≠ 0) :\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "    mobius al be ga de x - mobius al be ga de y =\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "      (al*de-be*ga)*(x-y)/((ga*x+de)*(ga*y+de)) := by\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "  simp only [mobius]\n  rw [div_sub_div _ _ hx hy]\n  congr 1\n  ring\n\n");
}

HOLONICS_CALLABLE constexpr bool affine(geometry_theory_face& out) noexcept {
  return append_geometry_face(out.bytes, out.byte_count,
      "theorem generated_swing_affine_commRing {K : Type*} [CommRing K]\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "    (a b c d u v : K) :\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "    swingPair (u*a+v) (u*b+v) (u*c+v) (u*d+v) =\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "      (swingPair a b c d).scale (u*u) := by\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "  apply RatioPresentation.ext <;> simp [swingPair, RatioPresentation.scale] <;> ring\n\n");
}

HOLONICS_CALLABLE constexpr bool fractional(geometry_theory_face& out) noexcept {
  return append_geometry_face(out.bytes, out.byte_count,
      "theorem generated_crossRatio_mobius {K : Type*} [Field K]\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "    (a b c d al be ga de : K) (hdet : al*de-be*ga ≠ 0)\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "    (ha : ga*a+de ≠ 0) (hb : ga*b+de ≠ 0)\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "    (hc : ga*c+de ≠ 0) (hd : ga*d+de ≠ 0)\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "    (hcb : c-b ≠ 0) (hda : d-a ≠ 0) :\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "    crossRatio (mobius al be ga de a) (mobius al be ga de b)\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "      (mobius al be ga de c) (mobius al be ga de d) = crossRatio a b c d := by\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "  simp only [crossRatio, swingPair]\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "  rw [generated_mobius_sub al be ga de c a hc ha,\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "    generated_mobius_sub al be ga de d b hd hb,\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "    generated_mobius_sub al be ga de c b hc hb,\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "    generated_mobius_sub al be ga de d a hd ha]\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "  field_simp [hdet, ha, hb, hc, hd, hcb, hda]\n\n");
}

HOLONICS_CALLABLE constexpr bool counterexample(geometry_theory_face& out) noexcept {
  return append_geometry_face(out.bytes, out.byte_count,
      "theorem generated_coordinate_counterexample :\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "    swingPair (5:ℚ) 7 9 11 ≠ swingPair 0 1 2 3 ∧\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "      (swingPair (5:ℚ) 7 9 11).ProjectivelyEq (swingPair 0 1 2 3) := by\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "  norm_num [swingPair, RatioPresentation.ProjectivelyEq]\n\n") &&
      append_geometry_face(out.bytes, out.byte_count,
      "end Soma.Holonics.R17\n\n#check Soma.Holonics.R17.generated_crossRatio_mobius\n");
}

}  // namespace geometry_render_detail

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_geometry_theory(
    const geometry_theory_surface& plan, geometry_theory_face& output) noexcept {
  if (plan.passage.value() == 0 || !plan.difference_factor || !plan.affine_common_square ||
      !plan.fractional_invariance || !plan.coordinate_counterexample ||
      !plan.singular_boundary) { return false; }
  output.identity = exact::word{123'300};
  output.passage = plan.passage;
  return geometry_render_detail::prelude(output) && geometry_render_detail::auxiliary(output) &&
      geometry_render_detail::affine(output) && geometry_render_detail::fractional(output) &&
      geometry_render_detail::counterexample(output);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_geometry_explanation(
    const geometry_theory_surface& plan, geometry_theory_explanation& output) noexcept {
  if (plan.passage.value() == 0 || !plan.fractional_invariance) { return false; }
  output.identity = exact::word{123'301};
  output.passage = plan.passage;
  return append_geometry_face(output.bytes, output.byte_count,
      "The inquiry did not receive a target theorem or a known-answer label. Exact local probes ") &&
      append_geometry_face(output.bytes, output.byte_count,
      "refuted raw coordinate equality while preserving the four-point projective relation. ") &&
      append_geometry_face(output.bytes, output.byte_count,
      "Symbolic expansion found that a fractional-linear difference carries the determinant ") &&
      append_geometry_face(output.bytes, output.byte_count,
      "times the original difference over two chart denominators. Across the complete Swing, ") &&
      append_geometry_face(output.bytes, output.byte_count,
      "the numerator and denominator each carry two determinant factors and one denominator for ") &&
      append_geometry_face(output.bytes, output.byte_count,
      "every point, so those factors cancel only after all four points are composed. Affine ") &&
      append_geometry_face(output.bytes, output.byte_count,
      "transport remains as the denominator-free common-square chart. A zero determinant or a ") &&
      append_geometry_face(output.bytes, output.byte_count,
      "zero chart denominator leaves the quotient receiver obstructed rather than totalized.\n");
}

}  // namespace holonics::codec
