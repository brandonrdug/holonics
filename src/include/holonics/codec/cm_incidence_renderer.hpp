#pragma once

#include <holonics/codec/cm_incidence_face.hpp>

namespace holonics::codec::cm_render_detail {

HOLONICS_CALLABLE constexpr bool element(cm_formal_face& out,
    const cm_element_surface& value) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "⟨")) { return false; }
  for (std::uint8_t slot = 0; slot < cm_degree_capacity; ++slot) {
    if (slot != 0 && !append_blind(out.bytes, out.byte_count, ",")) { return false; }
    if (!append_blind_integer(out.bytes, out.byte_count, value.coefficients[slot])) {
      return false;
    }
  }
  return append_blind(out.bytes, out.byte_count, "⟩");
}

HOLONICS_CALLABLE constexpr bool horner(cm_formal_face& out,
    const std::int64_t* coefficients, std::uint8_t degree) noexcept {
  for (std::uint8_t slot = 0; slot < degree; ++slot) {
    if (!append_blind(out.bytes, out.byte_count, "(")) { return false; }
  }
  if (!append_blind_integer(out.bytes, out.byte_count, coefficients[0])) { return false; }
  for (std::uint8_t slot = 1; slot <= degree; ++slot) {
    if (!append_blind(out.bytes, out.byte_count, " * X + ") ||
        !append_blind_integer(out.bytes, out.byte_count, coefficients[slot]) ||
        !append_blind(out.bytes, out.byte_count, ")")) { return false; }
  }
  return true;
}

HOLONICS_CALLABLE constexpr bool factorization(cm_formal_face& out,
    const cm_factor_surface* factors, std::uint8_t count) noexcept {
  for (std::uint8_t slot = 0; slot < count; ++slot) {
    if (slot != 0 && !append_blind(out.bytes, out.byte_count, " * ")) { return false; }
    if (!append_blind(out.bytes, out.byte_count, "((") ||
        !horner(out, factors[slot].coefficients, factors[slot].degree) ||
        !append_blind(out.bytes, out.byte_count, ") ^ ") ||
        !append_blind_integer(out.bytes, out.byte_count, factors[slot].multiplicity) ||
        !append_blind(out.bytes, out.byte_count, ")")) { return false; }
  }
  return true;
}

HOLONICS_CALLABLE constexpr bool definitions(const cm_incidence_surface& surface,
    cm_formal_face& out) noexcept {
  if (!append_blind(out.bytes, out.byte_count,
      "import Mathlib.Data.Finset.Prod\nimport Mathlib.Data.Fintype.Fin\n"
      "import Mathlib.Tactic.NormNum\n"
      "import Mathlib.Tactic.Ring\n\n"
      "namespace Soma.Holonics.R22\n\n"
      "structure CM4 where\n  a0 : ℤ\n  a1 : ℤ\n  a2 : ℤ\n  a3 : ℤ\n"
      "deriving DecidableEq\n\n"
      "def cmOne : CM4 := ⟨1,0,0,0⟩\n"
      "def cmConj (a : CM4) : CM4 := ⟨a.a0-a.a1,-a.a1,a.a3-a.a1,a.a2-a.a1⟩\n"
      "def cmMul (a b : CM4) : CM4 :=\n"
      "  let c0 := a.a0*b.a0\n"
      "  let c1 := a.a0*b.a1+a.a1*b.a0\n"
      "  let c2 := a.a0*b.a2+a.a1*b.a1+a.a2*b.a0\n"
      "  let c3 := a.a0*b.a3+a.a1*b.a2+a.a2*b.a1+a.a3*b.a0\n"
      "  let c4 := a.a1*b.a3+a.a2*b.a2+a.a3*b.a1\n"
      "  let c5 := a.a2*b.a3+a.a3*b.a2\n"
      "  let c6 := a.a3*b.a3\n"
      "  ⟨c0-c4+c5,c1-c4+c6,c2-c4,c3-c4⟩\n"
      "def cmSub (a b : CM4) : CM4 := ⟨a.a0-b.a0,a.a1-b.a1,a.a2-b.a2,a.a3-b.a3⟩\n"
      "def cmNorm (a : CM4) : CM4 := cmMul a (cmConj a)\n\n")) { return false; }
  for (std::uint8_t slot = 0; slot < cm_translation_capacity; ++slot) {
    if (!append_blind(out.bytes, out.byte_count, "def root") ||
        !append_blind_integer(out.bytes, out.byte_count, slot) ||
        !append_blind(out.bytes, out.byte_count, " : CM4 := ") ||
        !element(out, surface.translations[slot]) ||
        !append_blind(out.bytes, out.byte_count, "\n")) { return false; }
  }
  return append_blind(out.bytes, out.byte_count,
      "\ntheorem generated_norm_one_translations :\n"
      "    cmNorm root0 = cmOne ∧ cmNorm root1 = cmOne ∧ cmNorm root2 = cmOne ∧\n"
      "    cmNorm root3 = cmOne ∧ cmNorm root4 = cmOne := by native_decide\n\n"
      "def coeff (n shift : Nat) : ℤ := Int.ofNat ((n / (2^shift)) % 2)\n"
      "def point (n : Fin 16) : CM4 :=\n"
      "  ⟨coeff n.val 0,coeff n.val 1,coeff n.val 2,coeff n.val 3⟩\n"
      "def unitPair (i j : Fin 16) : Bool :=\n"
      "  decide (i.val < j.val) && decide (cmNorm (cmSub (point j) (point i)) = cmOne)\n"
      "def unitPairCount : Nat :=\n"
      "  (((Finset.univ : Finset (Fin 16)) ×ˢ (Finset.univ : Finset (Fin 16))).filter\n"
      "    (fun p : Fin 16 × Fin 16 => unitPair p.1 p.2 = true)).card\n\n"
      "theorem generated_bounded_embedding_injective :\n"
      "    ∀ i j : Fin 16, point i = point j → i = j := by native_decide\n\n");
}

HOLONICS_CALLABLE constexpr bool proof(const cm_incidence_surface& surface,
    cm_formal_face& out) noexcept {
  if (!definitions(surface, out) ||
      !append_blind(out.bytes, out.byte_count,
          "theorem generated_unit_pair_count : unitPairCount = ") ||
      !append_blind_integer(out.bytes, out.byte_count, surface.unit_pairs) ||
      !append_blind(out.bytes, out.byte_count, " := by native_decide\n\n"
          "def periodicChar (X : ℤ) : ℤ := ") ||
      !horner(out, surface.periodic_characteristic, 16) ||
      !append_blind(out.bytes, out.byte_count, "\ndef periodicFactor (X : ℤ) : ℤ := ") ||
      !factorization(out, surface.periodic_factors, surface.periodic_factor_count) ||
      !append_blind(out.bytes, out.byte_count, "\ndef windowChar (X : ℤ) : ℤ := ") ||
      !horner(out, surface.window_characteristic, 16) ||
      !append_blind(out.bytes, out.byte_count, "\ndef windowFactor (X : ℤ) : ℤ := ") ||
      !factorization(out, surface.window_factors, surface.window_factor_count) ||
      !append_blind(out.bytes, out.byte_count,
          "\n\ntheorem generated_cm_characteristic_transport (X : ℤ) :\n"
          "    periodicChar X = periodicFactor X ∧ windowChar X = windowFactor X := by\n"
          "  constructor <;>\n"
          "    simp only [periodicChar, periodicFactor, windowChar, windowFactor] <;> ring\n\n"
          "theorem generated_aperture_transport : (")) { return false; }
  return append_blind_integer(out.bytes, out.byte_count, surface.periodic_edges) &&
      append_blind(out.bytes, out.byte_count, " : ℤ) - ") &&
      append_blind_integer(out.bytes, out.byte_count, surface.lost_edges) &&
      append_blind(out.bytes, out.byte_count, " = ") &&
      append_blind_integer(out.bytes, out.byte_count, surface.window_edges) &&
      append_blind(out.bytes, out.byte_count, " ∧ (") &&
      append_blind_integer(out.bytes, out.byte_count, surface.projection_loss) &&
      append_blind(out.bytes, out.byte_count,
          " : ℤ) = 0 := by norm_num\n\nend Soma.Holonics.R22\n\n"
          "#check Soma.Holonics.R22.generated_cm_characteristic_transport\n");
}

}  // namespace holonics::codec::cm_render_detail

namespace holonics::codec {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_cm_incidence(
    const cm_incidence_surface& surface, cm_formal_face& out) noexcept {
  if (surface.passage.value() == 0 || !surface.norm_one ||
      !surface.incidence_agreement || !surface.characteristic_transport ||
      !surface.aperture_scattering || !surface.alternatives_retained ||
      surface.periodic_factor_count == 0 || surface.window_factor_count == 0) { return false; }
  out.identity = exact::word{126'600};
  out.passage = surface.passage;
  return cm_render_detail::proof(surface, out);
}

}  // namespace holonics::codec
