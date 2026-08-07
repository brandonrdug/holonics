#pragma once

#include <holonics/codec/cultivated_organ_face.hpp>
#include <holonics/codec/cultivation_renderer_atoms.hpp>

namespace holonics::codec {

HOLONICS_CALLABLE inline bool render_tail_statement(
    rederivation_render_detail::writer<cultivated_formal_face> &out,
    const cultivated_tail_surface &tail,
    const cultivated_kernel_surface &organ, std::int64_t offset) noexcept {
  using cultivation_render_detail::rational;
  for (std::uint8_t i = tail.prefix_count; i < tail.sample_count; ++i) {
    if (i != tail.prefix_count && !out.text(" ∧\n  ")) return false;
    if (!rational(out, tail.predicted[i]) || !out.text(" = ") ||
        !rational(out, tail.source[i]) || !out.text(" ∧ (") ) return false;
    const auto n = offset + i - organ.order;
    bool first = true;
    for (std::uint8_t shift = 0; shift <= organ.order; ++shift) {
      std::int64_t coefficient = 0;
      for (std::uint8_t p = 0; p <= organ.degree; ++p) {
        std::int64_t factor = 1;
        for (std::uint8_t k = 0; k < p; ++k) factor *= n;
        coefficient += organ.coefficients[shift * (organ.degree + 1U) + p] * factor;
      }
      if (!first && !out.text(" + ")) return false;
      first = false;
      if (!out.integer(coefficient) || !out.text(" * ") ||
          !rational(out, tail.predicted[i - organ.order + shift])) return false;
    }
    if (!out.text(" = 0)")) return false;
  }
  return true;
}

HOLONICS_CALLABLE inline bool render_cultivated_application(
    const cultivated_application_surface &receipt,
    cultivated_formal_face &face) noexcept {
  using rederivation_render_detail::writer;
  writer out{face}; face.identity = exact::word{198'411}; face.passage = receipt.passage;
  if (!receipt.exact || !out.text(
      "import Mathlib.Tactic.NormNum\n\nnamespace Soma.Holonics.R31\n\n"
      "def starUnitConductance : ℤ := 1\n"
      "def squareSteps : List (ℤ × ℤ) := [(1,0),(-1,0),(0,1),(0,-1)]\n"
      "def signedCarrierMatrix : List ℤ := [1,-2,2,1]\n"
      "def gradedGeneratorCount : ℕ := 2\n\n")) return false;
  constexpr const char *names[4]{"conductanceStar", "squareWalk", "signedCarrier", "gradedIncidence"};
  constexpr std::int64_t offsets[4]{1,0,0,0};
  for (std::uint8_t family = 0; family < cultivated_surface_family_count; ++family) {
    if (!out.text("def ") || !out.text(names[family]) || !out.text("Statement : Prop :=\n  ") ||
        !render_tail_statement(out, receipt.tails[family], receipt.kernels[family], offsets[family]) ||
        !out.text("\n\ntheorem ") ||
        !out.text(names[family]) || !out.text("Return : ") || !out.text(names[family]) ||
        !out.text("Statement := by\n  unfold ") || !out.text(names[family]) ||
        !out.text("Statement\n  norm_num\n\n")) return false;
  }
  return out.text(
      "theorem generated_cultivated_organs_transport :\n"
      "    conductanceStarStatement ∧ squareWalkStatement ∧\n"
      "    signedCarrierStatement ∧ gradedIncidenceStatement := by\n"
      "  exact ⟨conductanceStarReturn, squareWalkReturn, signedCarrierReturn, "
      "gradedIncidenceReturn⟩\n\nend Soma.Holonics.R31\n\n"
      "#check Soma.Holonics.R31.generated_cultivated_organs_transport\n");
}

}  // namespace holonics::codec
