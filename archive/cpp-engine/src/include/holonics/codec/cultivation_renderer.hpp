#pragma once

#include <holonics/codec/cultivated_organ_face.hpp>
#include <holonics/codec/cultivation_renderer_atoms.hpp>

namespace holonics::codec {

HOLONICS_CALLABLE inline bool render_cultivation_residual(
    rederivation_render_detail::writer<cultivated_formal_face> &out,
    const cultivated_kernel_surface &organ, std::uint8_t series,
    std::uint8_t n) noexcept {
  using cultivation_render_detail::rational;
  if (!out.text("(")) return false;
  bool first = true;
  for (std::uint8_t shift = 0; shift <= organ.order; ++shift) {
    for (std::uint8_t p = 0; p <= organ.degree; ++p) {
      const auto coefficient = organ.coefficients[shift * (organ.degree + 1U) + p];
      std::int64_t factor = 1;
      for (std::uint8_t k = 0; k < p; ++k) factor *= n;
      if (!first && !out.text(" + ")) return false;
      first = false;
      if (!out.integer(coefficient * factor) || !out.text(" * ") ||
          !rational(out, organ.samples[series][n + shift])) return false;
    }
  }
  return out.text(" = 0)");
}

HOLONICS_CALLABLE inline bool render_cultivation(
    const cultivation_surface &receipt,
    cultivated_formal_face &face) noexcept {
  using rederivation_render_detail::writer;
  using cultivation_render_detail::kernel_list;
  writer out{face}; face.identity = exact::word{198'410}; face.passage = receipt.passage;
  if (!receipt.exact || !out.text(
      "import Mathlib.Tactic.NormNum\n\nnamespace Soma.Holonics.R31\n\n")) return false;
  constexpr const char *names[4]{"reciprocal", "centralWalk", "signedTrace", "polygonIncidence"};
  for (std::uint8_t family = 0; family < cultivated_surface_family_count; ++family) {
    const auto &organ = receipt.kernels[family];
    if (!out.text("def ") || !out.text(names[family]) || !out.text("Kernel : List ℤ := ") ||
        !kernel_list(out, organ) || !out.text("\n\ntheorem ") || !out.text(names[family]) ||
        !out.text("Organ : ") || !out.text(names[family]) || !out.text("Kernel = ") ||
        !kernel_list(out, organ)) return false;
    for (std::uint8_t series = 0; series < organ.series_count; ++series)
      for (std::uint8_t n = 0; n + organ.order < organ.sample_count[series]; ++n)
        if (!out.text(" ∧\n  ") ||
            !render_cultivation_residual(out, organ, series, n)) return false;
    if (!out.text(" := by\n  norm_num [") || !out.text(names[family]) ||
        !out.text("Kernel]\n\n")) return false;
  }
  return out.text(
      "theorem generated_cultivated_shift_organs :\n"
      "    reciprocalKernel = [1, 1, -2, -1] ∧\n"
      "    centralWalkKernel = [1, 4, 4, -4, -8, -4] ∧\n"
      "    signedTraceKernel = [5, -2, 1] ∧\n"
      "    polygonIncidenceKernel = [1, -3, 3, -1] := by\n"
      "  exact ⟨reciprocalOrgan.1, centralWalkOrgan.1, signedTraceOrgan.1, "
      "polygonIncidenceOrgan.1⟩\n\nend Soma.Holonics.R31\n\n"
      "#check Soma.Holonics.R31.generated_cultivated_shift_organs\n");
}

}  // namespace holonics::codec
