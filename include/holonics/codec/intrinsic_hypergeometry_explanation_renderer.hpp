#pragma once

#include <holonics/codec/intrinsic_hypergeometry_face.hpp>

namespace holonics::codec {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_intrinsic_hypergeometry_explanation(
    const intrinsic_hypergeometry_surface& surface,
    intrinsic_hypergeometry_explanation& out) noexcept {
  if (surface.passage.value() == 0 || !surface.incidence_exact ||
      !surface.distributions_exact || !surface.sections_exact ||
      !surface.supports_separated || !surface.controls_exact ||
      !surface.changed_sensitive || !surface.alternatives_retained) { return false; }
  out.identity = exact::word{128'701}; out.passage = surface.passage;
  return append_blind(out.bytes, out.byte_count,
      "The recurring polygon is only one receiver face. The resident return now keeps every "
      "product vertex, oriented edge, filled face, flag, star, link, shared seam, CRT successor, "
      "projection fiber, and transported local section. Its seam words act as causal teeth: their "
      "ordered neighboring distribution selects an exact continuation, while a simultaneous seam "
      "retains two unequal monodromy resolutions as an obstruction. A phase face and a CM Cayley "
      "square meet through the same oriented four-cycle and share its characteristic polynomial, "
      "but only the phase cycle bounds an owned two-cell. The nontrivial variation commutator can "
      "therefore remain supported on the CM loop while obstructing extension across the filled "
      "phase face. Equal four-corner receiver hulls, equal normalized local populations, and equal "
      "cycle spectra consequently do not erase their retained source fibers. Axis swap returns a "
      "basis-conjugate passage, and changing (5,7) to (5,8) rebuilds the word, section, and face "
      "population. This is a bounded characteristic archetype calculus, not evidence for Hodge or RH.");
}

}  // namespace holonics::codec
