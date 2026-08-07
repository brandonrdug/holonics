#pragma once

#include <holonics/codec/hodge_realization_face.hpp>

namespace holonics::codec {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_hodge_realization_explanation(
    const hodge_realization_surface& source, hodge_explanation& out) noexcept {
  if (source.passage.value() == 0 || !source.factor_exact || !source.cup_exact ||
      !source.transport_exact || !source.locus_exact || !source.translations_exact ||
      !source.fibers_exact || !source.blowup_exact || !source.changed_sensitive ||
      !source.alternatives_retained) { return false; }
  out.identity = exact::word{128'901}; out.passage = source.passage;
  return append_blind(out.bytes, out.byte_count,
      "Two mounted Legendre factors were composed into one rank-six degree-two carrier. Its cup "
      "form, Hodge filtration, and the two induced Gauss-Manin directions were derived in the "
      "same exact integer chart; the directions preserve the form, commute, and cross only the "
      "declared filtration face. The identity and negation correspondences determine distinct "
      "cohomology classes, while four algebraically distinct two-torsion translations share the "
      "identity graph class. Their cleared rational maps satisfy the curve equation and preserve "
      "the differential without decimal root approximation. The diagonal class has a first-order "
      "Hodge obstruction du-dt: diagonal transport closes, normal transport does not, with "
      "multiplicity one. Bounded coefficient enumeration retains sixteen integral presentations "
      "of the graph class and sixteen rational presentations at denominator two, while a declared "
      "outside target remains obstructed. Blowing up a selected graph point adds the exact "
      "negative exceptional direction and changes only the selected strict transform; moving "
      "the center moves that incidence. This is a bounded project-postulate realization receipt, "
      "not a proof of the Hodge conjecture or a claim about arbitrary varieties.");
}

}  // namespace holonics::codec
