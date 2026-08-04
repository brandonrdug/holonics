#pragma once

#include <holonics/codec/cm_incidence_face.hpp>

namespace holonics::codec {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_cm_explanation(
    const cm_incidence_surface& surface, cm_explanation& out) noexcept {
  if (surface.passage.value() == 0 || !surface.norm_one ||
      !surface.incidence_agreement || !surface.characteristic_transport ||
      !surface.aperture_scattering || !surface.alternatives_retained) { return false; }
  out.identity = exact::word{126'601};
  out.passage = surface.passage;
  return append_blind(out.bytes, out.byte_count,
      "The exact CM source is Z[z]/(1+z+z^2+z^3+z^4). Its five derived powers have "
      "relative norm one, so every retained translation is a unit edge in the chosen complex "
      "receiver. The periodic residue crystal carries five commuting involutions. The bounded "
      "lift retains the field identities but refuses modular wrap: the resulting partial fifth "
      "direction no longer commutes with the four axes, and its characteristic return splits "
      "into boundary factors. Complete factorized translation incidence equals independent "
      "all-pair norm incidence; the injective field embedding loses no further edge. The "
      "four-direction, wrap-as-window, and coefficient-sum alternatives remain rejected.");
}

}  // namespace holonics::codec
