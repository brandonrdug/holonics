#pragma once

#include <holonics/codec/characteristic_hypergeometry_face.hpp>
#include <holonics/codec/rederivation_renderer_atoms.hpp>

namespace holonics::codec {

HOLONICS_CALLABLE inline bool
render_characteristic_dossier(const characteristic_hypergeometry_surface &d,
                              const heldout_characteristic_surface &h,
                              characteristic_dossier_face &face) noexcept {
  using rederivation_render_detail::writer;
  writer out{face};
  face.identity = exact::word{200'412};
  face.passage = h.passage;
  if (!d.exact || !h.exact ||
      !out.text("# R33 characteristic hypergeometry return\n\nTruth status: "
                "project-postulate pending gate admission.\n\n"
                "The three developmental transition ecologies formed "))
    return false;
  std::uint16_t total = 0;
  for (const auto count : d.pair_count)
    total = static_cast<std::uint16_t>(total + count);
  if (!out.natural(total) || !out.text(" ordered face pairs and ") ||
      !out.natural(d.group_count) ||
      !out.text(" exact characteristic archetypes. Closed strata contained ") ||
      !out.natural(d.closed_strata[0]) || !out.text(" elliptic, ") ||
      !out.natural(d.closed_strata[1]) || !out.text(" parabolic, and ") ||
      !out.natural(d.closed_strata[2]) ||
      !out.text(
          " hyperbolic returns in this bounded population. These are counts, "
          "not universal probabilities.\n\n"
          "Exact elimination selected the primitive coefficient geometry ["))
    return false;
  for (std::uint8_t i = 0; i < characteristic_surface_feature_count; ++i) {
    if (i != 0 && !out.text(","))
      return false;
    if (!out.integer(d.coefficients[i]))
      return false;
  }
  return out.text(
             "]. It transports the closed commutator trace from the three open "
             "face traces. The retained collisions show why the individual "
             "faces alone are insufficient, why equal characteristic "
             "coordinates do not identify their source, and why order and "
             "rechart information survive outside this receiver.\n\n"
             "After the developmental words and matrices departed, a five-edge "
             "held-out local system exposed only (") &&
         out.integer(h.visible[0]) && out.text(",") &&
         out.integer(h.visible[1]) && out.text(",") &&
         out.integer(h.visible[2]) &&
         out.text("). The organ predicted closed trace ") &&
         out.integer(h.predicted_trace) && out.text(", characteristic [1,") &&
         out.integer(h.characteristic[1]) &&
         out.text(",1], and discriminant ") &&
         out.integer(h.predicted_discriminant) &&
         out.text(
             " before comparison; the independently formed matrix return "
             "agreed. Organ exclusion removed the prediction, while a "
             "determinant-violating transition returned an obstruction.\n\n"
             "The organ forgets word lineage, embedding, orientation, full "
             "matrices, and analytic continuation. Higher rank, arbitrary "
             "character varieties, Hodge realization, RH, and autonomous "
             "theorem valuation remain outside this aperture.\n");
}

} // namespace holonics::codec
