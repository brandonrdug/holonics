#pragma once

#include <holonics/organ/rederivation_geometry_alternative_law.hpp>
#include <holonics/organ/rederivation_receipt.hpp>

namespace holonics::organ::rederivation_realization_detail {

HOLONICS_CALLABLE inline void close(rederivation_receipt &out) noexcept {
  bool polygons = true;
  for (const auto &polygon : out.polygons) {
    polygons = polygons && polygon.simple && polygon.pick_exact &&
               polygon.ehrhart_exact && polygon.reciprocity_exact;
  }
  out.source_separated =
      out.matching_card.metadata.lineage != out.lattice_card.metadata.lineage &&
      out.matching_card.metadata.lineage != out.cover_card.metadata.lineage &&
      out.lattice_card.metadata.lineage != out.cover_card.metadata.lineage;
  out.comparison_withheld = true;
  out.self_crossing_obstructed =
      rederivation_geometry_alternative_detail::self_crossing_foil(
          out.lattice_card);
  out.alternatives_retained = out.matching.duplicate_q_obstructed &&
                              out.matching.changed_independence_undetermined &&
                              out.self_crossing_obstructed &&
                              out.potential.disconnected_obstructed &&
                              out.cover.width_two_obstructed;
  out.dependency_exact = out.potential.geometry_return_mounted;
  out.all_exact = out.matching.independence_supported && polygons &&
                  out.potential.equations_exact && out.potential.eigen_exact &&
                  out.potential.symbolic_minimum &&
                  out.cover.saturation_exact && out.cover.cover_exact &&
                  out.source_separated && out.alternatives_retained &&
                  out.dependency_exact;
  out.theory = {exact::word{197'399},
                exact::word{197'400},
                exact::word{out.matching.lineage.value() +
                            out.polygons[1].lineage.value() +
                            out.potential.lineage.value() +
                            out.cover.lineage.value()},
                0,
                4,
                3,
                out.all_exact};
  out.theory_formed = out.all_exact;
  out.obstruction = out.all_exact ? rederivation_obstruction::none
                                  : rederivation_obstruction::matching_refused;
}

} // namespace holonics::organ::rederivation_realization_detail
