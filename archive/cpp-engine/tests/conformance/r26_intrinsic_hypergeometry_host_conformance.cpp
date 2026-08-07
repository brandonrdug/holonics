#include "r22_cases.hpp"
#include "r24_cases.hpp"
#include "r26_cases.hpp"

int main() {
  using namespace holonics;
  const auto mount = tests::r26_case({}, tests::r26_host_card(),
      tests::r22_host_card(), tests::r24_host_card());
  const auto receipt = organ::intrinsic_hypergeometry_detail::derive(
      mount.foundation, mount.question);
  organ::intrinsic_phase_case_receipt changed{};
  organ::intrinsic_hypergeometry_detail::derive_phase_incidence(
      mount.changed_foundation, 2, changed);
  organ::intrinsic_hypergeometry_detail::form_chronology(
      mount.changed_foundation, receipt.local_system, changed);
  const auto& baseline = receipt.cases[2];
  const bool changed_sensitive = changed.exact && baseline.vertex_count != changed.vertex_count &&
      baseline.lcm != changed.lcm &&
      organ::intrinsic_hypergeometry_detail::unequal_transitions(baseline, changed) &&
      organ::intrinsic_hypergeometry_detail::unequal_return(baseline, changed);
  const auto surface = event::intrinsic_hypergeometry_surface(
      receipt, changed, changed_sensitive);
  codec::intrinsic_hypergeometry_formal_face formal{};
  codec::intrinsic_hypergeometry_explanation explanation{};
  int failures = !receipt.all_exact || !receipt.theory_formed ||
      receipt.source_mask != 0x0fffU || !receipt.supported.exact ||
      receipt.supported.square_count != 40 ||
      !receipt.controls.equal_hull_unequal_transport ||
      !receipt.controls.equal_local_population_unequal_order ||
      !receipt.controls.equal_spectrum_unequal_support ||
      !receipt.controls.conjugate_rechart || !changed_sensitive ||
      changed.vertex_count != 40 || changed.edge_count != 80 || changed.face_count != 40 ||
      changed.flag_count != 320 || changed.lcm != 40 || changed.tour_count != 1 ||
      !codec::render_intrinsic_hypergeometry(surface, formal) ||
      !codec::render_intrinsic_hypergeometry_explanation(surface, explanation);
  for (std::uint8_t slot = 0; slot < organ::intrinsic_case_capacity; ++slot) {
    const auto& value = receipt.cases[slot];
    std::uint32_t seams = 0;
    for (const auto count : value.seam_receiver_fibers) { seams += count; }
    failures += !value.exact || value.edge_count != 2U * value.vertex_count ||
        value.face_count != value.vertex_count ||
        value.flag_count != 8U * value.face_count ||
        value.tour_count * value.lcm != value.vertex_count || seams != value.vertex_count;
  }
  return failures == 0 ? 0 : 1;
}
