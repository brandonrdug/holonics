#pragma once

#include <holonics/organ/cm_window_law.hpp>

namespace holonics::organ::cm_incidence_detail {

HOLONICS_CALLABLE constexpr void form_characteristic(const cm_problem_card& card,
    cm_graph_receipt& graph) noexcept {
  if (!graph.exact || !cm_characteristic_detail::characteristic(graph) ||
      !cm_characteristic_detail::factor(graph, card.factor_min, card.factor_max)) {
    graph.characteristic_exact = false;
  }
}

HOLONICS_CALLABLE constexpr void form_candidates(cm_incidence_receipt& out) noexcept {
  std::uint8_t four_direction_edges = 0;
  for (std::uint8_t direction = 0; direction < cm_degree_capacity; ++direction) {
    four_direction_edges = static_cast<std::uint8_t>(
        four_direction_edges + out.projection.direction_population[direction]);
  }
  out.candidates[0] = {cm_candidate_kind::four_direction_collapse,
      exact::word{190'700}, out.projection.lineage + 190'700U,
      out.projection.unit_pair_count, four_direction_edges,
      four_direction_edges == out.projection.unit_pair_count, true, false};
  out.candidates[1] = {cm_candidate_kind::modular_wrap_window,
      exact::word{190'701}, out.projection.lineage + 190'701U,
      out.projection.unit_pair_count, out.periodic.edge_count,
      out.periodic.edge_count == out.projection.unit_pair_count, true, false};
  out.candidates[2] = {cm_candidate_kind::coefficient_sum_projection,
      exact::word{190'702}, out.projection.lineage + 190'702U,
      cm_point_capacity, out.projection.distinct_scalar_sums, true,
      out.projection.distinct_scalar_sums == cm_point_capacity, false};
  out.alternatives_retained = true;
}

HOLONICS_CALLABLE constexpr void close_cm_incidence(
    const cm_incidence_foundation& foundation, const cm_incidence_question& question,
    cm_incidence_receipt& out) noexcept {
  out.question = question;
  if (!valid_foundation(foundation) || question.identity.value() == 0 ||
      question.receiver.value() == 0 || question.material.value() == 0) {
    out.obstruction = cm_obstruction::invalid_foundation; return;
  }
  bool translations_exact = out.returned_translations == foundation.card.translation_count;
  for (std::uint8_t slot = 0; slot < out.returned_translations; ++slot) {
    translations_exact = translations_exact && out.translations[slot].exact;
  }
  const bool characteristic_exact = out.periodic.characteristic_exact &&
      out.window.characteristic_exact && out.periodic.factor_count != 0 &&
      out.window.factor_count != 0;
  const bool aperture_exact = out.periodic.edge_count > out.window.edge_count &&
      out.projection.lost_count == out.periodic.edge_count - out.window.edge_count &&
      out.projection.projection_loss == 0 && out.scattering.interchange_broken;
  out.all_exact = translations_exact && out.periodic.exact && out.window.exact &&
      out.projection.exact && out.scattering.exact && characteristic_exact && aperture_exact;
  if (!out.all_exact) { out.obstruction = cm_obstruction::characteristic_refused; return; }
  out.theory = {exact::word{176'500}, exact::word{196'500},
      exact::word{foundation.provenance.value() + foundation.card.lineage.value() +
          out.periodic.lineage + out.window.lineage},
      translations_exact, out.projection.factor_expansion_agree, characteristic_exact,
      aperture_exact, out.alternatives_retained};
  out.obstruction = cm_obstruction::none;
  out.theory_formed = out.theory.norm_one && out.theory.incidence_agreement &&
      out.theory.characteristic_transport && out.theory.aperture_scattering &&
      out.theory.alternatives_retained;
}

}  // namespace holonics::organ::cm_incidence_detail
