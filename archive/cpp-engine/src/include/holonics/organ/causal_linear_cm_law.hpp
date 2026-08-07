#pragma once

#include <holonics/organ/causal_linear_phase_law.hpp>
#include <holonics/organ/cm_incidence_law.hpp>

namespace holonics::organ::causal_linear_detail {

HOLONICS_CALLABLE constexpr void derive_cm(const cm_problem_card& card,
    causal_cm_section& out) noexcept {
  out.identity = exact::word{192'430};
  out.lineage = exact::word{card.lineage.value() + 30U};
  cm_incidence_receipt source{};
  cm_incidence_detail::form_translations(card, source);
  cm_incidence_detail::form_periodic(source);
  if (source.obstruction != cm_obstruction::invalid_foundation &&
      source.obstruction != cm_obstruction::none) { return; }
  if (!cm_characteristic_detail::characteristic(source.periodic)) { return; }
  out.factor_exact = cm_characteristic_detail::factor(source.periodic, -8, 8);
  out.factor_count = source.periodic.factor_count;
  for (std::uint8_t factor = 0; factor < out.factor_count; ++factor) {
    if (source.periodic.factors[factor].degree != 1) { out.factor_exact = false; continue; }
    out.factor_roots[factor] = -source.periodic.factors[factor].coefficients[1];
    out.factor_multiplicities[factor] = source.periodic.factors[factor].multiplicity;
  }
  set_matrix(out.incidence, cm_point_capacity, source.periodic.edge_count,
      192'431, out.lineage.value() + 1U);
  set_matrix(out.adjacency, cm_point_capacity, cm_point_capacity,
      192'432, out.lineage.value() + 2U);
  for (std::uint8_t edge = 0; edge < source.periodic.edge_count; ++edge) {
    const auto& value = source.periodic.edges[edge];
    out.incidence.values[value.source][edge] = -1;
    out.incidence.values[value.target][edge] = 1;
    out.edge_lineage[edge] = value.lineage;
  }
  for (std::uint8_t row = 0; row < cm_point_capacity; ++row) {
    for (std::uint8_t column = 0; column < cm_point_capacity; ++column) {
      out.adjacency.values[row][column] = source.periodic.adjacency[row][column];
    }
  }
  analyze(out.incidence, out.incidence_analysis, 192'433);
  characteristic(out.adjacency, out.adjacency_characteristic, 192'434);
  out.domain_characteristic_agrees = out.adjacency_characteristic.exact &&
      source.periodic.characteristic_exact;
  for (std::uint8_t slot = 0; slot <= cm_point_capacity; ++slot) {
    out.domain_characteristic_agrees = out.domain_characteristic_agrees &&
        out.adjacency_characteristic.coefficients[slot] ==
            source.periodic.characteristic[slot];
  }
  out.vertices = cm_point_capacity; out.edges = source.periodic.edge_count;
  out.homology_zero = static_cast<std::uint8_t>(out.vertices - out.incidence_analysis.rank);
  out.homology_one = static_cast<std::uint8_t>(out.edges - out.incidence_analysis.rank);
  out.exact = source.periodic.exact && out.incidence_analysis.exact &&
      out.adjacency_characteristic.exact && out.domain_characteristic_agrees &&
      out.factor_exact && out.factor_count == 3 &&
      out.incidence_analysis.rank == 15 && out.homology_zero == 1 &&
      out.homology_one == 25;
}

}  // namespace holonics::organ::causal_linear_detail
