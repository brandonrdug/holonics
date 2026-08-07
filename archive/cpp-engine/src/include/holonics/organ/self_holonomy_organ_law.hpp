#pragma once

#include <holonics/organ/cultivated_organ_application_law.hpp>
#include <holonics/organ/elementary_matrix_law.hpp>
#include <holonics/organ/shift_organ_cultivation_law.hpp>

namespace holonics::organ::self_holonomy_detail {

HOLONICS_CALLABLE inline void clear(elementary_workspace &workspace) noexcept {
  for (auto &row : workspace.matrix) for (auto &value : row) value = {};
}

HOLONICS_CALLABLE inline void cultivate(const chart_receipt &chart,
    elementary_workspace &workspace, self_organ_receipt &out) noexcept {
  elementary_matrix_detail::trace_stream(chart.closed_word, out.trace);
  out.trace_count = 8;
  developmental_stream_card card{}; card.metadata.parsed = true;
  card.metadata.lineage = exact::word{520'325}; card.series_count = 1;
  card.sample_count[0] = out.trace_count; card.maximum_order = 3; card.maximum_degree = 0;
  card.family = cultivation_family::signed_trace;
  for (std::uint8_t i = 0; i < out.trace_count; ++i) card.samples[0][i] = out.trace[i];
  constexpr std::uint8_t orders[3]{1,2,3};
  bool selected = false;
  for (std::uint8_t i = 0; i < 3; ++i) {
    clear(workspace);
    shift_cultivation_detail::derive_candidate(card, orders[i], 0, workspace.matrix,
                                                out.candidates[i]);
    if (!selected && out.candidates[i].obstruction == cultivation_obstruction::none) {
      selected = true; out.candidates[i].selected = true; const auto &candidate = out.candidates[i];
      out.organ.order = candidate.order; out.organ.degree = 0;
      out.organ.features = candidate.features; out.organ.minimum_prefix = candidate.order;
      out.organ.family = cultivation_family::signed_trace; out.organ.primitive = candidate.primitive;
      out.organ.lineage = card.metadata.lineage;
      for (std::uint8_t slot = 0; slot < candidate.features; ++slot)
        out.organ.coefficients[slot] = candidate.coefficients[slot];
    }
  }
  out.selected_exact = selected && out.organ.order == 2 && out.organ.features == 3 &&
      out.organ.coefficients[0] == 1 && out.organ.coefficients[1] == -3 &&
      out.organ.coefficients[2] == 1;
}

HOLONICS_CALLABLE inline void close(elementary_calculus_receipt &out,
    elementary_workspace &workspace) noexcept {
  cultivate(out.chart, workspace, out.self_organ);
  out.connected = out.occurrence.theory_formed && out.composition.theory_formed &&
      out.receiver.theory_formed && out.chart.theory_formed && out.conduct.theory_formed &&
      out.self_organ.selected_exact;
  out.passage = exact::word{199'400}; out.lineage = exact::word{520'320};
  out.theory_formed = out.development_ports_distinct && out.connected;
}

HOLONICS_CALLABLE inline void derive_source(const heldout_triangle_card &card,
    heldout_workspace &workspace, heldout_holonomy_receipt &out) noexcept {
  using namespace elementary_matrix_detail;
  out.product = multiply(multiply(card.edges[0], card.edges[1]), card.edges[2]);
  trace_stream(out.product, workspace.hidden);
  auto changed_edges = card.edges[2]; changed_edges.value[card.changed_slot] = card.changed_value;
  const auto changed_product = multiply(multiply(card.edges[0], card.edges[1]), changed_edges);
  trace_stream(changed_product, workspace.changed);
  out.tail.sample_count = elementary_trace_count; out.tail.prefix_count = 2;
  out.tail.source[0] = workspace.hidden[0]; out.tail.source[1] = workspace.hidden[1];
}

HOLONICS_CALLABLE inline void predict(const cultivated_shift_organ &organ,
    heldout_holonomy_receipt &out) noexcept {
  static_cast<void>(cultivated_application_detail::predict(&organ, out.tail, 2, 0));
  out.tail.prediction_before_comparison = true; out.prediction_before_comparison = true;
  tail_receipt excluded{}; excluded.sample_count = elementary_trace_count;
  out.exclusion = cultivated_application_detail::predict(nullptr, excluded, 2, 0);
}

HOLONICS_CALLABLE inline void compare(const cultivated_shift_organ &organ,
    const heldout_workspace &workspace, heldout_holonomy_receipt &out) noexcept {
  bool exact = true;
  for (std::uint8_t i = 0; i < elementary_trace_count; ++i) {
    out.tail.source[i] = workspace.hidden[i];
    exact = exact && exact::small_rational_law::equal(out.tail.predicted[i], workspace.hidden[i]);
  }
  out.tail.exact = exact; out.tail.prediction_count = elementary_trace_count - 2U;
  tail_receipt changed{}; changed.sample_count = elementary_trace_count;
  for (std::uint8_t i = 0; i < elementary_trace_count; ++i) changed.source[i] = workspace.changed[i];
  out.changed = cultivated_application_detail::predict(&organ, changed, 2, 0);
  out.development_sources_absent = true;
  out.ablation_exact = out.exclusion == cultivation_obstruction::organ_absent;
  out.improved = exact && out.ablation_exact;
  out.passage = exact::word{199'401}; out.lineage = exact::word{520'326};
  out.theory_formed = out.improved && out.changed == cultivation_obstruction::heldout_residual &&
      out.product.value[0] == 2 && out.product.value[1] == 1 &&
      out.product.value[2] == 1 && out.product.value[3] == 1;
}

}  // namespace holonics::organ::self_holonomy_detail
