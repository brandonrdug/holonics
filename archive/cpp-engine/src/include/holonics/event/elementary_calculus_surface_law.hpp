#pragma once

#include <holonics/codec/elementary_calculus_face.hpp>
#include <holonics/event/elementary_calculus_rest.hpp>
#include <holonics/organ/elementary_calculus_receipt.hpp>

namespace holonics::event {

[[nodiscard]] HOLONICS_CALLABLE inline codec::elementary_matrix2_surface matrix_surface(
    const organ::exact_matrix2 &source) noexcept {
  codec::elementary_matrix2_surface out{};
  for (std::uint8_t i = 0; i < 4; ++i) out.value[i] = source.value[i];
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE inline codec::elementary_calculus_surface elementary_surface(
    const organ::elementary_development_bundle &cards,
    const organ::elementary_calculus_receipt &receipt) noexcept {
  codec::elementary_calculus_surface out{}; out.passage = receipt.passage; out.exact = receipt.theory_formed;
  out.occurrence.selected_mask = receipt.occurrence.selected_mask;
  for (std::uint8_t row = 0; row < 6; ++row) {
    out.occurrence.payload[row] = cards.occurrence.payload[row];
    for (std::uint8_t field = 0; field < 5; ++field)
      out.occurrence.coordinates[row][field] = cards.occurrence.coordinates[row][field];
  }
  for (std::uint8_t row = 0; row < 4; ++row) for (std::uint8_t edge = 0; edge < 5; ++edge)
    out.occurrence.boundary_one[row][edge] = cards.occurrence.boundary_one[row][edge];
  for (std::uint8_t edge = 0; edge < 5; ++edge) for (std::uint8_t face = 0; face < 2; ++face)
    out.occurrence.boundary_two[edge][face] = cards.occurrence.boundary_two[edge][face];
  for (std::uint8_t row = 0; row < 4; ++row) for (std::uint8_t face = 0; face < 2; ++face) {
    out.occurrence.unsigned_residual[row][face] = receipt.occurrence.boundaries[1].residual[row][face];
    out.occurrence.incoherent_residual[row][face] = receipt.occurrence.boundaries[3].residual[row][face];
  }
  for (std::uint8_t c = 0; c < 5; ++c) {
    out.composition.codes[c] = static_cast<std::uint8_t>(receipt.composition.signatures[c].code);
    out.composition.visible[c] = cards.composition.cases[c].visible;
    out.composition.contact[c] = cards.composition.cases[c].contact;
    out.composition.predecessor_link[c] = cards.composition.cases[c].predecessor_link;
    out.composition.forward_available[c] = cards.composition.cases[c].forward_available;
    out.composition.reverse_available[c] = cards.composition.cases[c].reverse_available;
    for (std::uint8_t f = 0; f < 4; ++f) {
      out.composition.forward[c][f] = cards.composition.cases[c].forward[f];
      out.composition.reverse[c][f] = cards.composition.cases[c].reverse[f];
    }
  }
  for (std::uint8_t i = 0; i < 6; ++i) {
    out.receiver.coarse[i] = cards.receiver.coarse[i]; out.receiver.fine[i] = cards.receiver.fine[i];
    out.receiver.first[i] = cards.receiver.first_consequence[i];
    out.receiver.strict[i] = cards.receiver.strict_consequence[i];
  }
  out.receiver.coarse_fibers = receipt.receiver.coarse_fibers;
  out.receiver.fine_fibers = receipt.receiver.fine_fibers;
  out.receiver.strict_witnesses = receipt.receiver.coarse_strict_witnesses;
  out.chart.first = matrix_surface(cards.chart.first); out.chart.second = matrix_surface(cards.chart.second);
  out.chart.first_path = matrix_surface(receipt.chart.first_path);
  out.chart.second_path = matrix_surface(receipt.chart.second_path);
  out.chart.residual = matrix_surface(receipt.chart.residual);
  out.chart.closed = matrix_surface(receipt.chart.closed_word);
  out.chart.determinant = receipt.chart.determinant; out.chart.trace = receipt.chart.trace;
  for (std::uint8_t c = 0; c < 8; ++c) {
    for (std::uint8_t f = 0; f < 7; ++f) out.conduct.cases[c][f] = cards.conduct.cases[c].fields[f];
    out.conduct.cases[c][7] = cards.conduct.cases[c].changed_conduct ? 1U : 0U;
  }
  for (std::uint8_t f = 0; f < 7; ++f)
    out.conduct.conditions[f] = receipt.conduct.selected_conditions[f];
  out.conduct.selected_code = receipt.conduct.selected_code;
  for (std::uint8_t i = 0; i < 3; ++i)
    out.organ.coefficients[i] = receipt.self_organ.organ.coefficients[i];
  out.organ.trace_count = receipt.self_organ.trace_count;
  for (std::uint8_t i = 0; i < out.organ.trace_count; ++i) out.organ.trace[i] = receipt.self_organ.trace[i];
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE inline codec::heldout_holonomy_surface heldout_surface(
    const organ::heldout_holonomy_receipt &receipt,
    const organ::cultivated_shift_organ &organ) noexcept {
  codec::heldout_holonomy_surface out{}; out.product = matrix_surface(receipt.product);
  for (std::uint8_t i = 0; i < 3; ++i) out.organ.coefficients[i] = organ.coefficients[i];
  out.organ.trace_count = receipt.tail.sample_count; out.sample_count = receipt.tail.sample_count;
  out.prefix_count = receipt.tail.prefix_count; out.changed = static_cast<std::uint8_t>(receipt.changed);
  out.exclusion = static_cast<std::uint8_t>(receipt.exclusion); out.passage = receipt.passage;
  out.prediction_before_comparison = receipt.prediction_before_comparison;
  out.source_detached = receipt.development_sources_absent;
  out.exact = receipt.theory_formed;
  for (std::uint8_t i = 0; i < out.sample_count; ++i) {
    out.source[i] = receipt.tail.source[i]; out.predicted[i] = receipt.tail.predicted[i];
    out.organ.trace[i] = receipt.tail.source[i];
  }
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE inline codec::elementary_calculus_surface rested_elementary_surface(
    const elementary_law_bundle &laws) noexcept {
  codec::elementary_calculus_surface out{}; out.exact = laws.checker_founded;
  out.occurrence.selected_mask = laws.occurrence_mask;
  for (std::uint8_t i = 0; i < 5; ++i) out.composition.codes[i] = laws.composition_codes[i];
  out.receiver.coarse_fibers = laws.coarse_fibers; out.receiver.fine_fibers = laws.fine_fibers;
  out.receiver.strict_witnesses = laws.strict_witnesses;
  out.chart.residual = matrix_surface(laws.path_residual);
  out.chart.closed = matrix_surface(laws.closed_word);
  out.chart.determinant = laws.closed_word.value[0]*laws.closed_word.value[3] -
      laws.closed_word.value[1]*laws.closed_word.value[2];
  out.chart.trace = laws.closed_word.value[0] + laws.closed_word.value[3];
  out.conduct.selected_code = laws.conduct_code;
  for (std::uint8_t i = 0; i < 7; ++i) out.conduct.conditions[i] = laws.conduct_conditions[i];
  for (std::uint8_t i = 0; i < 3; ++i) out.organ.coefficients[i] = laws.self_organ.coefficients[i];
  return out;
}

}  // namespace holonics::event
