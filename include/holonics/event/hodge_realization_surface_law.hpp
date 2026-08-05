#pragma once

#include <holonics/codec/hodge_realization_face.hpp>
#include <holonics/organ/hodge_realization_receipt.hpp>

namespace holonics::event {

[[nodiscard]] HOLONICS_CALLABLE constexpr codec::hodge_realization_surface
hodge_realization_surface(const organ::hodge_realization_receipt& inquiry,
    const organ::hodge_blowup_receipt& changed, bool changed_sensitive) noexcept {
  codec::hodge_realization_surface out{};
  out.passage = inquiry.theory.passage;
  for (std::uint8_t slot = 0; slot < 5; ++slot) {
    out.discriminant[slot] = inquiry.factors[0].discriminant.coefficients[slot];
  }
  for (std::uint8_t row = 0; row < organ::hodge_rank; ++row) {
    out.graph[row] = inquiry.cycles.locus.graph_class[row];
    out.negation[row] = inquiry.cycles.locus.negation_class[row];
    out.primitive[row] = inquiry.cycles.locus.primitive_class[row];
    out.polarization[row] = inquiry.product.polarization[row];
    for (std::uint8_t column = 0; column < organ::hodge_rank; ++column) {
      out.cup[row][column] = inquiry.product.cup[row][column];
      out.connection_t[row][column] = inquiry.product.connection_t_base[row][column];
      out.connection_u[row][column] = inquiry.product.connection_u_base[row][column];
    }
  }
  for (std::uint8_t row = 0; row < organ::hodge_blowup_rank; ++row) {
    out.selected_strict[row] = inquiry.blowup.strict_classes[inquiry.blowup.center_selector][row];
    out.exceptional[row] = inquiry.blowup.exceptional[row];
    for (std::uint8_t column = 0; column < organ::hodge_rank; ++column) {
      out.pullback[row][column] = inquiry.blowup.pullback[row][column];
    }
    for (std::uint8_t column = 0; column < organ::hodge_blowup_rank; ++column) {
      out.blowup_pairing[row][column] = inquiry.blowup.pairing[row][column];
    }
  }
  for (std::uint8_t row = 0; row < organ::hodge_rank; ++row) {
    for (std::uint8_t column = 0; column < organ::hodge_blowup_rank; ++column) {
      out.pushforward[row][column] = inquiry.blowup.pushforward[row][column];
    }
  }
  out.quotient_obstruction[0] = inquiry.cycles.locus.quotient_obstruction[0];
  out.quotient_obstruction[1] = inquiry.cycles.locus.quotient_obstruction[1];
  out.common_denominator = inquiry.product.common_denominator;
  out.graph_square = inquiry.cycles.locus.graph_square;
  out.mutual_intersection = inquiry.cycles.locus.mutual_intersection;
  out.primitive_square = inquiry.cycles.locus.primitive_square;
  out.tangent_obstruction = inquiry.cycles.locus.tangent_obstruction;
  out.normal_obstruction = inquiry.cycles.locus.normal_obstruction;
  out.selected_self_intersection =
      inquiry.blowup.self_intersections[inquiry.blowup.center_selector];
  out.enumerated = inquiry.cycles.fibers[0].enumerated;
  out.rational_rank = inquiry.product.rational_rank;
  out.f2_rank = inquiry.product.f2_rank; out.f1_rank = inquiry.product.f1_rank;
  out.h20 = inquiry.product.h20; out.h11 = inquiry.product.h11;
  out.h02 = inquiry.product.h02;
  out.integral_realizers = inquiry.cycles.fibers[0].realizer_count;
  out.rational_realizers = inquiry.cycles.fibers[1].realizer_count;
  out.effective_graphs = inquiry.cycles.fibers[0].effective_count;
  out.translation_count = organ::hodge_translation_capacity;
  out.blowup_rank = inquiry.blowup.rank; out.changed_center = changed.center_selector;
  out.center = inquiry.blowup.center_selector;
  out.multiplicity = inquiry.cycles.locus.multiplicity;
  out.factor_exact = inquiry.factors[0].exact && inquiry.factors[1].exact;
  out.cup_exact = inquiry.product.cup_nondegenerate && inquiry.product.polarization_square_two;
  out.transport_exact = inquiry.product.connection_t_preserves_cup &&
      inquiry.product.connection_u_preserves_cup && inquiry.product.mixed_curvature_zero &&
      inquiry.product.griffiths_transverse;
  out.locus_exact = inquiry.cycles.locus.exact;
  out.translations_exact = inquiry.cycles.translations_distinct;
  out.fibers_exact = inquiry.cycles.fibers[0].exact && inquiry.cycles.fibers[1].exact &&
      inquiry.cycles.fibers[2].exact;
  out.blowup_exact = inquiry.blowup.exact && changed.exact;
  out.changed_sensitive = changed_sensitive;
  out.alternatives_retained = inquiry.alternatives_retained;
  out.rational_integral_separated = inquiry.cycles.rational_integral_separated;
  out.outside_image = inquiry.cycles.fibers[2].outside_image;
  return out;
}

}  // namespace holonics::event
