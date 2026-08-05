#pragma once

#include <holonics/organ/expression_residue_law.hpp>

namespace holonics::organ::expression_geometry_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_foundation(
    const expression_geometry_foundation& foundation) noexcept {
  const auto& card = foundation.card;
  if (!card.parsed || card.schema != exact::word{270'027} ||
      card.presentation_count != expression_presentation_capacity || card.series_depth != 11 ||
      card.discovery_min != -4 || card.discovery_max != 4 || card.holdout_first != 5 ||
      card.holdout_second != 6 || card.chart_min != -2 || card.chart_max != 2 ||
      foundation.ecology.value() == 0 || foundation.expression.value() == 0 ||
      foundation.ideal.value() == 0 || foundation.local_ring.value() == 0 ||
      foundation.differential.value() == 0 || foundation.characteristic.value() == 0 ||
      foundation.theorem.value() == 0 || foundation.provenance.value() == 0) { return false; }
  for (const auto& expression : card.presentations) {
    if (!expression_sparse_detail::valid(expression)) { return false; }
  }
  return true;
}

HOLONICS_CALLABLE constexpr void derive_presentation(
    const expression_geometry_foundation& foundation, std::uint8_t slot,
    expression_presentation_receipt& out) noexcept {
  if (!valid_foundation(foundation) || slot >= expression_presentation_capacity) { return; }
  expression_ideal_detail::derive(foundation.card.presentations[slot],
      foundation.card.chart_min, foundation.card.chart_max, out);
  expression_connection_detail::derive(out, foundation.card.discovery_min,
      foundation.card.discovery_max, foundation.card.holdout_first,
      foundation.card.holdout_second);
  expression_cyclic_detail::derive(out);
  expression_series_detail::derive(out, foundation.card.series_depth);
  expression_residue_detail::derive(out);
  out.exact = out.ideal.exact && out.connection.exact && out.scalar.exact &&
      out.indicial.exact && out.residue.exact;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool same_scalar(
    const expression_presentation_receipt& left,
    const expression_presentation_receipt& right) noexcept {
  if (!left.scalar.exact || !right.scalar.exact) { return false; }
  for (std::uint8_t derivative = 0; derivative <= 4; ++derivative) {
    if (!expression_exact_detail::same_polynomial(left.scalar.coefficients[derivative],
            right.scalar.coefficients[derivative])) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr expression_rechart_receipt search_rechart(
    const sparse_expression& source, const sparse_expression& target,
    std::int8_t minimum, std::int8_t maximum, bool gaussian) noexcept {
  expression_rechart_receipt out{}; out.source = source.identity; out.target = target.identity;
  out.lineage = exact::word{source.lineage.value() + target.lineage.value()};
  const std::int8_t y_squares[2]{1,-1}; const auto count = static_cast<std::uint8_t>(gaussian ? 2U : 1U);
  for (std::int8_t x_scale = -1; x_scale <= 1; x_scale += 2) {
    for (std::int8_t shift = minimum; shift <= maximum; ++shift) {
      for (std::uint8_t y_slot = 0; y_slot < count; ++y_slot) {
        for (std::int8_t equation = -1; equation <= 1; equation += 2) {
          if (!expression_sparse_detail::rechart_identity(source, target, x_scale, shift,
                  y_squares[y_slot], equation)) { continue; }
          out.x_scale = x_scale; out.x_shift = shift; out.y_square = y_squares[y_slot];
          out.equation_scale = equation; out.rational = y_squares[y_slot] == 1;
          out.gaussian = y_squares[y_slot] == -1; out.expression_identity = true;
          out.geometry_identity = true; out.field_dependency_retained = out.gaussian;
          out.exact = true; return out;
        }
      }
    }
  }
  return out;
}

HOLONICS_CALLABLE constexpr void compose(const expression_geometry_foundation& foundation,
    expression_geometry_receipt& out) noexcept {
  out.mounted = foundation.card;
  bool exact = valid_foundation(foundation);
  for (const auto& presentation : out.presentations) { exact = exact && presentation.exact; }
  out.rational_rechart = search_rechart(foundation.card.presentations[0],
      foundation.card.presentations[1], foundation.card.chart_min,
      foundation.card.chart_max, false);
  const auto rational_twist = search_rechart(foundation.card.presentations[0],
      foundation.card.presentations[2], foundation.card.chart_min,
      foundation.card.chart_max, false);
  out.gaussian_rechart = search_rechart(foundation.card.presentations[0],
      foundation.card.presentations[2], foundation.card.chart_min,
      foundation.card.chart_max, true);
  const bool same_resultant = expression_exact_detail::same_polynomial(
      out.presentations[0].ideal.resultant, out.presentations[1].ideal.resultant) &&
      expression_exact_detail::same_polynomial(out.presentations[0].ideal.resultant,
          out.presentations[2].ideal.resultant);
  const bool scalar_equal = same_scalar(out.presentations[0], out.presentations[1]) &&
      same_scalar(out.presentations[0], out.presentations[2]);
  out.invariant_fiber.invariant = exact::word{194'800}; out.invariant_fiber.member_count = 3;
  for (std::uint8_t slot = 0; slot < 3; ++slot) {
    out.invariant_fiber.members[slot] = out.presentations[slot].identity;
  }
  out.invariant_fiber.rational_members_separated = !rational_twist.exact;
  out.invariant_fiber.complete = same_resultant && scalar_equal;
  out.controls.translated_support_changed = foundation.card.presentations[0].term_count !=
      foundation.card.presentations[1].term_count;
  out.controls.rational_rechart_exact = out.rational_rechart.exact;
  out.controls.equal_discriminant_not_rational_identity = same_resultant && !rational_twist.exact;
  out.controls.gaussian_extension_exact = out.gaussian_rechart.exact &&
      out.gaussian_rechart.field_dependency_retained;
  out.controls.equal_scalar_fiber_retained = scalar_equal && out.invariant_fiber.complete;
  out.controls.exact = out.controls.translated_support_changed &&
      out.controls.rational_rechart_exact && out.controls.equal_discriminant_not_rational_identity &&
      out.controls.gaussian_extension_exact && out.controls.equal_scalar_fiber_retained;
  out.no_expected_invariants = true; out.alternatives_retained =
      out.presentations[0].ideal.higher_factor_open &&
      out.presentations[2].ideal.higher_factor_open;
  out.obstruction = exact && out.controls.exact ? expression_geometry_obstruction::none :
      expression_geometry_obstruction::control_refused;
  out.theory = {exact::word{194'820}, exact::word{194'821},
      exact::word{foundation.card.lineage.value() + 640U}, 7,
      exact, exact, exact, scalar_equal, out.invariant_fiber.complete};
  out.all_exact = out.obstruction == expression_geometry_obstruction::none &&
      out.controls.exact && out.alternatives_retained; out.theory_formed = out.all_exact;
}

HOLONICS_CALLABLE constexpr void derive_changed(
    const expression_geometry_foundation& foundation, expression_changed_receipt& out) noexcept {
  derive_presentation(foundation, 0, out.presentations[0]);
  derive_presentation(foundation, 1, out.presentations[1]);
  out.rechart = search_rechart(foundation.card.presentations[0],
      foundation.card.presentations[1], foundation.card.chart_min,
      foundation.card.chart_max, false);
  out.exact = out.presentations[0].exact && out.presentations[1].exact && out.rechart.exact;
}

}  // namespace holonics::organ::expression_geometry_detail
