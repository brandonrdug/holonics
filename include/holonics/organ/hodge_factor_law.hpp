#pragma once

#include <holonics/organ/hodge_realization_receipt.hpp>
#include <holonics/organ/variation_connection_law.hpp>

namespace holonics::organ::hodge_factor_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool same_root(
    affine_integer_coefficient value, std::int64_t constant,
    std::int64_t parameter) noexcept {
  return value.constant == constant && value.parameter == parameter;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool make_variation_card(
    const hodge_family_source& source, std::uint8_t factor,
    algebraic_variation_card& card) noexcept {
  if (!source.exact || source.term_count == 0 || factor >= hodge_factor_capacity) { return false; }
  bool y_square = false;
  for (std::uint8_t slot = 0; slot < source.term_count; ++slot) {
    const auto& term = source.terms[slot];
    if (term.y_power == 2 && term.x_power == 0 && term.parameter_power == 0 &&
        term.coefficient == 1) { y_square = true; continue; }
    if (term.y_power != 0 || term.x_power > 3 || term.parameter_power > 1) { return false; }
    auto& coefficient = card.coefficients[term.x_power];
    if (term.parameter_power == 0) { coefficient.constant += term.coefficient; }
    else { coefficient.parameter += term.coefficient; }
  }
  if (!y_square) { return false; }
  card.schema = exact::word{240'024}; card.occurrence = exact::word{195'400U + factor};
  card.lineage = source.lineage; card.byte_fold = source.identity.value();
  card.path_fold = source.lineage.value(); card.byte_count = source.term_count;
  constexpr exact::small_rational samples[7]{{-3,1},{-2,1},{-1,1},{1,2},{2,1},{3,1},{4,1}};
  for (std::uint8_t slot = 0; slot < 7; ++slot) { card.samples[slot] = samples[slot]; }
  card.root_min = -2; card.root_max = 2; card.form_min = -2; card.form_max = 2;
  card.degree = 3; card.cover_degree = 2; card.sample_count = 7;
  card.discovery_count = 5; card.series_depth = 6; card.parsed = true; return true;
}

HOLONICS_CALLABLE constexpr void order_roots(
    const algebraic_variation_receipt& source, hodge_factor_receipt& out) noexcept {
  for (std::uint8_t slot = 0; slot < source.root_count; ++slot) {
    const auto& candidate = source.roots[slot]; std::uint8_t target = 3;
    if (same_root(candidate.root, 0, 0)) { target = 0; }
    else if (same_root(candidate.root, 1, 0)) { target = 1; }
    else if (same_root(candidate.root, 0, 1)) { target = 2; }
    if (target < 3) { out.roots[target] = candidate; }
  }
}

HOLONICS_CALLABLE constexpr void derive(const hodge_realization_foundation& foundation,
    std::uint8_t factor, hodge_factor_receipt& out) noexcept {
  if (factor >= foundation.card.factor_count) { return; }
  out.mounted = foundation.card.factors[factor]; out.base_parameter =
      factor == 0 ? foundation.card.base_t : foundation.card.base_u;
  algebraic_variation_card card{};
  if (!make_variation_card(out.mounted, factor, card)) { return; }
  const algebraic_variation_foundation variation{exact::word{195'410U + factor},
      exact::word{195'412U + factor}, exact::word{195'414U + factor},
      exact::word{195'416U + factor}, exact::word{195'418U + factor},
      exact::word{195'420U + factor}, exact::word{195'422U + factor},
      exact::word{195'424U + factor}, card};
  algebraic_variation_receipt derived{};
  variation_polynomial_detail::derive_family(variation, derived);
  variation_connection_detail::derive_connection(derived);
  order_roots(derived, out); out.discriminant = derived.discriminant;
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      out.connection[row][column] = derived.connection.numerator[row][column];
    }
  }
  out.denominator = variation_polynomial_detail::scale(
      derived.connection.pole_polynomial, derived.connection.denominator_scale);
  out.alternating[0][1] = 1; out.alternating[1][0] = -1;
  out.identity = exact::word{195'430U + factor};
  out.lineage = exact::word{out.mounted.lineage.value() + 64U};
  out.source_derived = true;
  out.roots_exact = derived.roots_exact && same_root(out.roots[0].root,0,0) &&
      same_root(out.roots[1].root,1,0) && same_root(out.roots[2].root,0,1);
  out.discriminant_exact = derived.discriminant_exact && out.discriminant.degree == 4;
  const auto base = exact::small_rational_law::make(out.base_parameter);
  const auto value = variation_polynomial_detail::evaluate(out.discriminant, base);
  out.smooth_base = value.numerator != 0;
  out.connection_exact = derived.connection.exact && out.denominator.degree == 2;
  out.exact = out.roots_exact && out.discriminant_exact && out.smooth_base &&
      out.connection_exact;
}

}  // namespace holonics::organ::hodge_factor_detail
