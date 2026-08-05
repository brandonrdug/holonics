#pragma once

#include <holonics/organ/algebraic_variation_law.hpp>
#include <holonics/organ/causal_linear_characteristic.hpp>
#include <holonics/organ/intrinsic_phase_distribution_law.hpp>
#include <holonics/organ/variation_loop_law.hpp>

namespace holonics::organ::intrinsic_hypergeometry_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool multiply_two(
    const std::int64_t left[2][2], const std::int64_t right[2][2],
    std::int64_t out[2][2]) noexcept {
  bool exact = true;
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      for (std::uint8_t inner = 0; inner < 2; ++inner) {
        std::int64_t product = 0; std::int64_t next = 0;
        exact = exact && blind_integer_detail::multiply(
            left[row][inner], right[inner][column], product) &&
            blind_integer_detail::add(
                out[row][column], product, next);
        out[row][column] = next;
      }
    }
  }
  return exact;
}

HOLONICS_CALLABLE constexpr void invert_unimodular(
    const std::int64_t source[2][2], std::int64_t out[2][2]) noexcept {
  out[0][0] = source[1][1]; out[0][1] = -source[0][1];
  out[1][0] = -source[1][0]; out[1][1] = source[0][0];
}

HOLONICS_CALLABLE constexpr void derive_section_source(
    const intrinsic_hypergeometry_foundation& foundation,
    intrinsic_series_receipt& series, intrinsic_local_system_receipt& local) noexcept {
  const algebraic_variation_foundation source_foundation{exact::word{139'940},
      exact::word{139'941}, exact::word{139'942}, exact::word{139'943},
      exact::word{139'944}, exact::word{139'945}, exact::word{139'946},
      exact::word{139'947}, foundation.variation};
  const algebraic_variation_question question{exact::word{149'940},
      exact::word{149'941}, exact::word{149'942}};
  const auto source = algebraic_variation_detail::derive(source_foundation, question);
  if (!source.all_exact) { return; }
  series.identity = exact::word{193'440};
  series.lineage = exact::word{source.scalar.lineage.value() + foundation.card.lineage.value()};
  for (std::uint8_t slot = 0; slot < 3; ++slot) { series.second[slot] = source.scalar.second[slot]; }
  for (std::uint8_t slot = 0; slot < 2; ++slot) { series.first[slot] = source.scalar.first[slot]; }
  series.zeroth = source.scalar.zeroth;
  const auto one = exact::rational<2>::normalized(
      exact::signed_magnitude<2>{false, exact::unsigned_128::from_word(1)},
      exact::unsigned_128::from_word(1));
  if (!one.accepted()) { return; }
  series.coefficients[0] = one.value;
  series.count = foundation.card.series_depth; series.recurrence_exact = series.count != 0;
  for (std::uint8_t n = 0; n + 1U < series.count; ++n) {
    const std::int64_t index = n;
    const std::int64_t denominator = (index + 1) *
        (series.second[1] * index + series.first[0]);
    const std::int64_t numerator = -(series.second[2] * index * (index - 1) +
        series.first[1] * index + series.zeroth);
    if (numerator <= 0 || denominator <= 0) { series.recurrence_exact = false; continue; }
    const auto next_numerator = exact::multiply(
        series.coefficients[n].numerator().magnitude(),
        exact::unsigned_128::from_word(static_cast<std::uint64_t>(numerator)));
    const auto next_denominator = exact::multiply(series.coefficients[n].denominator(),
        exact::unsigned_128::from_word(static_cast<std::uint64_t>(denominator)));
    if (!next_numerator.accepted() || !next_denominator.accepted()) {
      series.recurrence_exact = false; continue;
    }
    const auto next = exact::rational<2>::normalized(
        exact::signed_magnitude<2>{false, next_numerator.value}, next_denominator.value);
    series.recurrence_exact = series.recurrence_exact && next.accepted();
    if (next.accepted()) { series.coefficients[n + 1U] = next.value; }
  }
  local.identity = exact::word{193'441};
  local.lineage = exact::word{source.loops.lineages[0].value() +
      source.loops.lineages[1].value()};
  for (std::uint8_t loop = 0; loop < 2; ++loop) {
    for (std::uint8_t row = 0; row < 2; ++row) {
      for (std::uint8_t column = 0; column < 2; ++column) {
        local.positive[loop][row][column] = source.loops.monodromy[loop][row][column];
        local.form[row][column] = source.invariant.selected[row][column];
      }
    }
    invert_unimodular(local.positive[loop], local.inverse[loop]);
  }
  bool exact = multiply_two(local.positive[0], local.positive[1], local.ordered_first) &&
      multiply_two(local.positive[1], local.positive[0], local.ordered_second);
  std::int64_t front[2][2]{}; std::int64_t next[2][2]{};
  exact = exact && multiply_two(local.ordered_first, local.inverse[0], front) &&
      multiply_two(front, local.inverse[1], next);
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      local.commutator[row][column] = next[row][column];
    }
  }
  local.form_preserved = causal_linear_detail::preserves_form(
      local.positive[0], local.form) && causal_linear_detail::preserves_form(
          local.positive[1], local.form);
  local.alternatives_unequal = local.ordered_first[0][0] != local.ordered_second[0][0] ||
      local.ordered_first[0][1] != local.ordered_second[0][1] ||
      local.ordered_first[1][0] != local.ordered_second[1][0] ||
      local.ordered_first[1][1] != local.ordered_second[1][1];
  local.commutator_nontrivial = local.commutator[0][0] != 1 ||
      local.commutator[0][1] != 0 || local.commutator[1][0] != 0 ||
      local.commutator[1][1] != 1;
  local.exact = exact && local.form_preserved && local.alternatives_unequal &&
      local.commutator_nontrivial;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t reduce_mod(
    std::int64_t value, std::uint32_t modulus) noexcept {
  const auto magnitude = phase_crystal_detail::magnitude(value);
  std::uint64_t quotient = 0; std::uint64_t remainder = 0;
  if (!phase_crystal_detail::divide_unsigned(magnitude, modulus, quotient, remainder)) { return 0; }
  if (value >= 0 || remainder == 0) { return static_cast<std::uint32_t>(remainder); }
  return static_cast<std::uint32_t>(modulus - remainder);
}

HOLONICS_CALLABLE constexpr void modular_multiply(const std::uint32_t left[4],
    const std::uint32_t right[4], std::uint32_t modulus, std::uint32_t out[4]) noexcept {
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      std::uint64_t sum = 0;
      for (std::uint8_t inner = 0; inner < 2; ++inner) {
        sum += static_cast<std::uint64_t>(left[2U * row + inner]) *
            right[2U * inner + column];
      }
      std::uint64_t quotient = 0; std::uint64_t remainder = 0;
      static_cast<void>(phase_crystal_detail::divide_unsigned(sum, modulus, quotient, remainder));
      out[2U * row + column] = static_cast<std::uint32_t>(remainder);
    }
  }
}

}  // namespace holonics::organ::intrinsic_hypergeometry_detail
