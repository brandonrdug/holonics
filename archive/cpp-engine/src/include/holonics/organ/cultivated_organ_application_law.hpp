#pragma once

#include <holonics/organ/cultivated_organ_receipt.hpp>

namespace holonics::organ::cultivated_application_detail {
namespace rational = exact::small_rational_law;

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t power(
    std::int64_t base, std::uint8_t exponent) noexcept {
  std::int64_t result = 1;
  for (std::uint8_t i = 0; i < exponent; ++i) result *= base;
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE inline cultivation_obstruction predict(
    const cultivated_shift_organ *organ, tail_receipt &tail,
    std::uint8_t prefix, std::int64_t index_offset) noexcept {
  if (organ == nullptr || !organ->checker_founded)
    return cultivation_obstruction::organ_absent;
  if (prefix < organ->minimum_prefix)
    return cultivation_obstruction::insufficient_prefix;
  for (std::uint8_t i = 0; i < prefix; ++i) tail.predicted[i] = tail.source[i];
  for (std::uint8_t target = prefix; target < tail.sample_count; ++target) {
    const auto n = index_offset + target - organ->order;
    exact::small_rational sum = rational::make(0);
    for (std::uint8_t shift = 0; shift < organ->order; ++shift) {
      std::int64_t coefficient = 0;
      for (std::uint8_t p = 0; p <= organ->degree; ++p)
        coefficient += organ->coefficients[shift * (organ->degree + 1U) + p] * power(n, p);
      sum = rational::add(sum, rational::multiply(rational::make(coefficient),
                                                   tail.predicted[target - organ->order + shift]));
    }
    std::int64_t forward = 0;
    for (std::uint8_t p = 0; p <= organ->degree; ++p)
      forward += organ->coefficients[organ->order * (organ->degree + 1U) + p] * power(n, p);
    if (forward == 0) return cultivation_obstruction::zero_forward_face;
    tail.predicted[target] = rational::divide(rational::negate(sum), rational::make(forward));
  }
  tail.prefix_count = prefix;
  tail.prediction_count = static_cast<std::uint8_t>(tail.sample_count - prefix);
  tail.prediction_before_comparison = true;
  tail.exact = true;
  for (std::uint8_t i = prefix; i < tail.sample_count; ++i)
    tail.exact = tail.exact && rational::equal(tail.predicted[i], tail.source[i]);
  return tail.exact ? cultivation_obstruction::none : cultivation_obstruction::heldout_residual;
}

HOLONICS_CALLABLE inline void derive_star(const star_structure_card &card,
    const cultivated_shift_organ &organ, tail_receipt &out) noexcept {
  out.sample_count = static_cast<std::uint8_t>(card.last_branch_count -
                                               card.first_branch_count + 1U);
  for (std::uint8_t i = 0; i < out.sample_count; ++i) {
    const auto branches = static_cast<std::int64_t>(card.first_branch_count + i);
    out.source[i] = rational::make(card.common_conductance,
        card.common_conductance * (branches + 1));
  }
  static_cast<void>(predict(&organ, out, 1, card.first_branch_count));
  tail_receipt changed{}; changed.sample_count = out.sample_count;
  for (std::uint8_t i = 0; i < changed.sample_count; ++i) {
    const auto branches = static_cast<std::int64_t>(card.first_branch_count + i);
    changed.source[i] = rational::make(card.changed_conductance,
        card.changed_conductance + card.common_conductance * branches);
  }
  out.changed_source = predict(&organ, changed, 1, card.first_branch_count);
  tail_receipt short_tail{}; short_tail.sample_count = out.sample_count;
  out.short_prefix = predict(&organ, short_tail, 0, card.first_branch_count);
  out.exclusion = predict(nullptr, short_tail, 1, card.first_branch_count);
}

HOLONICS_CALLABLE inline void walk_stream(const walk_structure_card &card,
    std::uint8_t step_count, tail_receipt &out) noexcept {
  std::int64_t current[33][33]{}; std::int64_t next[33][33]{};
  current[16][16] = 1; out.sample_count = static_cast<std::uint8_t>(card.maximum_half_horizon + 1U);
  out.source[0] = rational::make(1); std::int64_t denominator = 1;
  for (std::uint8_t step = 1; step <= 2U * card.maximum_half_horizon; ++step) {
    for (auto &row : next) for (auto &value : row) value = 0;
    for (std::uint8_t x = 0; x < 33; ++x) for (std::uint8_t y = 0; y < 33; ++y) {
      if (current[x][y] == 0) continue;
      for (std::uint8_t s = 0; s < step_count; ++s) {
        const auto nx = static_cast<std::int16_t>(x) + card.steps[s][0];
        const auto ny = static_cast<std::int16_t>(y) + card.steps[s][1];
        if (nx >= 0 && nx < 33 && ny >= 0 && ny < 33)
          next[nx][ny] += current[x][y];
      }
    }
    for (std::uint8_t x = 0; x < 33; ++x) for (std::uint8_t y = 0; y < 33; ++y)
      current[x][y] = next[x][y];
    denominator *= step_count;
    if ((step & 1U) == 0) out.source[step / 2U] = rational::make(current[16][16], denominator);
  }
}

HOLONICS_CALLABLE inline void derive_walk(const walk_structure_card &card,
    const cultivated_shift_organ &organ, tail_receipt &out) noexcept {
  walk_stream(card, card.step_count, out); static_cast<void>(predict(&organ, out, 1, 0));
  tail_receipt changed{}; walk_stream(card, static_cast<std::uint8_t>(card.step_count - 1U), changed);
  out.changed_source = predict(&organ, changed, 1, 0);
  tail_receipt short_tail{}; short_tail.sample_count = out.sample_count;
  out.short_prefix = predict(&organ, short_tail, 0, 0);
  out.exclusion = predict(nullptr, short_tail, 1, 0);
}

HOLONICS_CALLABLE inline void carrier_stream(const signed_carrier_card &card,
    const std::int16_t (&matrix)[4], tail_receipt &out) noexcept {
  std::int64_t state[4]{1,0,0,1}; out.sample_count = static_cast<std::uint8_t>(card.maximum_horizon + 1U);
  out.source[0] = rational::make(2);
  for (std::uint8_t n = 1; n <= card.maximum_horizon; ++n) {
    std::int64_t next[4]{};
    next[0] = state[0]*matrix[0] + state[1]*matrix[2];
    next[1] = state[0]*matrix[1] + state[1]*matrix[3];
    next[2] = state[2]*matrix[0] + state[3]*matrix[2];
    next[3] = state[2]*matrix[1] + state[3]*matrix[3];
    for (std::uint8_t i = 0; i < 4; ++i) state[i] = next[i];
    out.source[n] = rational::make(state[0] + state[3]);
  }
}

HOLONICS_CALLABLE inline void derive_carrier(const signed_carrier_card &card,
    const cultivated_shift_organ &organ, tail_receipt &out) noexcept {
  carrier_stream(card, card.matrix, out); static_cast<void>(predict(&organ, out, 2, 0));
  std::int16_t changed_matrix[4]{};
  for (std::uint8_t i = 0; i < 4; ++i) changed_matrix[i] = card.matrix[i];
  changed_matrix[card.changed_slot] = card.changed_value;
  tail_receipt changed{}; carrier_stream(card, changed_matrix, changed);
  out.changed_source = predict(&organ, changed, 2, 0);
  tail_receipt short_tail{}; short_tail.sample_count = out.sample_count;
  out.short_prefix = predict(&organ, short_tail, 1, 0);
  out.exclusion = predict(nullptr, short_tail, 2, 0);
}

HOLONICS_CALLABLE inline void graded_stream(std::uint8_t generators,
    std::uint8_t horizon, tail_receipt &out) noexcept {
  out.sample_count = static_cast<std::uint8_t>(horizon + 1U);
  for (std::uint8_t n = 0; n <= horizon; ++n) {
    std::int64_t count = 0;
    for (std::uint8_t a = 0; a <= n; ++a) for (std::uint8_t b = 0; b <= n; ++b)
      for (std::uint8_t c = 0; c <= (generators == 3 ? n : 0); ++c)
        count += a + b + c <= n ? 1 : 0;
    out.source[n] = rational::make(count);
  }
}

HOLONICS_CALLABLE inline void derive_graded(const graded_structure_card &card,
    const cultivated_shift_organ &organ, tail_receipt &out) noexcept {
  graded_stream(card.generators, card.maximum_horizon, out);
  static_cast<void>(predict(&organ, out, 3, 0));
  tail_receipt changed{}; graded_stream(card.changed_generators, card.maximum_horizon, changed);
  out.changed_source = predict(&organ, changed, 3, 0);
  tail_receipt short_tail{}; short_tail.sample_count = out.sample_count;
  out.short_prefix = predict(&organ, short_tail, 2, 0);
  out.exclusion = predict(nullptr, short_tail, 3, 0);
}

HOLONICS_CALLABLE inline void close(heldout_application_receipt &out) noexcept {
  out.all_exact = true;
  for (std::uint8_t i = 0; i < cultivation_family_count; ++i)
    out.all_exact = out.all_exact && out.tails[i].exact &&
      out.tails[i].changed_source == cultivation_obstruction::heldout_residual &&
      out.tails[i].short_prefix == cultivation_obstruction::insufficient_prefix &&
      out.tails[i].exclusion == cultivation_obstruction::organ_absent;
  out.development_sources_absent = true; out.identity_ablation_exact = out.all_exact;
  out.passage = exact::word{198'401}; out.lineage = exact::word{510'132};
  out.theory_formed = out.structure_ports_distinct && out.development_sources_absent && out.all_exact;
}

}  // namespace holonics::organ::cultivated_application_detail
