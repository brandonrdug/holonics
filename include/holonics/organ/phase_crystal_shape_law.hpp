#pragma once

#include <holonics/organ/phase_crystal_geometry.hpp>

namespace holonics::organ::phase_crystal_detail {

struct shape_entry final {
  phase_ratio first{};
  phase_ratio second{};
  std::uint16_t population{};
};

struct transition_entry final {
  phase_ratio first{};
  phase_ratio second{};
  phase_ratio next_first{};
  phase_ratio next_second{};
  std::uint16_t population{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr bool ratio_equal(
    phase_ratio left, phase_ratio right) noexcept {
  return left.numerator == right.numerator && left.denominator == right.denominator;
}

HOLONICS_CALLABLE constexpr void fold_ratio(std::uint64_t& fold, phase_ratio value) noexcept {
  fold ^= magnitude(value.numerator) + 0x9e37'79b9U + (fold << 6U) + (fold >> 2U);
  fold ^= value.denominator + 0x85eb'ca6bU + (fold << 6U) + (fold >> 2U);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool factor_side_lengths(
    std::uint16_t modulus, phase_ratio* lengths, std::uint16_t& types,
    phase_ratio& shortest, phase_ratio& longest) noexcept {
  bool exact = true;
  types = 0;
  for (std::uint16_t residue = 0; residue < modulus; ++residue) {
    phase_case_definition factor{modulus, 2, 1, 1, phase_case_kind::prime_pair, false, false};
    phase_point left{};
    phase_point right{};
    const auto next = static_cast<std::uint16_t>(residue + 1U == modulus ? 0U : residue + 1U);
    if (!project_point(factor, residue, 0, left) ||
        !project_point(factor, next, 0, right) ||
        !squared_distance(left, right, lengths[residue])) { return false; }
    if (residue == 0 || compare(lengths[residue], shortest, exact) < 0) {
      shortest = lengths[residue];
    }
    if (residue == 0 || compare(lengths[residue], longest, exact) > 0) {
      longest = lengths[residue];
    }
    bool seen = false;
    for (std::uint16_t prior = 0; prior < residue; ++prior) {
      seen = seen || ratio_equal(lengths[prior], lengths[residue]);
    }
    types = static_cast<std::uint16_t>(types + (seen ? 0U : 1U));
  }
  return exact;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool shape_distribution(
    const phase_case_definition& definition, phase_case_receipt& receipt) noexcept {
  phase_ratio first_lengths[19]{};
  phase_ratio second_lengths[19]{};
  if (!factor_side_lengths(definition.first_modulus, first_lengths,
          receipt.first_edge_types, receipt.first_shortest_side, receipt.first_longest_side) ||
      !factor_side_lengths(definition.second_modulus, second_lengths,
          receipt.second_edge_types, receipt.second_shortest_side, receipt.second_longest_side)) {
    return false;
  }
  shape_entry shapes[phase_crystal_point_capacity]{};
  std::uint16_t shape_count = 0;
  for (std::uint16_t first = 0; first < definition.first_modulus; ++first) {
    for (std::uint16_t second = 0; second < definition.second_modulus; ++second) {
      std::uint16_t found = shape_count;
      for (std::uint16_t slot = 0; slot < shape_count; ++slot) {
        if (ratio_equal(shapes[slot].first, first_lengths[first]) &&
            ratio_equal(shapes[slot].second, second_lengths[second])) { found = slot; break; }
      }
      if (found == shape_count) {
        shapes[shape_count] = {first_lengths[first], second_lengths[second], 0};
        ++shape_count;
      }
      ++shapes[found].population;
    }
  }
  transition_entry transitions[phase_crystal_point_capacity]{};
  std::uint16_t transition_count = 0;
  for (std::uint16_t first = 0; first < definition.first_modulus; ++first) {
    for (std::uint16_t second = 0; second < definition.second_modulus; ++second) {
      const auto next_first = static_cast<std::uint16_t>(first + 1U ==
          definition.first_modulus ? 0U : first + 1U);
      const auto next_second = static_cast<std::uint16_t>(second + 1U ==
          definition.second_modulus ? 0U : second + 1U);
      std::uint16_t found = transition_count;
      for (std::uint16_t slot = 0; slot < transition_count; ++slot) {
        const auto& entry = transitions[slot];
        if (ratio_equal(entry.first, first_lengths[first]) &&
            ratio_equal(entry.second, second_lengths[second]) &&
            ratio_equal(entry.next_first, first_lengths[next_first]) &&
            ratio_equal(entry.next_second, second_lengths[next_second])) { found = slot; break; }
      }
      if (found == transition_count) {
        transitions[transition_count] = {first_lengths[first], second_lengths[second],
            first_lengths[next_first], second_lengths[next_second], 0};
        ++transition_count;
      }
      ++transitions[found].population;
    }
  }
  receipt.cell_shape_types = shape_count;
  receipt.shape_transition_types = transition_count;
  for (std::uint16_t slot = 0; slot < shape_count; ++slot) {
    if (shapes[slot].population > receipt.largest_shape_population) {
      receipt.largest_shape_population = shapes[slot].population;
    }
    fold_ratio(receipt.shape_population_fold, shapes[slot].first);
    fold_ratio(receipt.shape_population_fold, shapes[slot].second);
    receipt.shape_population_fold ^= shapes[slot].population;
  }
  for (std::uint16_t slot = 0; slot < transition_count; ++slot) {
    if (transitions[slot].population > receipt.largest_transition_population) {
      receipt.largest_transition_population = transitions[slot].population;
    }
    fold_ratio(receipt.transition_population_fold, transitions[slot].first);
    fold_ratio(receipt.transition_population_fold, transitions[slot].second);
    fold_ratio(receipt.transition_population_fold, transitions[slot].next_first);
    fold_ratio(receipt.transition_population_fold, transitions[slot].next_second);
    receipt.transition_population_fold ^= transitions[slot].population;
  }
  receipt.cell_population_factorized = shape_count ==
      receipt.first_edge_types * receipt.second_edge_types;
  receipt.chronology_distribution_exact = transition_count != 0;
  return receipt.cell_population_factorized && receipt.chronology_distribution_exact;
}

}  // namespace holonics::organ::phase_crystal_detail
