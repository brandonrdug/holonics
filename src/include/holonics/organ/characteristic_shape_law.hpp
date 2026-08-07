#pragma once

#include <holonics/organ/characteristic_exact.hpp>
#include <holonics/organ/phase_crystal_receipt.hpp>
#include <holonics/organ/phase_crystal_shape_law.hpp>

namespace holonics::organ::characteristic_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t locate_shape(
    const phase_crystal_detail::shape_entry* shapes, std::uint16_t shape_count,
    phase_ratio first, phase_ratio second) noexcept {
  for (std::uint16_t slot = 0; slot < shape_count; ++slot) {
    if (phase_crystal_detail::ratio_equal(shapes[slot].first, first) &&
        phase_crystal_detail::ratio_equal(shapes[slot].second, second)) { return slot; }
  }
  return shape_count;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool same_exponents(
    const std::uint16_t* left, const std::uint16_t* right,
    std::uint16_t count) noexcept {
  for (std::uint16_t slot = 0; slot < count; ++slot) {
    if (left[slot] != right[slot]) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool carry_shape_transport(
    characteristic_case_receipt& receipt) noexcept {
  const auto& definition = receipt.definition;
  phase_ratio first_lengths[19]{};
  phase_ratio second_lengths[19]{};
  phase_ratio shortest{};
  phase_ratio longest{};
  std::uint16_t first_types = 0;
  std::uint16_t second_types = 0;
  if (!phase_crystal_detail::factor_side_lengths(definition.first_modulus, first_lengths,
          first_types, shortest, longest) ||
      !phase_crystal_detail::factor_side_lengths(definition.second_modulus, second_lengths,
          second_types, shortest, longest)) { return false; }
  phase_crystal_detail::shape_entry shapes[characteristic_shape_capacity]{};
  std::uint16_t shape_count = 0;
  for (std::uint16_t first = 0; first < definition.first_modulus; ++first) {
    for (std::uint16_t second = 0; second < definition.second_modulus; ++second) {
      auto found = locate_shape(shapes, shape_count, first_lengths[first], second_lengths[second]);
      if (found == shape_count) {
        shapes[shape_count] = {first_lengths[first], second_lengths[second], 0};
        ++shape_count;
      }
      ++shapes[found].population;
    }
  }
  bool visited[characteristic_shape_capacity]{};
  std::uint16_t tour = 0;
  for (std::uint16_t first = 0; first < definition.first_modulus; ++first) {
    for (std::uint16_t second = 0; second < definition.second_modulus; ++second) {
      const auto start_index = static_cast<std::uint16_t>(
          first * definition.second_modulus + second);
      if (visited[start_index]) { continue; }
      if (tour >= characteristic_tour_capacity) { return false; }
      auto current_first = first;
      auto current_second = second;
      std::uint16_t length = 0;
      do {
        const auto index = static_cast<std::uint16_t>(
            current_first * definition.second_modulus + current_second);
        if (visited[index]) { return false; }
        visited[index] = true;
        const auto shape = locate_shape(shapes, shape_count, first_lengths[current_first],
            second_lengths[current_second]);
        if (shape >= shape_count) { return false; }
        ++receipt.shape_exponents[tour][shape];
        ++receipt.shape_exponent_total;
        ++length;
        current_first = static_cast<std::uint16_t>(current_first + 1U ==
            definition.first_modulus ? 0U : current_first + 1U);
        current_second = static_cast<std::uint16_t>(current_second + 1U ==
            definition.second_modulus ? 0U : current_second + 1U);
      } while (current_first != first || current_second != second);
      if (length != receipt.tour_length) { return false; }
      receipt.shape_tour_folds[tour] = fold_word(receipt.shape_exponents[tour], shape_count);
      ++tour;
    }
  }
  receipt.shape_types = shape_count;
  receipt.shape_tour_classes = 0;
  for (std::uint16_t current = 0; current < tour; ++current) {
    bool prior = false;
    for (std::uint16_t other = 0; other < current; ++other) {
      prior = prior || same_exponents(receipt.shape_exponents[current],
          receipt.shape_exponents[other], shape_count);
    }
    receipt.shape_tour_classes = static_cast<std::uint16_t>(
        receipt.shape_tour_classes + (prior ? 0U : 1U));
  }
  receipt.formal_shape_transport_exact = tour == receipt.tours &&
      shape_count == first_types * second_types &&
      receipt.shape_exponent_total == receipt.vertices;
  return receipt.formal_shape_transport_exact;
}

}  // namespace holonics::organ::characteristic_detail
