#pragma once

#include <holonics/organ/blind_code_exact.hpp>

namespace holonics::organ {
namespace blind_code_detail {

HOLONICS_CALLABLE constexpr void form_code_population(
    const binary_code_problem_card& card, code_population_receipt& out) noexcept {
  out.identity = exact::word{189'400};
  out.lineage = card.lineage.value() + card.byte_fold;
  if (!card.parsed || card.dimension == 0 ||
      card.dimension > blind_cube_dimension_capacity || card.row_count == 0 ||
      card.row_count > blind_parity_row_capacity) { return; }
  out.vertex_count = static_cast<std::uint16_t>(1U << card.dimension);
  out.parity_enumerated = true;
  out.minimum_distance = card.dimension;
  for (std::uint16_t word = 0; word < out.vertex_count; ++word) {
    const auto narrow = static_cast<std::uint8_t>(word);
    if (!belongs(card, narrow)) { continue; }
    if (out.codeword_count >= blind_codeword_capacity) { return; }
    out.codewords[out.codeword_count++] = narrow;
    const auto distance = popcount(narrow);
    ++out.distance_distribution[distance];
    if (distance != 0 && distance < out.minimum_distance) { out.minimum_distance = distance; }
  }
  out.dual_moments_nonnegative = true;
  for (std::uint8_t degree = 0; degree <= card.dimension; ++degree) {
    std::int64_t numerator = 0;
    for (std::uint8_t distance = 0; distance <= card.dimension; ++distance) {
      out.krawtchouk[degree][distance] = krawtchouk(card.dimension, degree, distance);
      numerator += static_cast<std::int64_t>(out.distance_distribution[distance]) *
          out.krawtchouk[degree][distance];
    }
    out.dual_numerators[degree] = numerator;
    std::int64_t quotient = 0;
    const bool divisible = blind_integer_detail::divide_exact(
        numerator, static_cast<std::int64_t>(out.codeword_count), quotient);
    out.dual_distribution[degree] = divisible ? quotient : 0;
    out.dual_moments_nonnegative = out.dual_moments_nonnegative && divisible &&
        out.dual_distribution[degree] >= 0;
  }
  out.exact = out.vertex_count == (1U << card.dimension) && out.codeword_count != 0 &&
      out.distance_distribution[0] == 1 && out.dual_moments_nonnegative;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t distance_for_slot(
    const code_population_receipt& code, std::uint8_t dimension, std::uint8_t slot) noexcept {
  std::uint8_t seen = 0;
  for (std::uint8_t distance = 1; distance <= dimension; ++distance) {
    if (code.distance_distribution[distance] == 0) { continue; }
    if (seen == slot) { return distance; }
    ++seen;
  }
  return 0;
}

HOLONICS_CALLABLE constexpr void form_pair_incidence(const binary_code_problem_card& card,
    const code_population_receipt& code, std::uint8_t slot,
    pair_incidence_receipt& out) noexcept {
  out.identity = exact::word{189'410U + slot};
  out.source_word = 0;
  out.distance = distance_for_slot(code, card.dimension, slot);
  if (!code.exact || out.distance == 0) { return; }
  for (std::uint8_t index = 0; index < code.codeword_count; ++index) {
    if (popcount(code.codewords[index]) == out.distance) {
      out.target_word = code.codewords[index]; break;
    }
  }
  out.left_size = static_cast<std::uint8_t>(out.distance + 1U);
  out.right_size = static_cast<std::uint8_t>(card.dimension - out.distance + 1U);
  out.cell_count = static_cast<std::uint8_t>(out.left_size * out.right_size);
  out.lineage = card.lineage.value() + out.identity.value() + out.target_word;
  if (out.cell_count > blind_pair_cell_capacity) { return; }
  for (std::uint16_t word = 0; word < code.vertex_count; ++word) {
    ++out.population[cell_of(static_cast<std::uint8_t>(word), out.target_word,
        card.dimension, out.right_size)];
  }
  for (std::uint8_t cell = 0; cell < out.cell_count; ++cell) {
    std::uint8_t representative = 0;
    bool found = false;
    for (std::uint16_t word = 0; word < code.vertex_count; ++word) {
      if (cell_of(static_cast<std::uint8_t>(word), out.target_word, card.dimension,
              out.right_size) == cell) {
        representative = static_cast<std::uint8_t>(word); found = true; break;
      }
    }
    if (!found) { return; }
    for (std::uint8_t bit = 0; bit < card.dimension; ++bit) {
      const auto neighbor = static_cast<std::uint8_t>(representative ^ (1U << bit));
      const auto target = cell_of(neighbor, out.target_word, card.dimension, out.right_size);
      ++out.quotient[cell][target];
    }
  }
  out.equitable = true;
  for (std::uint16_t word = 0; word < code.vertex_count; ++word) {
    const auto source = cell_of(static_cast<std::uint8_t>(word), out.target_word,
        card.dimension, out.right_size);
    std::uint8_t counts[blind_pair_cell_capacity]{};
    for (std::uint8_t bit = 0; bit < card.dimension; ++bit) {
      const auto neighbor = static_cast<std::uint8_t>(word ^ (1U << bit));
      ++counts[cell_of(neighbor, out.target_word, card.dimension, out.right_size)];
    }
    for (std::uint8_t target = 0; target < out.cell_count; ++target) {
      out.equitable = out.equitable && counts[target] == out.quotient[source][target];
    }
  }
  out.detailed_balance = true;
  bool unit_grid = true;
  bool symmetric = true;
  bool product = true;
  for (std::uint8_t source = 0; source < out.cell_count; ++source) {
    std::uint64_t a_wide = 0;
    std::uint64_t b_wide = 0;
    if (!blind_integer_detail::divide_unsigned(
            source, out.right_size, a_wide, b_wide)) { return; }
    const auto a = static_cast<std::uint8_t>(a_wide);
    const auto b = static_cast<std::uint8_t>(b_wide);
    for (std::uint8_t target = 0; target < out.cell_count; ++target) {
      out.detailed_balance = out.detailed_balance &&
          static_cast<std::int64_t>(out.population[source]) * out.quotient[source][target] ==
          static_cast<std::int64_t>(out.population[target]) * out.quotient[target][source];
      symmetric = symmetric && out.quotient[source][target] == out.quotient[target][source];
      if (out.quotient[source][target] > 1) { unit_grid = false; }
      std::int16_t expected = 0;
      if (a > 0 && target == source - out.right_size) { expected = a; }
      if (a + 1U < out.left_size && target == source + out.right_size) {
        expected = static_cast<std::int16_t>(out.left_size - 1U - a);
      }
      if (b > 0 && target == source - 1U) { expected = b; }
      if (b + 1U < out.right_size && target == source + 1U) {
        expected = static_cast<std::int16_t>(out.right_size - 1U - b);
      }
      product = product && out.quotient[source][target] == expected;
    }
  }
  out.directions_commute = product;
  for (std::uint8_t degree = 0; degree < out.left_size; ++degree) {
    for (std::uint8_t position = 0; position < out.left_size; ++position) {
      out.left_krawtchouk[degree][position] =
          krawtchouk(static_cast<std::uint8_t>(out.left_size - 1U), degree, position);
    }
  }
  for (std::uint8_t degree = 0; degree < out.right_size; ++degree) {
    for (std::uint8_t position = 0; position < out.right_size; ++position) {
      out.right_krawtchouk[degree][position] =
          krawtchouk(static_cast<std::uint8_t>(out.right_size - 1U), degree, position);
    }
  }
  const std::uint8_t left_degree = out.left_size > 1 ? 1U : 0U;
  const std::uint8_t right_degree = out.right_size > 2 ? 2U : 0U;
  out.witness_eigenvalue = static_cast<std::int16_t>(card.dimension -
      2U * static_cast<std::uint8_t>(left_degree + right_degree));
  bool eigen_exact = true;
  for (std::uint8_t cell = 0; cell < out.cell_count; ++cell) {
    std::uint64_t a_wide = 0;
    std::uint64_t b_wide = 0;
    if (!blind_integer_detail::divide_unsigned(
            cell, out.right_size, a_wide, b_wide)) { return; }
    const auto a = static_cast<std::uint8_t>(a_wide);
    const auto b = static_cast<std::uint8_t>(b_wide);
    out.witness_vector[cell] = out.left_krawtchouk[left_degree][a] *
        out.right_krawtchouk[right_degree][b];
  }
  for (std::uint8_t row = 0; row < out.cell_count; ++row) {
    std::int64_t image = 0;
    for (std::uint8_t column = 0; column < out.cell_count; ++column) {
      image += out.quotient[row][column] * out.witness_vector[column];
    }
    eigen_exact = eigen_exact && image == out.witness_eigenvalue * out.witness_vector[row];
  }
  for (std::uint8_t total = 0; total <= card.dimension; ++total) {
    out.characteristic_roots[total] = static_cast<std::int16_t>(card.dimension - 2U * total);
    for (std::uint8_t left = 0; left < out.left_size; ++left) {
      const auto right = static_cast<std::int16_t>(total) - left;
      if (right >= 0 && right < out.right_size) { ++out.characteristic_multiplicity[total]; }
    }
  }
  std::uint8_t multiplicity = 0;
  for (std::uint8_t slot2 = 0; slot2 <= card.dimension; ++slot2) {
    multiplicity = static_cast<std::uint8_t>(multiplicity +
        out.characteristic_multiplicity[slot2]);
  }
  out.characteristic_exact = eigen_exact && multiplicity == out.cell_count;
  out.candidates[0] = {blind_candidate_kind::shell_collapse, exact::word{189'500U + slot},
      out.lineage + 1U, out.right_size == 1, true, out.right_size == 1, true, true,
      out.right_size == 1};
  out.candidates[1] = {blind_candidate_kind::unit_grid, exact::word{189'510U + slot},
      out.lineage + 2U, true, unit_grid, unit_grid, true, true, unit_grid};
  out.candidates[2] = {blind_candidate_kind::lineage_transpose,
      exact::word{189'520U + slot}, out.lineage + 3U, true, symmetric, symmetric, false,
      true, false};
  out.candidates[3] = {blind_candidate_kind::incidence_product,
      exact::word{189'530U + slot}, out.lineage + 4U, true, product, product, true, true,
      product};
  out.exact = out.equitable && out.detailed_balance && out.directions_commute &&
      out.characteristic_exact && out.candidates[3].admitted;
}

}  // namespace blind_code_detail
}  // namespace holonics::organ
