#pragma once

#include <holonics/organ/cultivated_organ_receipt.hpp>

namespace holonics::organ::shift_cultivation_detail {
namespace rational = exact::small_rational_law;

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t power(
    std::int64_t base, std::uint8_t exponent) noexcept {
  std::int64_t result = 1;
  for (std::uint8_t i = 0; i < exponent; ++i) result *= base;
  return result;
}

HOLONICS_CALLABLE inline std::uint8_t form_rows(
    const developmental_stream_card &card, std::uint8_t order,
    std::uint8_t degree,
    exact::small_rational (&matrix)[cultivation_row_capacity]
                                    [cultivation_feature_capacity]) noexcept {
  std::uint8_t row = 0;
  for (std::uint8_t series = 0; series < card.series_count; ++series) {
    const auto count = card.sample_count[series];
    if (count <= order) continue;
    for (std::uint8_t n = 0; n + order < count; ++n) {
      std::uint8_t column = 0;
      for (std::uint8_t shift = 0; shift <= order; ++shift)
        for (std::uint8_t p = 0; p <= degree; ++p)
          matrix[row][column++] = rational::multiply(
              rational::make(power(n, p)), card.samples[series][n + shift]);
      ++row;
    }
  }
  return row;
}

HOLONICS_CALLABLE inline std::uint8_t reduce(
    exact::small_rational (&matrix)[cultivation_row_capacity]
                                    [cultivation_feature_capacity],
    std::uint8_t rows, std::uint8_t features,
    std::uint8_t (&pivots)[cultivation_feature_capacity]) noexcept {
  std::uint8_t rank = 0;
  for (std::uint8_t column = 0; column < features && rank < rows; ++column) {
    std::uint8_t pivot = rank;
    while (pivot < rows && matrix[pivot][column].numerator == 0) ++pivot;
    if (pivot == rows) continue;
    if (pivot != rank)
      for (std::uint8_t slot = 0; slot < features; ++slot) {
        const auto swap = matrix[pivot][slot];
        matrix[pivot][slot] = matrix[rank][slot]; matrix[rank][slot] = swap;
      }
    const auto divisor = matrix[rank][column];
    for (std::uint8_t slot = column; slot < features; ++slot)
      matrix[rank][slot] = rational::divide(matrix[rank][slot], divisor);
    for (std::uint8_t row = 0; row < rows; ++row) {
      if (row == rank) continue;
      const auto factor = matrix[row][column];
      for (std::uint8_t slot = column; slot < features; ++slot)
        matrix[row][slot] = rational::subtract(
            matrix[row][slot], rational::multiply(factor, matrix[rank][slot]));
    }
    pivots[rank++] = column;
  }
  return rank;
}

HOLONICS_CALLABLE inline bool primitive_kernel(
    exact::small_rational (&matrix)[cultivation_row_capacity]
                                    [cultivation_feature_capacity],
    feature_geometry_receipt &out) noexcept {
  bool pivot[cultivation_feature_capacity]{};
  for (std::uint8_t row = 0; row < out.rank; ++row)
    pivot[out.pivot_columns[row]] = true;
  std::uint8_t free_column = 0;
  while (free_column < out.features && pivot[free_column]) ++free_column;
  if (free_column == out.features) return false;
  exact::small_rational vector[cultivation_feature_capacity]{};
  for (auto &value : vector) value = rational::make(0);
  vector[free_column] = rational::make(1);
  for (std::uint8_t row = 0; row < out.rank; ++row)
    vector[out.pivot_columns[row]] = rational::negate(matrix[row][free_column]);
  std::int64_t common = 1;
  for (std::uint8_t i = 0; i < out.features; ++i)
    common = rational::quotient(common * vector[i].denominator,
        rational::gcd(common, vector[i].denominator));
  std::int64_t divisor = 0;
  for (std::uint8_t i = 0; i < out.features; ++i) {
    out.coefficients[i] = vector[i].numerator *
        rational::quotient(common, vector[i].denominator);
    divisor = rational::gcd(divisor, out.coefficients[i]);
  }
  for (std::uint8_t i = 0; i < out.features; ++i)
    out.coefficients[i] = rational::quotient(out.coefficients[i], divisor);
  std::uint8_t first = 0;
  while (first < out.features && out.coefficients[first] == 0) ++first;
  if (first == out.features) return false;
  if (out.coefficients[first] < 0)
    for (std::uint8_t i = 0; i < out.features; ++i)
      out.coefficients[i] = -out.coefficients[i];
  out.primitive = true;
  return true;
}

HOLONICS_CALLABLE inline void derive_candidate(
    const developmental_stream_card &card, std::uint8_t order,
    std::uint8_t degree,
    exact::small_rational (&matrix)[cultivation_row_capacity]
                                    [cultivation_feature_capacity],
    feature_geometry_receipt &out) noexcept {
  out.order = order; out.degree = degree;
  out.features = static_cast<std::uint8_t>((order + 1U) * (degree + 1U));
  out.rows = form_rows(card, order, degree, matrix);
  if (out.rows < out.features - 1U) {
    out.obstruction = cultivation_obstruction::insufficient_rows; return;
  }
  out.rank = reduce(matrix, out.rows, out.features, out.pivot_columns);
  out.nullity = static_cast<std::uint8_t>(out.features - out.rank);
  if (out.nullity == 0) { out.obstruction = cultivation_obstruction::full_rank; return; }
  if (out.nullity != 1) {
    out.obstruction = cultivation_obstruction::nonunique_kernel; return;
  }
  if (!primitive_kernel(matrix, out)) {
    out.obstruction = cultivation_obstruction::candidate_absent; return;
  }
  const auto base = static_cast<std::uint8_t>(order * (degree + 1U));
  bool forward = false;
  for (std::uint8_t p = 0; p <= degree; ++p)
    forward = forward || out.coefficients[base + p] != 0;
  out.obstruction = forward ? cultivation_obstruction::none :
      cultivation_obstruction::zero_forward_face;
}

HOLONICS_CALLABLE inline void derive_family(
    const developmental_stream_card &card,
    exact::small_rational (&matrix)[cultivation_row_capacity]
                                    [cultivation_feature_capacity],
    cultivation_family_receipt &out) noexcept {
  constexpr std::uint8_t orders[cultivation_candidate_count]{1,2,1,3,1,2,3,2,3};
  constexpr std::uint8_t degrees[cultivation_candidate_count]{0,0,1,0,2,1,1,2,2};
  out.candidate_count = cultivation_candidate_count;
  out.source_current_independent = card.metadata.parsed;
  bool selected = false;
  for (std::uint8_t i = 0; i < cultivation_candidate_count; ++i) {
    for (auto &row : matrix) for (auto &value : row) value = {};
    derive_candidate(card, orders[i], degrees[i], matrix, out.candidates[i]);
    if (!selected && out.candidates[i].obstruction == cultivation_obstruction::none) {
      out.candidates[i].selected = true; selected = true;
      auto &organ = out.candidate;
      organ.order = orders[i]; organ.degree = degrees[i]; organ.features = out.candidates[i].features;
      organ.minimum_prefix = orders[i]; organ.family = card.family;
      organ.primitive = true; organ.lineage = card.metadata.lineage;
      for (std::uint8_t k = 0; k < organ.features; ++k)
        organ.coefficients[k] = out.candidates[i].coefficients[k];
    }
  }
  out.selected_exact = selected;
}

}  // namespace holonics::organ::shift_cultivation_detail
