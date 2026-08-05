#include "r31_host_reference.hpp"

namespace holonics::tests {
namespace rational = exact::small_rational_law;
namespace {
[[nodiscard]] std::int64_t power(std::int64_t n, std::uint8_t p) noexcept {
  std::int64_t result = 1; while (p-- != 0) result *= n; return result;
}
std::uint8_t rank(exact::small_rational (&a)[28][12], std::uint8_t rows,
    std::uint8_t columns, std::uint8_t (&pivots)[12]) noexcept {
  std::uint8_t r = 0;
  for (std::uint8_t c = 0; c < columns && r < rows; ++c) {
    std::uint8_t p = r; while (p < rows && a[p][c].numerator == 0) ++p;
    if (p == rows) continue;
    for (std::uint8_t k = 0; k < columns; ++k) { const auto x = a[p][k]; a[p][k] = a[r][k]; a[r][k] = x; }
    const auto divisor = a[r][c];
    for (std::uint8_t k = c; k < columns; ++k) a[r][k] = rational::divide(a[r][k], divisor);
    for (std::uint8_t q = 0; q < rows; ++q) if (q != r) {
      const auto factor = a[q][c];
      for (std::uint8_t k = c; k < columns; ++k)
        a[q][k] = rational::subtract(a[q][k], rational::multiply(factor, a[r][k]));
    }
    pivots[r++] = c;
  }
  return r;
}
void kernel(exact::small_rational (&a)[28][12], organ::feature_geometry_receipt &out) noexcept {
  bool pivot[12]{}; for (std::uint8_t i = 0; i < out.rank; ++i) pivot[out.pivot_columns[i]] = true;
  std::uint8_t free = 0; while (pivot[free]) ++free;
  exact::small_rational vector[12]{}; for (auto &x : vector) x = rational::make(0);
  vector[free] = rational::make(1);
  for (std::uint8_t i = 0; i < out.rank; ++i) vector[out.pivot_columns[i]] = rational::negate(a[i][free]);
  std::int64_t common = 1;
  for (std::uint8_t i = 0; i < out.features; ++i)
    common = rational::quotient(common * vector[i].denominator, rational::gcd(common, vector[i].denominator));
  std::int64_t divisor = 0;
  for (std::uint8_t i = 0; i < out.features; ++i) {
    out.coefficients[i] = vector[i].numerator * rational::quotient(common, vector[i].denominator);
    divisor = rational::gcd(divisor, out.coefficients[i]);
  }
  for (std::uint8_t i = 0; i < out.features; ++i) out.coefficients[i] = rational::quotient(out.coefficients[i], divisor);
  std::uint8_t first = 0; while (out.coefficients[first] == 0) ++first;
  if (out.coefficients[first] < 0) for (std::uint8_t i = 0; i < out.features; ++i) out.coefficients[i] *= -1;
  out.primitive = true;
}
}  // namespace

organ::feature_geometry_receipt r31_reference_candidate(
    const organ::developmental_stream_card &card, std::uint8_t order,
    std::uint8_t degree) noexcept {
  organ::feature_geometry_receipt out{}; exact::small_rational matrix[28][12]{};
  out.order = order; out.degree = degree; out.features = static_cast<std::uint8_t>((order+1U)*(degree+1U));
  for (std::uint8_t s = 0; s < card.series_count; ++s)
    for (std::uint8_t n = 0; n + order < card.sample_count[s]; ++n) {
      std::uint8_t column = 0;
      for (std::uint8_t shift = 0; shift <= order; ++shift) for (std::uint8_t p = 0; p <= degree; ++p)
        matrix[out.rows][column++] = rational::multiply(rational::make(power(n,p)), card.samples[s][n+shift]);
      ++out.rows;
    }
  if (out.rows < out.features - 1U) { out.obstruction = organ::cultivation_obstruction::insufficient_rows; return out; }
  out.rank = rank(matrix, out.rows, out.features, out.pivot_columns);
  out.nullity = static_cast<std::uint8_t>(out.features - out.rank);
  if (out.nullity == 0) out.obstruction = organ::cultivation_obstruction::full_rank;
  else if (out.nullity != 1) out.obstruction = organ::cultivation_obstruction::nonunique_kernel;
  else { kernel(matrix, out); out.obstruction = organ::cultivation_obstruction::none; }
  return out;
}

}  // namespace holonics::tests
