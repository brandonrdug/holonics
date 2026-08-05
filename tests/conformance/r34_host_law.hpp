#pragma once

#include <algorithm>
#include <array>
#include <numeric>

#include "r34_host_model.hpp"

namespace r34_host {
struct Rat {
  std::int64_t n{};
  std::int64_t d{1};
};
inline Rat rat(std::int64_t n, std::int64_t d = 1) {
  if (d < 0) {
    n = -n;
    d = -d;
  }
  const auto g = std::gcd(n, d);
  return {n / g, d / g};
}
inline Rat add(Rat a, Rat b) { return rat(a.n * b.d + b.n * a.d, a.d * b.d); }
inline Rat sub(Rat a, Rat b) { return add(a, {-b.n, b.d}); }
inline Rat mul(Rat a, Rat b) { return rat(a.n * b.n, a.d * b.d); }
inline Rat div(Rat a, Rat b) { return rat(a.n * b.d, a.d * b.n); }
using Exponent = std::array<std::uint8_t, 6>;
inline std::vector<Exponent> exponents() {
  std::vector<Exponent> out{};
  for (std::uint8_t total = 0; total <= 3; ++total)
    for (std::uint8_t a = 0; a <= total; ++a)
      for (std::uint8_t b = 0; b <= total - a; ++b)
        for (std::uint8_t c = 0; c <= total - a - b; ++c)
          for (std::uint8_t d = 0; d <= total - a - b - c; ++d)
            for (std::uint8_t e = 0; e <= total - a - b - c - d; ++e)
              out.push_back({a, b, c, d, e,
                             static_cast<std::uint8_t>(total - a - b - c - d - e)});
  return out;
}
inline std::int64_t power(std::int64_t value, std::uint8_t exponent) {
  std::int64_t out = 1;
  for (std::uint8_t i = 0; i < exponent; ++i)
    out *= value;
  return out;
}
inline std::array<std::int64_t, 84> monomials(const Triple &t) {
  std::array<std::int64_t, 84> out{};
  const auto all = exponents();
  for (std::size_t i = 0; i < all.size(); ++i) {
    out[i] = 1;
    for (std::size_t j = 0; j < 6; ++j)
      out[i] *= power(t.lower[j], all[i][j]);
  }
  return out;
}
enum class Mode : std::uint8_t { complete, degree_two, delete_sixth, delete_target };
inline bool admitted(std::size_t column, Mode mode) {
  if (column == 84)
    return mode != Mode::delete_target;
  const auto e = exponents()[column];
  const auto degree = std::accumulate(e.begin(), e.end(), std::uint8_t{0});
  return mode == Mode::degree_two ? degree <= 2
       : mode == Mode::delete_sixth ? e[5] == 0 : true;
}
inline std::uint8_t feature_count(Mode mode) {
  std::uint8_t count = 0;
  for (std::size_t i = 0; i < 85; ++i)
    count = static_cast<std::uint8_t>(count + (admitted(i, mode) ? 1U : 0U));
  return count;
}
struct Basis {
  std::array<std::array<Rat, 85>, 85> rows{};
  std::array<std::uint8_t, 85> pivots{};
  std::uint8_t rank{};
};
inline bool insert(Basis &basis, const Triple &t, std::uint8_t target, Mode mode) {
  const auto m = monomials(t);
  std::array<Rat, 85> row{};
  std::uint8_t count = 0;
  for (std::size_t i = 0; i < 85; ++i)
    if (admitted(i, mode))
      row[count++] = rat(i == 84 ? t.symmetric[target] : m[i]);
  for (std::uint8_t r = 0; r < basis.rank; ++r) {
    const auto p = basis.pivots[r];
    const auto factor = row[p];
    if (factor.n == 0)
      continue;
    for (std::uint8_t c = p; c < count; ++c)
      row[c] = sub(row[c], mul(factor, basis.rows[r][c]));
  }
  std::uint8_t pivot = 0;
  while (pivot < count && row[pivot].n == 0)
    ++pivot;
  if (pivot == count)
    return false;
  const auto divisor = row[pivot];
  for (std::uint8_t c = pivot; c < count; ++c)
    row[c] = div(row[c], divisor);
  for (std::uint8_t r = 0; r < basis.rank; ++r) {
    const auto factor = basis.rows[r][pivot];
    if (factor.n == 0)
      continue;
    for (std::uint8_t c = pivot; c < count; ++c)
      basis.rows[r][c] = sub(basis.rows[r][c], mul(factor, row[c]));
  }
  std::uint8_t at = 0;
  while (at < basis.rank && basis.pivots[at] < pivot)
    ++at;
  for (std::uint8_t r = basis.rank; r > at; --r) {
    basis.pivots[r] = basis.pivots[r - 1U];
    basis.rows[r] = basis.rows[r - 1U];
  }
  basis.pivots[at] = pivot;
  basis.rows[at] = row;
  ++basis.rank;
  return true;
}
struct Candidate {
  std::array<std::int64_t, 85> coefficients{};
  std::uint16_t rows{};
  std::uint8_t features{}, rank{}, nullity{}, target{}, mode{}, obstruction{};
  bool selected{};
};
inline Candidate candidate(const std::vector<Triple> &triples, std::size_t base,
                           std::uint16_t rows, std::uint8_t target, Mode mode) {
  Candidate out{};
  out.rows = rows;
  out.features = feature_count(mode);
  out.target = target;
  out.mode = static_cast<std::uint8_t>(mode);
  Basis basis{};
  const auto wanted = mode == Mode::complete
                          ? static_cast<std::uint8_t>(out.features - 1U)
                          : out.features;
  for (std::uint16_t i = 0; i < rows && basis.rank < wanted; ++i)
    insert(basis, triples[base + i], target, mode);
  out.rank = basis.rank;
  out.nullity = static_cast<std::uint8_t>(out.features - out.rank);
  if (rows < out.features - 1U) {
    out.obstruction = 1;
    return out;
  }
  if (out.nullity == 0) {
    out.obstruction = 2;
    return out;
  }
  if (out.nullity != 1) {
    out.obstruction = 3;
    return out;
  }
  std::array<bool, 85> pivot{};
  for (std::uint8_t r = 0; r < basis.rank; ++r)
    pivot[basis.pivots[r]] = true;
  std::uint8_t free = 0;
  while (free < out.features && pivot[free])
    ++free;
  std::array<Rat, 85> vector{};
  for (auto &value : vector)
    value = rat(0);
  vector[free] = rat(1);
  for (std::uint8_t r = 0; r < basis.rank; ++r)
    vector[basis.pivots[r]] = {-basis.rows[r][free].n, basis.rows[r][free].d};
  std::int64_t common = 1, divisor = 0;
  for (std::uint8_t i = 0; i < out.features; ++i)
    common = std::lcm(common, vector[i].d);
  std::uint8_t reduced = 0;
  for (std::size_t column = 0; column < 85; ++column)
    if (admitted(column, mode)) {
      out.coefficients[column] = vector[reduced].n * (common / vector[reduced].d);
      divisor = std::gcd(divisor, out.coefficients[column]);
      ++reduced;
    }
  for (auto &value : out.coefficients)
    value /= divisor;
  const auto first = std::find_if(out.coefficients.begin(), out.coefficients.end(),
                                  [](std::int64_t value) { return value != 0; });
  if (first != out.coefficients.end() && *first < 0)
    for (auto &value : out.coefficients)
      value = -value;
  return out;
}
} // namespace r34_host
