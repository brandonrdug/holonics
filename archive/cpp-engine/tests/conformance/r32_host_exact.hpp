#pragma once

#include <cstdint>
#include <fstream>
#include <numeric>
#include <sstream>
#include <string>
#include <vector>

namespace r32_host {

using numbers = std::vector<std::int64_t>;

[[nodiscard]] inline numbers read_numbers(const char* path) {
  std::ifstream input{path};
  numbers result{};
  std::int64_t value = 0;
  while (input >> value) result.push_back(value);
  return result;
}

[[nodiscard]] inline std::string read_bytes(const char* path) {
  std::ifstream input{path, std::ios::binary};
  std::ostringstream bytes{};
  bytes << input.rdbuf();
  return bytes.str();
}

struct matrix2 final { std::int64_t v[4]{}; };

[[nodiscard]] inline matrix2 matrix_at(const numbers& source, std::size_t offset) {
  return {{source[offset], source[offset + 1U], source[offset + 2U], source[offset + 3U]}};
}

[[nodiscard]] inline matrix2 multiply(const matrix2& x, const matrix2& y) {
  return {{x.v[0]*y.v[0]+x.v[1]*y.v[2], x.v[0]*y.v[1]+x.v[1]*y.v[3],
           x.v[2]*y.v[0]+x.v[3]*y.v[2], x.v[2]*y.v[1]+x.v[3]*y.v[3]}};
}

[[nodiscard]] inline matrix2 subtract(const matrix2& x, const matrix2& y) {
  return {{x.v[0]-y.v[0],x.v[1]-y.v[1],x.v[2]-y.v[2],x.v[3]-y.v[3]}};
}

[[nodiscard]] inline matrix2 inverse_unimodular(const matrix2& x) {
  return {{x.v[3],-x.v[1],-x.v[2],x.v[0]}};
}

[[nodiscard]] inline std::vector<std::int64_t> traces(const matrix2& generator,
    std::size_t count) {
  matrix2 state{{1,0,0,1}};
  std::vector<std::int64_t> result{};
  for (std::size_t i = 0; i < count; ++i) {
    result.push_back(state.v[0] + state.v[3]);
    state = multiply(state, generator);
  }
  return result;
}

struct rational final { std::int64_t n{}; std::int64_t d{1}; };

[[nodiscard]] inline rational reduced(std::int64_t n, std::int64_t d = 1) {
  if (d < 0) { n = -n; d = -d; }
  const auto divisor = std::gcd(n, d);
  return {n / divisor, d / divisor};
}

[[nodiscard]] inline rational difference(rational x, rational y) {
  return reduced(x.n*y.d-y.n*x.d,x.d*y.d);
}

[[nodiscard]] inline rational quotient(rational x, rational y) {
  return reduced(x.n*y.d,x.d*y.n);
}

[[nodiscard]] inline rational product(rational x, rational y) {
  return reduced(x.n*y.n,x.d*y.d);
}

[[nodiscard]] inline std::size_t rank(std::vector<std::vector<rational>> matrix) {
  std::size_t pivot_row = 0;
  const auto columns = matrix.empty() ? 0U : matrix.front().size();
  for (std::size_t column = 0; column < columns && pivot_row < matrix.size(); ++column) {
    std::size_t pivot = pivot_row;
    while (pivot < matrix.size() && matrix[pivot][column].n == 0) ++pivot;
    if (pivot == matrix.size()) continue;
    if (pivot != pivot_row) std::swap(matrix[pivot],matrix[pivot_row]);
    const auto divisor = matrix[pivot_row][column];
    for (std::size_t slot = column; slot < columns; ++slot)
      matrix[pivot_row][slot] = quotient(matrix[pivot_row][slot],divisor);
    for (std::size_t row = 0; row < matrix.size(); ++row) {
      if (row == pivot_row) continue;
      const auto factor = matrix[row][column];
      for (std::size_t slot = column; slot < columns; ++slot)
        matrix[row][slot] = difference(matrix[row][slot],product(factor,matrix[pivot_row][slot]));
    }
    ++pivot_row;
  }
  return pivot_row;
}

[[nodiscard]] inline std::size_t recurrence_rank(const std::vector<std::int64_t>& trace,
    std::size_t order) {
  std::vector<std::vector<rational>> rows(trace.size()-order,
      std::vector<rational>(order+1U));
  for (std::size_t row = 0; row < rows.size(); ++row)
    for (std::size_t column = 0; column <= order; ++column)
      rows[row][column] = reduced(trace[row+column]);
  return rank(rows);
}

[[nodiscard]] inline std::vector<std::int64_t> order_two_kernel(
    const std::vector<std::int64_t>& trace) {
  std::vector<std::int64_t> result{
    trace[1]*trace[3]-trace[2]*trace[2],
    trace[2]*trace[1]-trace[0]*trace[3],
    trace[0]*trace[2]-trace[1]*trace[1]};
  std::int64_t divisor = 0;
  for (const auto value : result) divisor = std::gcd(divisor,value);
  for (auto& value : result) value /= divisor;
  if (result[0] < 0) for (auto& value : result) value = -value;
  return result;
}

}  // namespace r32_host
