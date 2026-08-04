#pragma once

#include <holonics/organ/cm_arithmetic_exact.hpp>

namespace holonics::organ::cm_characteristic_detail {

HOLONICS_CALLABLE constexpr bool matrix_product(
    const std::int64_t left[cm_point_capacity][cm_point_capacity],
    const std::uint8_t right[cm_point_capacity][cm_point_capacity],
    std::int64_t out[cm_point_capacity][cm_point_capacity]) noexcept {
  bool exact = true;
  for (std::uint8_t row = 0; row < cm_point_capacity; ++row) {
    for (std::uint8_t column = 0; column < cm_point_capacity; ++column) {
      std::int64_t sum = 0;
      for (std::uint8_t inner = 0; inner < cm_point_capacity; ++inner) {
        std::int64_t product = 0;
        std::int64_t next = 0;
        exact = exact && blind_integer_detail::multiply(
            left[row][inner], right[inner][column], product) &&
            blind_integer_detail::add(sum, product, next);
        sum = next;
      }
      out[row][column] = sum;
    }
  }
  return exact;
}

HOLONICS_CALLABLE constexpr bool characteristic(cm_graph_receipt& graph) noexcept {
  std::int64_t power[cm_point_capacity][cm_point_capacity]{};
  for (std::uint8_t row = 0; row < cm_point_capacity; ++row) {
    for (std::uint8_t column = 0; column < cm_point_capacity; ++column) {
      power[row][column] = graph.adjacency[row][column];
    }
  }
  bool exact = true;
  for (std::uint8_t order = 0; order < cm_point_capacity; ++order) {
    std::int64_t trace = 0;
    for (std::uint8_t diagonal = 0; diagonal < cm_point_capacity; ++diagonal) {
      std::int64_t next = 0;
      exact = exact && blind_integer_detail::add(
          trace, power[diagonal][diagonal], next);
      trace = next;
    }
    graph.traces[order] = trace;
    if (order + 1U < cm_point_capacity) {
      std::int64_t next[cm_point_capacity][cm_point_capacity]{};
      exact = exact && matrix_product(power, graph.adjacency, next);
      for (std::uint8_t row = 0; row < cm_point_capacity; ++row) {
        for (std::uint8_t column = 0; column < cm_point_capacity; ++column) {
          power[row][column] = next[row][column];
        }
      }
    }
  }
  graph.characteristic[0] = 1;
  for (std::uint8_t degree = 1; degree <= cm_point_capacity; ++degree) {
    std::int64_t sum = 0;
    for (std::uint8_t index = 1; index <= degree; ++index) {
      std::int64_t product = 0;
      std::int64_t next = 0;
      exact = exact && blind_integer_detail::multiply(
          graph.characteristic[degree - index], graph.traces[index - 1U], product) &&
          blind_integer_detail::add(sum, product, next);
      sum = next;
    }
    std::int64_t quotient = 0;
    exact = exact && blind_integer_detail::divide_exact(
        -sum, static_cast<std::int64_t>(degree), quotient);
    graph.characteristic[degree] = quotient;
  }
  graph.characteristic_exact = exact;
  return exact;
}

HOLONICS_CALLABLE constexpr bool remove_linear(std::int64_t* polynomial,
    std::uint8_t& degree, std::int64_t root) noexcept {
  if (degree == 0) { return false; }
  std::int64_t quotient[cm_characteristic_capacity]{};
  quotient[0] = polynomial[0];
  bool exact = true;
  for (std::uint8_t slot = 1; slot <= degree; ++slot) {
    std::int64_t product = 0;
    exact = exact && blind_integer_detail::multiply(quotient[slot - 1U], root, product) &&
        blind_integer_detail::add(polynomial[slot], product, quotient[slot]);
  }
  if (!exact || quotient[degree] != 0) { return false; }
  --degree;
  for (std::uint8_t slot = 0; slot <= degree; ++slot) { polynomial[slot] = quotient[slot]; }
  polynomial[degree + 1U] = 0;
  return true;
}

HOLONICS_CALLABLE constexpr bool divide_quadratic(const std::int64_t* polynomial,
    std::uint8_t degree, std::int64_t linear, std::int64_t constant,
    std::int64_t* quotient) noexcept {
  if (degree < 2) { return false; }
  std::int64_t remainder[cm_characteristic_capacity]{};
  for (std::uint8_t slot = 0; slot <= degree; ++slot) { remainder[slot] = polynomial[slot]; }
  bool exact = true;
  for (std::uint8_t slot = 0; slot + 2U <= degree; ++slot) {
    quotient[slot] = remainder[slot];
    std::int64_t first = 0;
    std::int64_t second = 0;
    exact = exact && blind_integer_detail::multiply(quotient[slot], linear, first) &&
        blind_integer_detail::multiply(quotient[slot], constant, second) &&
        blind_integer_detail::subtract(remainder[slot + 1U], first,
            remainder[slot + 1U]) &&
        blind_integer_detail::subtract(remainder[slot + 2U], second,
            remainder[slot + 2U]);
  }
  return exact && remainder[degree - 1U] == 0 && remainder[degree] == 0;
}

HOLONICS_CALLABLE constexpr bool factor(cm_graph_receipt& graph,
    std::int16_t aperture_min, std::int16_t aperture_max) noexcept {
  std::int64_t remaining[cm_characteristic_capacity]{};
  for (std::uint8_t slot = 0; slot < cm_characteristic_capacity; ++slot) {
    remaining[slot] = graph.characteristic[slot];
  }
  std::uint8_t degree = cm_point_capacity;
  for (std::int16_t root = aperture_min; root <= aperture_max; ++root) {
    std::uint8_t multiplicity = 0;
    while (remove_linear(remaining, degree, root)) { ++multiplicity; }
    if (multiplicity != 0) {
      auto& value = graph.factors[graph.factor_count++];
      value.coefficients[0] = 1;
      value.coefficients[1] = -root;
      value.degree = 1;
      value.multiplicity = multiplicity;
      value.exact = true;
    }
  }
  if (degree == 0) { return graph.factor_count != 0; }
  for (std::int16_t linear = aperture_min; linear <= aperture_max; ++linear) {
    for (std::int16_t constant = aperture_min; constant <= aperture_max; ++constant) {
      std::int64_t quotient[cm_characteristic_capacity]{};
      if (!divide_quadratic(remaining, degree, linear, constant, quotient)) { continue; }
      auto& quadratic = graph.factors[graph.factor_count++];
      quadratic.coefficients[0] = 1;
      quadratic.coefficients[1] = linear;
      quadratic.coefficients[2] = constant;
      quadratic.degree = 2;
      quadratic.multiplicity = 1;
      quadratic.exact = true;
      auto& residual = graph.factors[graph.factor_count++];
      residual.degree = static_cast<std::uint8_t>(degree - 2U);
      residual.multiplicity = 1;
      residual.exact = true;
      for (std::uint8_t slot = 0; slot <= residual.degree; ++slot) {
        residual.coefficients[slot] = quotient[slot];
      }
      return true;
    }
  }
  return false;
}

}  // namespace holonics::organ::cm_characteristic_detail
