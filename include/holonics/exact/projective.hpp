#pragma once

#include <cstddef>

#include <holonics/exact/integer_arithmetic.hpp>

namespace holonics::exact {

template<exact_carrier Coordinate>
struct projective_pair final {
  using holonics_exact_carrier = exact_carrier_marker;

  Coordinate first{};
  Coordinate second{};
};

template<std::size_t Capacity>
struct projective_equality_result final {
  bool equal{};
  operation_receipt receipt{};
};

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr projective_equality_result<Capacity> projectively_equal(
    const projective_pair<unsigned_integer<Capacity>>& left,
    const projective_pair<unsigned_integer<Capacity>>& right) noexcept {
  projective_equality_result<Capacity> result{};
  result.receipt.admitted_limbs = static_cast<std::uint16_t>(Capacity);
  if ((left.first.is_zero() && left.second.is_zero()) ||
      (right.first.is_zero() && right.second.is_zero())) {
    result.receipt.state = status::invalid_projective_pair;
    return result;
  }
  const auto first_cross = multiply(left.first, right.second);
  const auto second_cross = multiply(left.second, right.first);
  if (!first_cross.accepted()) {
    result.receipt = first_cross.receipt;
    return result;
  }
  if (!second_cross.accepted()) {
    result.receipt = second_cross.receipt;
    return result;
  }
  result.equal = first_cross.value == second_cross.value;
  result.receipt.required_limbs = static_cast<std::uint16_t>(first_cross.value.used());
  return result;
}

static_assert(exact_carrier<projective_pair<unsigned_integer<2>>>);

}  // namespace holonics::exact
