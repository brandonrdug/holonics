#pragma once

#include <cstddef>

#include <holonics/exact/integer_arithmetic.hpp>

namespace holonics::exact {

template<exact_carrier Coefficient, std::size_t Capacity>
class polynomial final {
  static_assert(Capacity > 0);

 public:
  using holonics_exact_carrier = exact_carrier_marker;
  using coefficient_type = Coefficient;
  static constexpr std::size_t capacity = Capacity;

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::size_t size() const noexcept { return size_; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const Coefficient& coefficient(
      std::size_t index) const noexcept {
    return coefficients_[index];
  }

  HOLONICS_CALLABLE constexpr void set_coefficient(
      std::size_t index,
      const Coefficient& value) noexcept {
    if (index >= Capacity) {
      return;
    }
    coefficients_[index] = value;
    if (size_ <= index) {
      size_ = index + 1;
    }
  }

 private:
  Coefficient coefficients_[Capacity]{};
  std::size_t size_{};
};

template<std::size_t LimbCapacity, std::size_t PolynomialCapacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr checked_result<
    polynomial<unsigned_integer<LimbCapacity>, PolynomialCapacity>> multiply(
    const polynomial<unsigned_integer<LimbCapacity>, PolynomialCapacity>& left,
    const polynomial<unsigned_integer<LimbCapacity>, PolynomialCapacity>& right) noexcept {
  using polynomial_type = polynomial<unsigned_integer<LimbCapacity>, PolynomialCapacity>;
  checked_result<polynomial_type> result{};
  result.receipt.admitted_limbs = static_cast<std::uint16_t>(LimbCapacity);
  if (left.size() == 0 || right.size() == 0) {
    return result;
  }
  const std::size_t required = left.size() + right.size() - 1;
  if (required > PolynomialCapacity) {
    result.receipt.state = status::degree_refused;
    result.receipt.required_limbs = static_cast<std::uint16_t>(required);
    return result;
  }
  for (std::size_t left_index = 0; left_index < left.size(); ++left_index) {
    for (std::size_t right_index = 0; right_index < right.size(); ++right_index) {
      const std::size_t output_index = left_index + right_index;
      const auto product = exact::multiply(
          left.coefficient(left_index), right.coefficient(right_index));
      if (!product.accepted()) {
        result.receipt = product.receipt;
        return result;
      }
      const auto sum = exact::add(
          result.value.coefficient(output_index), product.value);
      if (!sum.accepted()) {
        result.receipt = sum.receipt;
        return result;
      }
      result.value.set_coefficient(output_index, sum.value);
    }
  }
  result.receipt.required_limbs = static_cast<std::uint16_t>(required);
  return result;
}

static_assert(exact_carrier<polynomial<unsigned_integer<2>, 8>>);

}  // namespace holonics::exact
