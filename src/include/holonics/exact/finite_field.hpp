#pragma once

#include <cstddef>

#include <holonics/exact/residue.hpp>

namespace holonics::exact {

template<std::size_t Capacity>
class prime_field_element final {
 public:
  using holonics_exact_carrier = exact_carrier_marker;

  [[nodiscard]] HOLONICS_CALLABLE static constexpr checked_result<prime_field_element> admitted(
      unsigned_integer<Capacity> value,
      unsigned_integer<Capacity> declared_prime) noexcept {
    checked_result<prime_field_element> result{};
    const auto reduced_value = residue<Capacity>::reduced(value, declared_prime);
    result.receipt = reduced_value.receipt;
    if (reduced_value.accepted()) {
      result.value.value_ = reduced_value.value;
    }
    return result;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr const residue<Capacity>& value() const noexcept {
    return value_;
  }

 private:
  residue<Capacity> value_{};
};

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr checked_result<prime_field_element<Capacity>> multiply(
    const prime_field_element<Capacity>& left,
    const prime_field_element<Capacity>& right) noexcept {
  checked_result<prime_field_element<Capacity>> result{};
  const auto product = exact::multiply(left.value(), right.value());
  result.receipt = product.receipt;
  if (product.accepted()) {
    result = prime_field_element<Capacity>::admitted(
        product.value.value(), product.value.modulus());
  }
  return result;
}

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr checked_result<prime_field_element<Capacity>> inverse(
    const prime_field_element<Capacity>& value) noexcept {
  checked_result<prime_field_element<Capacity>> result{};
  result.receipt.admitted_limbs = static_cast<std::uint16_t>(Capacity);
  const auto one = unsigned_integer<Capacity>::from_word(1);
  const auto exponent_difference = subtract(value.value().modulus(),
                                             unsigned_integer<Capacity>::from_word(2));
  if (!exponent_difference.accepted() || value.value().value().is_zero()) {
    result.receipt.state = status::noninvertible;
    return result;
  }
  unsigned_integer<Capacity> exponent = exponent_difference.value;
  auto factor = value;
  auto accumulator = prime_field_element<Capacity>::admitted(one, value.value().modulus());
  while (!exponent.is_zero()) {
    if (exponent.bit(0)) {
      accumulator = multiply(accumulator.value, factor);
      if (!accumulator.accepted()) {
        return accumulator;
      }
    }
    exponent = shift_right(exponent, 1);
    if (!exponent.is_zero()) {
      const auto squared = multiply(factor, factor);
      if (!squared.accepted()) {
        return squared;
      }
      factor = squared.value;
    }
  }
  return accumulator;
}

static_assert(exact_carrier<prime_field_element<2>>);

}  // namespace holonics::exact
