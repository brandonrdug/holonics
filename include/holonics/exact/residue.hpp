#pragma once

#include <cstddef>

#include <holonics/exact/integer_division.hpp>

namespace holonics::exact {

template<std::size_t Capacity>
class residue final {
 public:
  using holonics_exact_carrier = exact_carrier_marker;

  [[nodiscard]] HOLONICS_CALLABLE static constexpr checked_result<residue> reduced(
      unsigned_integer<Capacity> value,
      unsigned_integer<Capacity> modulus) noexcept {
    checked_result<residue> result{};
    result.receipt.admitted_limbs = static_cast<std::uint16_t>(Capacity);
    if (modulus.is_zero()) {
      result.receipt.state = status::invalid_modulus;
      return result;
    }
    const auto reduction = divide(value, modulus);
    result.value.value_ = reduction.remainder;
    result.value.modulus_ = modulus;
    result.receipt.required_limbs = static_cast<std::uint16_t>(modulus.used());
    return result;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr const unsigned_integer<Capacity>& value() const noexcept {
    return value_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const unsigned_integer<Capacity>& modulus() const noexcept {
    return modulus_;
  }

 private:
  unsigned_integer<Capacity> value_{};
  unsigned_integer<Capacity> modulus_{};
};

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr checked_result<residue<Capacity>> add(
    const residue<Capacity>& left,
    const residue<Capacity>& right) noexcept {
  checked_result<residue<Capacity>> result{};
  result.receipt.admitted_limbs = static_cast<std::uint16_t>(Capacity);
  if (left.modulus() != right.modulus()) {
    result.receipt.state = status::invalid_modulus;
    return result;
  }
  const auto sum = add(left.value(), right.value());
  if (!sum.accepted()) {
    result.receipt = sum.receipt;
    return result;
  }
  return residue<Capacity>::reduced(sum.value, left.modulus());
}

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr checked_result<residue<Capacity>> multiply(
    const residue<Capacity>& left,
    const residue<Capacity>& right) noexcept {
  checked_result<residue<Capacity>> result{};
  result.receipt.admitted_limbs = static_cast<std::uint16_t>(Capacity);
  if (left.modulus() != right.modulus()) {
    result.receipt.state = status::invalid_modulus;
    return result;
  }
  const auto product = multiply(left.value(), right.value());
  if (!product.accepted()) {
    result.receipt = product.receipt;
    return result;
  }
  return residue<Capacity>::reduced(product.value, left.modulus());
}

static_assert(exact_carrier<residue<6>>);

}  // namespace holonics::exact
