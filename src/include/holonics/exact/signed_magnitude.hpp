#pragma once

#include <cstddef>

#include <holonics/exact/integer_division.hpp>

namespace holonics::exact {

template<std::size_t Capacity>
class signed_magnitude final {
 public:
  using holonics_exact_carrier = exact_carrier_marker;

  HOLONICS_CALLABLE constexpr signed_magnitude() noexcept
      : negative_{}, magnitude_{} {}
  HOLONICS_CALLABLE constexpr signed_magnitude(
      bool negative,
      unsigned_integer<Capacity> magnitude) noexcept
      : negative_(negative && !magnitude.is_zero()), magnitude_(magnitude) {}

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool negative() const noexcept { return negative_; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const unsigned_integer<Capacity>& magnitude() const noexcept {
    return magnitude_;
  }

  friend HOLONICS_CALLABLE constexpr bool operator==(
      const signed_magnitude& left,
      const signed_magnitude& right) noexcept {
    return left.negative_ == right.negative_ && left.magnitude_ == right.magnitude_;
  }

 private:
  bool negative_{};
  unsigned_integer<Capacity> magnitude_{};
};

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr checked_result<signed_magnitude<Capacity>> add(
    const signed_magnitude<Capacity>& left,
    const signed_magnitude<Capacity>& right) noexcept {
  checked_result<signed_magnitude<Capacity>> result{};
  result.receipt.admitted_limbs = static_cast<std::uint16_t>(Capacity);
  if (left.negative() == right.negative()) {
    const auto magnitude = add(left.magnitude(), right.magnitude());
    result.receipt = magnitude.receipt;
    if (magnitude.accepted()) {
      result.value = signed_magnitude<Capacity>{left.negative(), magnitude.value};
    }
    return result;
  }
  const int order = compare(left.magnitude(), right.magnitude());
  if (order == 0) {
    return result;
  }
  checked_result<unsigned_integer<Capacity>> magnitude{};
  if (order > 0) {
    magnitude = subtract(left.magnitude(), right.magnitude());
  } else {
    magnitude = subtract(right.magnitude(), left.magnitude());
  }
  result.receipt = magnitude.receipt;
  if (magnitude.accepted()) {
    result.value = signed_magnitude<Capacity>{
        order > 0 ? left.negative() : right.negative(), magnitude.value};
  }
  return result;
}

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr checked_result<signed_magnitude<Capacity>> multiply(
    const signed_magnitude<Capacity>& left,
    const signed_magnitude<Capacity>& right) noexcept {
  checked_result<signed_magnitude<Capacity>> result{};
  const auto magnitude = multiply(left.magnitude(), right.magnitude());
  result.receipt = magnitude.receipt;
  if (magnitude.accepted()) {
    result.value = signed_magnitude<Capacity>{
        left.negative() != right.negative(), magnitude.value};
  }
  return result;
}

static_assert(exact_carrier<signed_magnitude<6>>);

}  // namespace holonics::exact
