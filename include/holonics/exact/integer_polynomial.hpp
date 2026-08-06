#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/dyadic.hpp>

namespace holonics::exact {

/// A signed integer polynomial in ascending coefficient order. It is the
/// declared algebraic source of an enclosure: the hypothesis under which a
/// separation certificate and a later sign commitment are exact.
template<std::size_t Capacity>
struct integer_polynomial final {
  static_assert(Capacity > 0);

  std::int64_t coefficient[Capacity]{};
  std::size_t used{};
};

/// Product aperture for the homogeneous evaluation below.
inline constexpr std::int64_t polynomial_product_ceiling = std::int64_t{1} << 62;

namespace integer_polynomial_law {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool product_admitted(
    std::int64_t left,
    std::int64_t right) noexcept {
  return dyadic_law::product_fits(left, right);
}

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t height(
    const integer_polynomial<Capacity>& source) noexcept {
  std::int64_t largest = 0;
  for (std::size_t index = 0; index < source.used; ++index) {
    const std::int64_t candidate = dyadic_law::magnitude(source.coefficient[index]);
    if (candidate > largest) {
      largest = candidate;
    }
  }
  return largest;
}

/// Preflight the homogeneous evaluation of `source` at a dyadic whose numerator
/// magnitude is `numerator_magnitude` and whose denominator is `2^exponent`.
/// Returns false when the declared aperture cannot prove every product in range.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool evaluation_admitted(
    const integer_polynomial<Capacity>& source,
    std::int64_t numerator_magnitude,
    std::uint8_t exponent) noexcept {
  if (source.used == 0 || exponent > dyadic_exponent_ceiling) {
    return false;
  }
  const std::int64_t denominator = std::int64_t{1} << exponent;
  std::int64_t bound = numerator_magnitude > denominator ? numerator_magnitude : denominator;
  if (bound < 1) {
    bound = 1;
  }
  std::int64_t accumulated = height(source);
  if (accumulated == 0) {
    return true;
  }
  const std::size_t degree = source.used - 1;
  for (std::size_t step = 0; step < degree; ++step) {
    if (!product_admitted(accumulated, bound)) {
      return false;
    }
    accumulated *= bound;
  }
  const auto terms = static_cast<std::int64_t>(source.used);
  return product_admitted(accumulated, terms);
}

/// The exact sign of `source(value)`, computed by homogeneous Horner transport
/// over integers. No division, no rounding, and no floating carrier takes part:
/// the returned sign is the sign of an exactly formed integer.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr checked_result<std::int8_t> sign_at(
    const integer_polynomial<Capacity>& source,
    dyadic value) noexcept {
  checked_result<std::int8_t> result{};
  result.receipt.admitted_limbs = dyadic_exponent_ceiling;
  result.receipt.required_limbs = value.exponent;
  if (!dyadic_law::admitted(value) || source.used == 0 ||
      !evaluation_admitted(source, dyadic_law::magnitude(value.numerator), value.exponent)) {
    result.receipt.state = status::capacity_refused;
    return result;
  }
  const std::int64_t numerator = value.numerator;
  const std::int64_t denominator = std::int64_t{1} << value.exponent;
  const std::size_t degree = source.used - 1;
  std::int64_t accumulated = source.coefficient[degree];
  std::int64_t power = 1;
  for (std::size_t step = 0; step < degree; ++step) {
    const std::size_t index = degree - 1 - step;
    if (!product_admitted(power, denominator) ||
        !product_admitted(accumulated, numerator)) {
      result.receipt.state = status::capacity_refused;
      return result;
    }
    power *= denominator;
    if (!product_admitted(source.coefficient[index], power)) {
      result.receipt.state = status::capacity_refused;
      return result;
    }
    accumulated = accumulated * numerator + source.coefficient[index] * power;
    if (dyadic_law::magnitude(accumulated) > polynomial_product_ceiling) {
      result.receipt.state = status::capacity_refused;
      return result;
    }
  }
  if (accumulated > 0) {
    result.value = 1;
  } else if (accumulated < 0) {
    result.value = -1;
  }
  return result;
}

/// The index of the lowest nonzero coefficient. When it is positive, zero is a
/// root of the declared source with that multiplicity.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr std::size_t zero_multiplicity(
    const integer_polynomial<Capacity>& source) noexcept {
  for (std::size_t index = 0; index < source.used; ++index) {
    if (source.coefficient[index] != 0) {
      return index;
    }
  }
  return source.used;
}

/// Remove the exact factor `x^zero_multiplicity`. The returned source has a
/// nonzero constant coefficient whenever the original was not identically zero.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr integer_polynomial<Capacity> deflate_zero(
    const integer_polynomial<Capacity>& source) noexcept {
  integer_polynomial<Capacity> result{};
  const std::size_t shift = zero_multiplicity(source);
  if (shift >= source.used) {
    return result;
  }
  result.used = source.used - shift;
  for (std::size_t index = 0; index < result.used; ++index) {
    result.coefficient[index] = source.coefficient[index + shift];
  }
  return result;
}

}  // namespace integer_polynomial_law
}  // namespace holonics::exact
